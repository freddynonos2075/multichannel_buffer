`timescale 1ns/1ps

// trying to add mutliple flows

module buffer_read #(
	 parameter SEGMENT_SIZE_W = 10 // size of a single segment
	,parameter BUF_SEG_AW = 10     // number of segments
	,parameter ADDR_WIDTH = BUF_SEG_AW + SEGMENT_SIZE_W
	,parameter FLOWS_W = 3 // number of flow is 2**FLOWS_W
	,parameter DWRR_BUFFER_W = FLOWS_W + 2; // put 4 entries per flow for a balanced weight distribution 
	)(
	 input logic                   clk
	,input logic                   rstn
	,input logic [BUF_SEG_AW:0]    used_pointer // top bit indicate the tlast
	,input logic                   used_pointer_valid
	,input logic [FLOWS_W-1:0]     used_pointer_flow
					               
	,input logic                   s_rready // t_ready coming from the read side (next element down the chain)
	,output logic                  s_rvalid // so that we know when an item is consumed
	,input logic                   s_rlast // last element of the packet
	
	,output logic [BUF_SEG_AW-1:0] freed_pointer
	,output logic                  freed_pointer_valid
	
	,output logic                  p_tready // probably not needed, we are managing the read from here, was thinking of sending this to the buffer itself, but it makes no sense
	,output logic [ADDR_WIDTH-1:0] b_raddr
	
	// will need a AXI interface for control of the weights
	
);

localparam MAX_CREDIT_W = 6; // 2**MAX_CREDIT_W is the max number of credits
// used pointer module
// will need something based on tready, but the read latency of 0 will be a challenge
// for now we will generate one pointer list per flow -- assume only 1 flow just yet

logic [2**FLOWS_W-1:0] pointers_rd_req ;
logic [BUF_SEG_AW:0] pointers_rd_out [2**FLOWS_W-1:0];
logic [BUF_SEG_AW:0] pointers_current;
logic pointer_valid;
logic [2**FLOWS_W-1:0] pointers_emtpy;
logic pointers_rd_req_r;

// counter to see when we arrive to the end of the segment
logic [SEGMENT_SIZE_W-1:0] location_counter;
logic [SEGMENT_SIZE_W-1:0] location_counter_r;

genvar i;
generate
    for (i = 0; i < 2**FLOWS_W; i++) begin : GEN_USED_POINTERS
		pointers #(
			 .DATA_WIDTH (BUF_SEG_AW+1)
			,.INITIALISE_POINTERS("NO")
		) used_pointers (
			 .clk          (clk)
			,.rstn         (rstn)
			,.wr_req       (used_pointer_valid && (used_pointer_flow == i))  // Write enable
			,.wr_din       (used_pointer)  // Write data
			,.rd_req       (pointers_rd_req[i])  // Read request
			,.rd_dout      (pointers_rd_out[i])  // Read data
			,.fifo_empty   (pointers_empty[i])
			,.init_done    ()
		);
    end
endgenerate

dwrr_credits #(
     .DEPTH_W (5) // the 2 parameters are related and should only be one
	,.FLOW_W (FLOWS_W) // must be lower than DEPTH_W
)dww_credits (
     .clk         (clk)
    ,.rstn        (rstn)
    ,.rd_req      (dwrr_next_credit_req)   // Read request
    ,.rd_dout     (dwrr_next_credit_value)   // Read data
    ,.init_done   (dwrr_init_done)

);


// read when we can and increment when tready is high
// will need prefetching the next segment
always_ff @(posedge clk) begin
	pointers_rd_req <= {(2**FLOWS_W){1'b0}};
	freed_pointer_valid <= 1'b0;
	s_rvalid <= 1'b0;
	// we are not active at the moment, need a first pointer -- take the decision from the DWRR to select the right pointer list
	if (pointer_valid == 1'b0 && pointers_rd_req == 1'b0 && pointers_rd_req_r == 1'b0 && pointers_empty == 1'b0) begin // latency of 1 to get the data 
		pointers_rd_req <= 1'b1;
		location_counter <= {SEGMENT_SIZE_W{1'b0}};
	end
	// this is the end of the current packet, need to get new one -- take the decision from the DWRR to select the right pointer list
	if (s_rlast == 1'b1) begin // last item in the segment and end of packet -- This is where we should make a decision on which flow to use
		if (pointers_empty == 1'b0) begin
			if (pointers_rd_req == 1'b0 && pointers_rd_req_r == 1'b0) begin
				pointers_rd_req <= 1'b1;
			end
			location_counter <= {SEGMENT_SIZE_W{1'b0}};
		end
		pointer_valid <= 1'b0; // loosing a clock cycle or 2 there
		// corner case when the whole segment is used and we just freed the pointer on the previous clock cycle due to the location counter saturating
		if (location_counter_r != {SEGMENT_SIZE_W{1'b1}}) begin
			freed_pointer_valid <= 1'b1;
		end
	end
	// this is the end of a segment but not the last segment in the packet, keep selecting from the same pointer list
	if (location_counter == {SEGMENT_SIZE_W{1'b1}} && s_rlast == 1'b0) begin // last item in the segment and end of packet
		if (pointers_empty == 1'b0) begin
			if (pointers_rd_req == 1'b0 && pointers_rd_req_r == 1'b0) begin
				pointers_rd_req <= 1'b1;
			end
			location_counter <= {SEGMENT_SIZE_W{1'b0}};
		end
		pointer_valid <= 1'b0; // loosing a clock cycle or 2 there
		freed_pointer_valid <= 1'b1;
	end
	// will need to take from the current pointer list to 
	if (pointers_rd_req_r == 1'b1) begin // this works only because we get a new pointer when we know we have one (otherwise would need to check the empty
		pointers_current <= pointers_rd_out;
		freed_pointer <= pointers_rd_out[BUF_SEG_AW-1:0]; // are we releasing this too early? probably should wait for the last of the packet or segment to release otherwise could be used whilst we are draining. 
		pointer_valid <= 1'b1;
	end
	if (pointer_valid == 1'b1 && s_rready == 1'b1 && s_rlast == 1'b0) begin
		location_counter <= location_counter + 1'b1;
		s_rvalid <= 1'b1;
	end
	pointers_rd_req_r <= pointers_rd_req;
	location_counter_r <= location_counter;
	
	if (rstn == 1'b0) begin
		pointers_rd_req <= {(2**FLOWS_W){1'b0}};
		pointer_valid <= 1'b0;
		pointers_current <= {(BUF_SEG_AW+1){1'b0}};
		location_counter <= {SEGMENT_SIZE_W{1'b0}};
		location_counter_r <= {SEGMENT_SIZE_W{1'b0}};
		freed_pointer <= {BUF_SEG_AW{1'b0}};
		freed_pointer_valid <= 1'b0;
		s_rvalid <= 1'b0;
	end
end

// -------- DWRR section --------------

logic [MAX_CREDIT_W-1:0] flow_credits [2**FLOWS_W-1:0]; // credits for each flow
logic [FLOW_W-1:0] current_selected_flow;
logic [FLOW_W-1:0] next_selected_flow;
logic              current_flow_valid;
logic              next_flow_valid;
logic              dwrr_init_done;
logic              dwrr_next_credit_req;
logic [FLOW_W-1:0] dwrr_next_credit_value;
logic [FLOW_W-1:0] rr_counter;
//DWRR_BUFFER_W
//reuse the pointer buffer as a mea
always_ff @(posedge clk)
begin
	// select the next flow
	if (next_flow_valid == 1'b0) begin
		if () begin // there are credits -- will need to do a prefetch on this the credits otherwise this is too slow -- assume prefectch is on for now
			
		end
	end
	// move to current flow
	
	// spend credits (done at move to current flow
	
	// give credits
	// give this based on a counter ? (may want to do that also when a new pointer is selcted.
	
	

	if (rstn == 1'b0) begin
		current_flow_valid <= 1'b0;
		next_flow_valid <= 1'b0;
		rr_counter <= {FLOW_W{1'b0}};
	end
end 

assign b_raddr = {pointers_current,location_counter};
assert property (@(posedge clk)
    pointers_rd_req == 1'b1 |-> ($past(pointers_rd_req,1) == 1'b0 && $past(pointers_rd_req,2) == 1'b0)
);
assert property (@(posedge clk) disable iff (!rstn)
    used_pointer_valid && $past(used_pointer_valid) |-> used_pointer != $past(used_pointer)
);
endmodule
