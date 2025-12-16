`timescale 1ns/1ps

// trying to add mutliple flows

module buffer_read_multi_flow #(
	 parameter SEGMENT_SIZE_W = 10 // size of a single segment
	,parameter BUF_SEG_AW = 10     // number of segments
	,parameter ADDR_WIDTH = BUF_SEG_AW + SEGMENT_SIZE_W
	,parameter FLOWS_W = 3 // number of flow is 2**FLOWS_W
	,parameter DWRR_BUFFER_W = FLOWS_W + 2 // put 4 entries per flow for a balanced weight distribution 
	)(
	 input logic                   clk
	,input logic                   rstn
	,input logic [BUF_SEG_AW+SEGMENT_SIZE_W:0]    used_pointer // top bit indicate the tlast
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
logic [BUF_SEG_AW+SEGMENT_SIZE_W:0] pointers_rd_out [2**FLOWS_W-1:0];
logic [BUF_SEG_AW+SEGMENT_SIZE_W:0] pointers_current;
logic pointer_valid;
logic pointers_emtpy [2**FLOWS_W-1:0];
logic pointers_rd_req_r;

// counter to see when we arrive to the end of the segment
logic [SEGMENT_SIZE_W-1:0] location_counter;
logic [SEGMENT_SIZE_W-1:0] location_counter_r;

enum {idle_no_sel, idle_with_sel,idle_with_sel2, idle_no_data_no_sel, idle_no_data_with_sel, rcvd_no_sel, rcvd_with_sel} rcvd_state;

// --- DWRR declaration section -------
logic [MAX_CREDIT_W-1:0] flow_credits [2**FLOWS_W-1:0]; // credits for each flow
logic [FLOWS_W-1:0] current_selected_flow;
logic [FLOWS_W-1:0] next_selected_flow;
logic [FLOWS_W-1:0] next_selected_flow_r;
logic [FLOWS_W-1:0] next_selected_flow_r2;
logic              current_flow_valid;
logic              next_flow_valid;
logic              dwrr_init_done;
logic              dwrr_next_credit_req;
logic [FLOWS_W-1:0] dwrr_next_credit_value;
logic [FLOWS_W-1:0] rr_counter;


logic data_valid;
// ---------------------------------
genvar i;
generate
    for (i = 0; i < 2**FLOWS_W; i++) begin : GEN_USED_POINTERS
		pointers #(
			 .DATA_WIDTH (BUF_SEG_AW+SEGMENT_SIZE_W+1)
			,.INITIALISE_POINTERS("NO")
		) used_pointers (
			 .clk          (clk)
			,.rstn         (rstn)
			,.wr_req       (used_pointer_valid && (used_pointer_flow == i))  // Write enable
			,.wr_din       (used_pointer)  // Write data
			,.rd_req       (pointers_rd_req[i])  // Read request
			,.rd_dout      (pointers_rd_out[i])  // Read data
			,.fifo_empty   (pointers_emtpy[i])
			,.init_done    ()
		);
    end
endgenerate

dwrr_credits #(
     .DEPTH_W (5) // the 2 parameters are related and should only be one
	,.FLOW_W (FLOWS_W) // must be lower than DEPTH_W
)dww_credits (
     .clk                   (clk)
    ,.rstn                  (rstn)
    ,.rd_req                (dwrr_next_credit_req)   // Read request
    ,.rd_out                (dwrr_next_credit_value)   // Read data
    ,.init_done             (dwrr_init_done)

);

// logic [2**FLOWS_W-1:0] pointers_rd_req ;
// logic [BUF_SEG_AW-1:0] pointers_rd_out [2**FLOWS_W-1:0];
// logic [BUF_SEG_AW-1:0] pointers_current;


always_ff @(posedge clk) begin
	pointers_rd_req <= {(2**FLOWS_W){1'b0}};
	freed_pointer_valid <= 1'b0;
	if (rcvd_state == idle_no_sel) begin //situation where we have not received traffic yet -- check if the current RR counter has data or not, if not move to the next
		if (pointers_emtpy[rr_counter] == 1'b0 && flow_credits[rr_counter] != 0) begin // this is our next selection
			next_selected_flow <= rr_counter;
			pointers_rd_req[rr_counter]<= 1'b1;
			next_flow_valid <= 1'b1;
			// consume a credit now?
			rcvd_state <= idle_with_sel;
		end
		rr_counter <= rr_counter + 1'b1;
		data_valid <= 1'b0;
	end
	if (rcvd_state == idle_with_sel) begin // as we have a selection, we can move to get the data (probably could have done that quicker in the idle_no_sel
		current_selected_flow <= next_selected_flow;
		current_flow_valid <= 1'b1;
		next_flow_valid <= 1'b0;
		next_selected_flow <= {FLOWS_W{1'bx}};
		rcvd_state <= idle_with_sel2;
		location_counter <= {SEGMENT_SIZE_W{1'b0}};
	end

	if (rcvd_state == idle_with_sel2) begin // as we have a selection, we can move to get the data (probably could have done that quicker in the idle_no_sel
		rcvd_state <= rcvd_no_sel;
		data_valid <= 1'b1;
		pointers_current <= pointers_rd_out[current_selected_flow];
	end
	
	if (rcvd_state == rcvd_no_sel) begin // receive until end of segment or end of packet -- need to select the next segment. Either the same flow if not end of packet or new flow
		data_valid <= 1'b1;
		// if (location_counter[1:0] == 2'b10 && pointers_current[BUF_SEG_AW] == 1'b0) begin // not the last segment of the packet and so pre-fetch the next pointer
			// pointers_rd_req[current_selected_flow]<= 1'b1;
		// end
		// if (pointers_current[BUF_SEG_AW+SEGMENT_SIZE_W-1:BUF_SEG_AW] == location_counter) begin // last word of the packet 
			// location_counter <= {SEGMENT_SIZE_W{1'b0}};
			// rcvd_state <= idle_no_sel;
			// data_valid <= 1'b0;
		// end else 
		if (pointers_current[BUF_SEG_AW+SEGMENT_SIZE_W-1:BUF_SEG_AW] == location_counter && pointers_current[BUF_SEG_AW+SEGMENT_SIZE_W] == 1'b1) begin // this is the last cycle for this packet
			location_counter <= {SEGMENT_SIZE_W{1'b0}};
			rcvd_state <= idle_no_sel;
			data_valid <= 1'b0;
			freed_pointer <= pointers_current[BUF_SEG_AW-1:0];
			freed_pointer_valid <= 1'b1;
		end else if (pointers_current[BUF_SEG_AW+SEGMENT_SIZE_W-1:BUF_SEG_AW] == location_counter  && pointers_current[BUF_SEG_AW+SEGMENT_SIZE_W] == 1'b0) begin // end of segment, more to come
			// stay on the same flow
			if (pointers_emtpy[current_selected_flow] == 1'b1) begin // temporarily ran out of data
				rcvd_state <= idle_no_data_no_sel;
				data_valid <= 1'b0;
			end else begin
				//pointers_current <= pointers_rd_out[current_selected_flow];
				rcvd_state <= idle_with_sel;
				data_valid <= 1'b0;
				pointers_rd_req[current_selected_flow]<= 1'b1;
				next_selected_flow <= current_selected_flow;
			end
			location_counter <= {SEGMENT_SIZE_W{1'b0}}; // counter goes back to 0 in both cases
			freed_pointer <= pointers_current[BUF_SEG_AW-1:0];
			freed_pointer_valid <= 1'b1;
		end else begin // mid segment
			if (pointers_emtpy[rr_counter] == 1'b0 && flow_credits[rr_counter] != 0 && pointers_current[BUF_SEG_AW+SEGMENT_SIZE_W] == 1'b1) begin // this is our next selection -- only change if we are on the last segment of the packet
				next_selected_flow <= rr_counter;
				next_flow_valid <= 1'b1;
				pointers_rd_req[rr_counter]<= 1'b1;
				// consume a credit now?
				rcvd_state <= rcvd_with_sel;
				rr_counter <= rr_counter + 1'b1;
				data_valid <= 1'b0;
			end else begin
			end
			location_counter <= location_counter + 1'b1;
		end
	end
	
	if (rcvd_state == rcvd_with_sel) begin // receive until end of segment or end of packet
		data_valid <= 1'b1;
		if (pointers_current[BUF_SEG_AW+SEGMENT_SIZE_W-1:BUF_SEG_AW] == location_counter  && pointers_current[BUF_SEG_AW+SEGMENT_SIZE_W] == 1'b1) begin // this is the last, we just don't know it yet
			location_counter <= {SEGMENT_SIZE_W{1'b0}};
			rcvd_state <= idle_with_sel;
			data_valid <= 1'b0;
			pointers_current <= pointers_rd_out[next_selected_flow];
			freed_pointer <= pointers_current[BUF_SEG_AW-1:0];
			freed_pointer_valid <= 1'b1;
		end else if (pointers_current[BUF_SEG_AW+SEGMENT_SIZE_W-1:BUF_SEG_AW] == location_counter  && pointers_current[BUF_SEG_AW+SEGMENT_SIZE_W] == 1'b0) begin // end of segment
			// stay on the same flow
			if (pointers_emtpy[current_selected_flow] == 1'b1) begin // temporarily ran out of data
				rcvd_state <= idle_no_data_with_sel;
				data_valid <= 1'b0;
			end else begin
				rcvd_state <= rcvd_no_sel;
				next_flow_valid <= 1'b0;
				data_valid <= 1'b0;
			end
			freed_pointer <= pointers_current[BUF_SEG_AW-1:0];
			freed_pointer_valid <= 1'b1;
		end else begin // mid segment
			location_counter <= location_counter + 1'b1;
		end
	end
	
	if (rcvd_state == idle_no_data_no_sel) begin // wait for the buffer to continue storing the current packet (this state should probably not occur)
		if (pointers_emtpy[current_selected_flow] == 1'b0) begin //resume
			rcvd_state <= rcvd_no_sel;
			data_valid <= 1'b1;
		end
	end
	
	if (rcvd_state == idle_no_data_with_sel) begin // wait for the buffer to continue storing the current packet (this state should probably not occur)
		if (pointers_emtpy[current_selected_flow] == 1'b0) begin //resume
			rcvd_state <= rcvd_with_sel;
			data_valid <= 1'b1;
		end
	end
	s_rvalid <= data_valid;
	
	if (rstn == 1'b0) begin
		rcvd_state <= idle_no_sel;
		rr_counter <= {FLOWS_W{1'b0}};
		next_flow_valid <= 1'b0;
		next_selected_flow <= {FLOWS_W{1'bx}}; // resetting to x for easier debug in simulation
		current_flow_valid <= 1'b0;
		current_selected_flow <= {FLOWS_W{1'bx}};
		location_counter <= {SEGMENT_SIZE_W{1'b0}};
		data_valid <= 1'b0;
		s_rvalid <= 1'b0;
		freed_pointer_valid <= 1'b0;
		pointers_current <= {(BUF_SEG_AW+SEGMENT_SIZE_W+1){1'b1}};
		for (int j = 0; j < 2**FLOWS_W; j++) begin
			flow_credits[j] <= {1'b0,{(MAX_CREDIT_W-1){1'b1}}};
		end

	end
end








// // read when we can and increment when tready is high
// // will need prefetching the next segment
// always_ff @(posedge clk) begin
	// pointers_rd_req <= {(2**FLOWS_W){1'b0}};
	// freed_pointer_valid <= 1'b0;
	// s_rvalid <= 1'b0;
	// // we are not active at the moment, need a first pointer -- take the decision from the DWRR to select the right pointer list
	// if (pointers_rd_req[current_selected_flow] == 1'b0 && pointers_rd_req_r == 1'b0 /*&& pointers_emtpy[current_selected_flow] == 1'b0 implicit */ && current_flow_valid == 1'b1 && rcvd_state == idle) begin // latency of 1 to get the data  -- this does not work as we try to fetch whilst we are already sending. Need a state as well
		// pointers_rd_req[current_selected_flow] <= 1'b1;
		// location_counter <= {SEGMENT_SIZE_W{1'b0}};
		// rcvd_state <= rcvd;
	// end
	// // this is the end of the current packet, need to get new one -- take the decision from the DWRR to select the right pointer list
	// if (s_rlast == 1'b1) begin // last item in the segment and end of packet -- This is where we should make a decision on which flow to use
		// if (next_flow_valid == 1'b1) begin
			// if (pointers_rd_req[next_selected_flow] == 1'b0 && pointers_rd_req_r == 1'b0) begin
				// pointers_rd_req[next_selected_flow] <= 1'b1;
			// end
			// location_counter <= {SEGMENT_SIZE_W{1'b0}};
		// end else begin
			// rcvd_state <= idle;
		// end
		// // corner case when the whole segment is used and we just freed the pointer on the previous clock cycle due to the location counter saturating
		// if (location_counter_r != {SEGMENT_SIZE_W{1'b1}}) begin
			// freed_pointer_valid <= 1'b1;
		// end
	// end
	// // this is the end of a segment but not the last segment in the packet, keep selecting from the same pointer list
	// if (location_counter == {SEGMENT_SIZE_W{1'b1}} && s_rlast == 1'b0) begin // last item in the segment and end of packet
		// if (next_flow_valid == 1'b1) begin
			// if (pointers_rd_req[next_selected_flow] == 1'b0 && pointers_rd_req_r == 1'b0) begin
				// pointers_rd_req[next_selected_flow] <= 1'b1;
			// end
			// location_counter <= {SEGMENT_SIZE_W{1'b0}};
		// end
		// freed_pointer_valid <= 1'b1;
	// end
	// // will need to take from the current pointer list to 
	// if (pointers_rd_req_r == 1'b1) begin // this works only because we get a new pointer when we know we have one (otherwise would need to check the empty
		// freed_pointer <= pointers_rd_out[current_selected_flow][BUF_SEG_AW-1:0]; // are we releasing this too early? probably should wait for the last of the packet or segment to release otherwise could be used whilst we are draining. 
		// // freed_pointer <= pointers_rd_out[BUF_SEG_AW-1:0][current_selected_flow]; // are we releasing this too early? probably should wait for the last of the packet or segment to release otherwise could be used whilst we are draining. 
	// end
	// if (current_flow_valid == 1'b1 && s_rready == 1'b1 && s_rlast == 1'b0) begin
		// location_counter <= location_counter + 1'b1;
		// s_rvalid <= 1'b1;
	// end
	// pointers_rd_req_r <= |pointers_rd_req; // any read request would trigger
	// location_counter_r <= location_counter;
	
	// //if (pointers_rd_req_r == 1'b1) begin // this works only because we get a new pointer when we know we have one (otherwise would need to check the empty
		// // need to update this when we are at the end of a segment
		// pointers_current <= pointers_rd_out[current_selected_flow];
	// //end
	
	// if (rstn == 1'b0) begin
		// pointers_rd_req <= {(2**FLOWS_W){1'b0}};
		// pointer_valid <= 1'b0;
		// pointers_current <= {(BUF_SEG_AW){1'b0}};
		// location_counter <= {SEGMENT_SIZE_W{1'b0}};
		// location_counter_r <= {SEGMENT_SIZE_W{1'b0}};
		// freed_pointer <= {BUF_SEG_AW{1'b0}};
		// freed_pointer_valid <= 1'b0;
		// s_rvalid <= 1'b0;
		// rcvd_state <= idle;
	// end
// end

// // -------- DWRR section --------------

// // logic [MAX_CREDIT_W-1:0] flow_credits [2**FLOWS_W-1:0]; // credits for each flow
// // logic [FLOWS_W-1:0] current_selected_flow;
// // logic [FLOWS_W-1:0] next_selected_flow;
// // logic              current_flow_valid;
// // logic              next_flow_valid;
// // logic              dwrr_init_done;
// // logic              dwrr_next_credit_req;
// // logic [FLOWS_W-1:0] dwrr_next_credit_value;
// // logic [FLOWS_W-1:0] rr_counter;

// //DWRR_BUFFER_W
// //reuse the pointer buffer as a mea
// always_ff @(posedge clk)
// begin

	// // select the next flow
	// if (next_flow_valid == 1'b0) begin
		// if (pointers_emtpy[rr_counter] == 1'b0 && flow_credits[rr_counter] != {2**FLOWS_W{1'b0}}) begin // there are credits -- will need to do a prefetch on this the credits otherwise this is too slow -- assume prefectch is on for now
			// // this could reselect the same flow after going full cicle if no other flow is selected
			// next_flow_valid <= 1'b1;
			// next_selected_flow <= rr_counter;
		// end 
		// rr_counter <= rr_counter + 1'b1; // go to the next address. Go if the one we are looking at is empty, but also go if we select it as we want to start from the next flow on the next try
	// end
	// // move to current flow and spend a credit
	// if (current_flow_valid == 1'b1) begin 
		// if (next_flow_valid == 1'b1 && s_rlast == 1'b1) begin // end of a packet, go to the next flow. 
			// current_selected_flow <= next_selected_flow;
			// current_flow_valid <= next_flow_valid;
			// flow_credits[next_selected_flow] <= flow_credits[next_selected_flow] - 1'b1;
			// if (pointers_emtpy[rr_counter] == 1'b0 && flow_credits[rr_counter] != {2**FLOWS_W{1'b0}}) begin
				// next_flow_valid <= 1'b1; 
				// next_selected_flow <= rr_counter;
			// end else begin
				// next_flow_valid <= 1'b0;
			// end
		// end else if (s_rlast == 1'b1) begin
			// current_flow_valid <= 1'b0; 
		// end
	// end else begin
		// if (next_flow_valid == 1'b1 /* && current_flow_valid == 1'b0 -- implicit */) begin // end of a packet, go to the next flow. 
			// current_selected_flow <= next_selected_flow;
			// current_flow_valid <= next_flow_valid;
			// flow_credits[next_selected_flow] <= flow_credits[next_selected_flow] - 1'b1;
			// if (pointers_emtpy[rr_counter] == 1'b0 && flow_credits[rr_counter] != {2**FLOWS_W{1'b0}}) begin
				// next_flow_valid <= 1'b1; 
				// next_selected_flow <= rr_counter;
			// end else begin
				// next_flow_valid <= 1'b0;
			// end
		// end
	// end
	

	// // give credits
	// if (s_rlast == 1'b1) begin
		// if (next_flow_valid == 1'b1 && current_selected_flow != next_selected_flow) begin
			// flow_credits[dwrr_next_credit_value] <= flow_credits[dwrr_next_credit_value] + 1'b1; // will need to check we are not consuming at the same time, in which case no changes
		// end
		// dwrr_next_credit_req <= 1'b1; // get ready to credit the next port
	// end else begin
		// dwrr_next_credit_req <= 1'b0;
	// end
	// // give this based on a counter ? (may want to do that also when a new pointer is selcted.
	// next_selected_flow_r <= next_selected_flow;
	// next_selected_flow_r2 <= next_selected_flow_r;
	

	// if (rstn == 1'b0) begin
		// current_flow_valid <= 1'b0;
		// next_flow_valid <= 1'b0;
		// rr_counter <= {FLOWS_W{1'b0}};
		// for (int j = 0; j < 2**FLOWS_W; j++) begin
			// flow_credits[j] <= {1'b0,{(MAX_CREDIT_W-1){1'b1}}};
		// end
	// end
// end 

assign b_raddr = {pointers_current[BUF_SEG_AW-1:0],location_counter};
assert property (@(posedge clk)
    pointers_rd_req == 1'b1 |-> ($past(pointers_rd_req,1) == 1'b0 && $past(pointers_rd_req,2) == 1'b0)
);
assert property (@(posedge clk) disable iff (!rstn)
    used_pointer_valid && $past(used_pointer_valid) |-> used_pointer != $past(used_pointer)
);
endmodule
