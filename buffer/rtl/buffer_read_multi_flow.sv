`timescale 1ns/1ps

// trying to add mutliple flows

module buffer_read_multi_flow #(
	 parameter SEGMENT_SIZE_W = 10 // size of a single segment
	,parameter BUF_SEG_AW = 10     // number of segments
	,parameter ADDR_WIDTH = BUF_SEG_AW + SEGMENT_SIZE_W
	,parameter FLOWS_W = 3 // number of flow is 2**FLOWS_W
	,parameter DWRR_BUFFER_W = FLOWS_W + 2 // put 4 entries per flow for a balanced weight distribution 
	,parameter VERSION_NUMBER = 32'h20251218
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
	,axi4lite_if.slave             csr

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
logic [2**FLOWS_W-1:0] init_done ;
logic [BUF_SEG_AW+SEGMENT_SIZE_W:0] usedw [2**FLOWS_W-1:0];


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
		pointers_orig #(
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
			,.init_done    (init_done[i])
			,.usedw        (usedw[i])
			,.full()
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
	if (s_rready == 1) begin // will have to do something more subtle than that, we can still look for new flows
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
					data_valid <= 1'b1;
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
	end		
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


// --------------------------------
//            CSR
// --------------------------------

// put a few things there:
// version register
// scratch register
// 1 info registers (top bit is OR)
// 1 warning registers (top bit is OR)
// 1 error registers (top bit is OR)
// then maybe the flow credits
// all info, warning and error will be W1C

// info[0]: init done on all pointers
// info[7]: OR of all info
 
//  logic [31:0] mem [0:2**(FLOWS_W)-1];   
  
  logic [31:0] version_reg = VERSION_NUMBER; // adr 0
  logic [31:0] scratch_reg; // adr 1 
  logic [31:0] info_reg;    // adr 2
  logic [31:0] warning_reg; // adr 3
  logic [31:0] error_reg;   // adr 4
//logic [2**FLOWS_W-1:0] init_done ; // will go to the info register
//logic [BUF_SEG_AW+SEGMENT_SIZE_W:0] usedw [2**FLOWS_W-1:0]; // adr 8+2**FLOW - 8+2*2**FLOW



  //always_ff @(posedge csr.ACLK ) begin
  always_ff @(posedge clk ) begin

      // Write
      if (csr.AWVALID && csr.WVALID && !csr.BVALID) begin
		case (csr.AWADDR[csr.ADDR_WIDTH-1:2])
			1 : scratch_reg <= csr.WDATA;
			2 : info_reg    <= csr.WDATA; // need to change that to W1C
			3 : warning_reg <= csr.WDATA; // need to change that to W1C
			4 : error_reg   <= csr.WDATA; // need to change that to W1C
		endcase
        csr.BVALID <= 1'b1;
      end else if (csr.BVALID && csr.BREADY) begin
        csr.BVALID <= 1'b0;
      end

      // Read
      if (csr.ARVALID && csr.ARREADY && !csr.RVALID) begin
        // unsure if/how I could use a case statement here
		if         (csr.ARADDR[csr.ADDR_WIDTH-1:2] == 0) begin
			csr.RDATA  <= version_reg;
		end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] == 1) begin
			csr.RDATA  <= scratch_reg;
		end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] == 2) begin
			csr.RDATA  <= info_reg;
		end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] == 3) begin
			csr.RDATA  <= warning_reg;
		end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] == 5) begin
			csr.RDATA  <= error_reg;
		end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] >= 8) begin
			csr.RDATA  <= usedw[csr.ARADDR[ADDR_WIDTH-1:2]-8];
		// end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] == 8) begin
			// csr.RDATA  <= usedw[0];
		// end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] == 9) begin
			// csr.RDATA  <= usedw[1];
		// end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] == 10) begin
			// csr.RDATA  <= usedw[2];
		// end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] == 11) begin
			// csr.RDATA  <= usedw[3];
		// end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] == 12) begin
			// csr.RDATA  <= usedw[4];
		// end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] == 13) begin
			// csr.RDATA  <= usedw[5];
		// end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] == 14) begin
			// csr.RDATA  <= usedw[6];
		// end else if(csr.ARADDR[csr.ADDR_WIDTH-1:2] == 15) begin
			// csr.RDATA  <= usedw[7];
        end else begin
			csr.RDATA  <= 32'hDEADDEAD;
		end
		csr.RVALID <= 1'b1;
      end else if (csr.RVALID && csr.RREADY) begin
        csr.RVALID <= 1'b0;
      end

    if (!rstn) begin
      csr.AWREADY <= 1'b1;
      csr.WREADY  <= 1'b1;
      csr.BVALID  <= 1'b0;
      csr.BRESP   <= 2'b00;
      csr.ARREADY <= 1'b1;
      csr.RVALID  <= 1'b0;
      csr.RRESP   <= 2'b00;
	  version_reg <= VERSION_NUMBER;
	  scratch_reg <= 32'hFFFFFFFF;
	  info_reg <= 32'h0;
	  warning_reg <= 32'h0;
	  error_reg <= 32'h0;
	  
	end
  end



assign b_raddr = {pointers_current[BUF_SEG_AW-1:0],location_counter};
assert property (@(posedge clk)
    pointers_rd_req == 1'b1 |-> ($past(pointers_rd_req,1) == 1'b0 && $past(pointers_rd_req,2) == 1'b0)
);
assert property (@(posedge clk) disable iff (!rstn)
    used_pointer_valid && $past(used_pointer_valid) |-> used_pointer != $past(used_pointer)
);
endmodule
