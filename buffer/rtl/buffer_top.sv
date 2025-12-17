// this is the top level unit of the buffer
// it will have AXI interfaces coming in and out
// it will instantiate the buffer and the various pointer 


module buffer_top #(
	 parameter DATA_WIDTH = 1024
	,parameter BUF_SEG_AW = 10 // this will represent the number of segments
	,parameter SEGMENT_SIZE_W = 8 // log2 of number of bytes
	,parameter FLOWS_W  = 3 // flow width
	,parameter SB_WIDTH = FLOWS_W // sideband information including flow number
) (
	// clock and reset
	 input logic 				clk // single clock domain for this module
	,input logic          		rstn // syncronous reset
	// write side
    ,input  logic [DATA_WIDTH-1:0] s_wdata   // Data from master
    ,input  logic                  s_wvalid  // Data valid
    ,output logic                  s_wready  // Ready to accept data
    ,input  logic                  s_wlast   // End of frame/packet 
    //,input  logic [(DATA_WIDTH/8)-1:0] s_wkeep // Byte qualifiers -- only bytes not used would be at the end of the packet
    ,input logic  [SB_WIDTH-1:0]   s_wsideband
	
	// read side
    ,output logic [DATA_WIDTH-1:0] s_rdata   // Data from master
    ,output logic                  s_rvalid  // Data valid
    ,input  logic                  s_rready  // Ready to accept data
    ,output logic                  s_rlast   // End of frame/packet 
    ,output logic [(DATA_WIDTH/8)-1:0] s_rkeep // Byte qualifiers -- only bytes not used would be at the end of the packet
		
	// control TBD
	
);


// First of all there will be a need to initialise the pointer list. This should be part of the pointer module
// then receive packets. For each new packet arriving, grab a free pointer.

// state machine for the receiving of data

// prefectch a pointer if there is one available
// always try to prefetch to enable faster turnaround -> may want to turn showahead on the FIFO, but this may have some timing implications
logic [BUF_SEG_AW-1:0] next_pointer; // this is the next free pointer
logic next_pointer_valid; // define if the pointer is valid or not
logic [BUF_SEG_AW-1:0] current_pointer; // this is the next free pointer
logic current_pointer_valid; // define if the pointer is valid or not
enum {idle, rcvd} rcvd_state;
logic [SEGMENT_SIZE_W-1:0] location_counter;

logic [DATA_WIDTH:0]     data_in;   // Data from master
logic                      valid_in;  // Data valid
//logic                      ready_out;  // Ready to accept data
logic                      last_in;   // End of frame/packet 
logic [(DATA_WIDTH/8)-1:0] keep_in; // Byte qualifiers -- only bytes not used would be at the end of the packet
logic [SB_WIDTH-1:0]       sideband_in;

logic rving_packet; 

// free pointers
logic [BUF_SEG_AW-1:0] pointers_rd_out; // pointer from the free pointers list
logic pointers_empty;
logic pointers_init_done;
logic pointers_wr_req;
logic [BUF_SEG_AW-1:0] pointers_wr_din;
logic pointers_rd_req;
logic pointers_rd_req_r;
logic pointers_empty_r;

// consumed pointers and release
logic [BUF_SEG_AW+SEGMENT_SIZE_W:0]  used_pointer; // top bit is for the last indication
logic                   used_pointer_valid;
//logic [BUF_SEG_AW-1:0]  freed_pointer;
//logic                   freed_pointer_valid;


// buffer
logic [BUF_SEG_AW+SEGMENT_SIZE_W-1:0] buffer_rd_addr;
logic [BUF_SEG_AW+SEGMENT_SIZE_W-1:0] buffer_wr_addr; // width is #segment + size of segment
logic [DATA_WIDTH:0] buffer_dout;

// skid buffer to match latency
logic [DATA_WIDTH-1:0] s_rdata_lat1;
logic                  s_rvalid_lat1;
logic                  s_rready_lat1;
logic                  s_rlast_lat1;



assign s_wready = (current_pointer_valid || (rcvd_state == rcvd) ) && pointers_init_done; // should allow traffic if we are currently in a packet or if we have space available. THis will probably be broken with the read latency of 0 -- to be checked

// need a current pointer and a next pointer that we fetch at least 2 cycles before the end of the packet


always_ff @(posedge clk) // will need to add something with the init done
begin
	pointers_rd_req <= 1'b0;
	if (pointers_init_done == 1'b1) begin
		if (next_pointer_valid == 1'b0 && pointers_rd_req == 1'b0 && pointers_rd_req_r == 1'b0) begin //fetch a new pointer as soon as possible - it takes 3 cycles a the start rather than 2
			pointers_rd_req <= 1'b1 & ~pointers_empty; // could try to fetch every 3 cycles, but may as well wait for the FIFO to have data. Possibly irrelevant, may be better to try to fetch
		end else if (pointers_rd_req_r == 1'b1) begin // ask for a pointer, getting it now
			next_pointer <= pointers_rd_out; // grab from the free pointer list
			next_pointer_valid <= ~pointers_empty_r; // may be one cycle too late for the empty
		end
		if (current_pointer_valid == 1'b0) begin // get a pointer if we don't have one
			if (next_pointer_valid == 1'b1) begin
				current_pointer_valid <= 1'b1;
				current_pointer <= next_pointer;
				next_pointer_valid <= 1'b0; // get ready to fetch the next pointer.
			end
		end
		// last cycle of the word/segment so try to get a new pointer
		if ((rcvd_state == rcvd) && s_wvalid && s_wlast) begin
			if (next_pointer_valid == 1'b1) begin
				current_pointer_valid <= 1'b1;
				current_pointer <= next_pointer;
				next_pointer_valid <= 1'b0; // get ready to fetch the next pointer.
			end else begin
				current_pointer_valid <= 1'b0;
			end
		end
		// if we reach out the last bit of the location_counter
		if ((rcvd_state == rcvd) && location_counter == {SEGMENT_SIZE_W{1'b1}}) begin // counter will wrap around
			// 2 cases, either we have a pointer available or we have not. For now let's assume we always have a pointer.
			if (next_pointer_valid == 1'b1) begin
				current_pointer_valid <= 1'b1;
				current_pointer <= next_pointer;
				next_pointer_valid <= 1'b0; // get ready to fetch the next pointer.
			end else begin
				current_pointer_valid <= 1'b0;
			end
		end
	end
	pointers_rd_req_r <= pointers_rd_req;
	pointers_empty_r <= pointers_empty;
    if (!rstn) begin 
        next_pointer_valid <= 1'b0;
		pointers_rd_req <= 1'b0;
		current_pointer_valid <= 1'b0;
		current_pointer <= {BUF_SEG_AW{1'b0}};
		pointers_rd_req_r <= 1'b0;
		pointers_empty_r <= 1'b1;
    end
 
end



// data coming in
always_ff @(posedge clk) // will need to add something with the init done
begin
	
	// when are we transitioning to rcvd: if we are idle, have a pointer and have valid Data
	// back to back packets will for now not being supported and we assume packets fit in a single container -- both will need to change
	used_pointer_valid <= 1'b0;
	
	if  (current_pointer_valid == 1'b1 && (rcvd_state == idle) ) begin
		rcvd_state <= rcvd;
		if (s_wvalid == 1'b1) begin
			location_counter <= location_counter + 1'b1;
		end
	end
	if (rcvd_state == rcvd && s_wvalid == 1'b1) begin // will need to add a next segment part
		location_counter <= location_counter + 1'b1;
	end
	if ((rcvd_state == rcvd) && s_wvalid && s_wlast) begin // this clearly will not do back to back, will also fail for packets using multiple segments
		rcvd_state <= idle;
		location_counter <= {SEGMENT_SIZE_W{1'b0}}; 
		valid_in <= 1'b0;
		// consume the pointer
		used_pointer_valid <= 1'b1;
		used_pointer <= {s_wlast,location_counter,current_pointer};
	end
	if ((rcvd_state == rcvd) && location_counter == {SEGMENT_SIZE_W{1'b1}}) begin // counter will wrap around -- end of segment
		if (next_pointer_valid == 1'b1) begin // we have another pointer available
			rcvd_state <= rcvd;
		end else begin // no pointer available, need to backpressure.
			rcvd_state <= idle;
		end
		used_pointer_valid <= 1'b1;
		used_pointer <= {s_wlast,location_counter,current_pointer};
	end
	
	buffer_wr_addr <= {current_pointer,location_counter};
	if (rcvd_state == rcvd || (current_pointer_valid == 1'b1 && rcvd_state == idle && s_wvalid == 1'b1)) begin // missing the first transfer
	    data_in <= {s_wlast,s_wdata};
	    valid_in <= s_wvalid;
	    last_in <= s_wlast;
	    sideband_in <= s_wsideband;
	end else begin
	    data_in <= {(DATA_WIDTH+1){1'bx}}; // this is temporary to have a clearer view in the waveform
	    valid_in <= 1'b0;
	    last_in <= 1'b0;
	    sideband_in <= {SB_WIDTH{1'bx}}; // this is temporary to have a clearer view in the waveform
	end
 
 if (!rstn) begin 
	    rving_packet <= 1'b0;
		rcvd_state <= idle;
		location_counter <= {SEGMENT_SIZE_W{1'b0}};
		buffer_wr_addr <= {(BUF_SEG_AW+SEGMENT_SIZE_W){1'b0}};
	    data_in <= {(DATA_WIDTH+1){1'bx}};
	    valid_in <= 1'b0;
	    last_in <= 1'b0;
	    sideband_in <= {SB_WIDTH{1'bx}};
		used_pointer <= {(BUF_SEG_AW+SEGMENT_SIZE_W+1){1'b0}};
		used_pointer_valid <= 1'b0;

    end

end


// free pointer list
pointers #(
	 .DATA_WIDTH (BUF_SEG_AW)
	,.INITIALISE_POINTERS("YES")
) free_pointers (
     .clk          (clk)
    ,.rstn         (rstn)
    ,.wr_req       (pointers_wr_req)  // Write enable
    ,.wr_din       (pointers_wr_din)  // Write data
    ,.rd_req       (pointers_rd_req)  // Read request
    ,.rd_dout      (pointers_rd_out)  // Read data
    ,.fifo_empty   (pointers_empty)
    ,.init_done    (pointers_init_done)
);

// buffer module
buffer_elem #(
     .DATA_WIDTH (DATA_WIDTH+1)
    ,.ADDR_WIDTH (BUF_SEG_AW+SEGMENT_SIZE_W) 
) buffer (
     .clk        (clk)
    ,.we         (valid_in)// Write enable
    ,.wr_addr    (buffer_wr_addr)// Write address -- pointer + cycle in the packet
    ,.din        (data_in)// Write data
    ,.rd_addr    (buffer_rd_addr)// Read address
    ,.dout       (buffer_dout)// Read data
);



buffer_read_multi_flow #(
	 .SEGMENT_SIZE_W (SEGMENT_SIZE_W)
	,.BUF_SEG_AW     (BUF_SEG_AW)
	,.FLOWS_W        (FLOWS_W)
	) buffer_read ( 
	 .clk                  (clk)
	,.rstn                 (rstn)
	,.used_pointer         (used_pointer)
	,.used_pointer_valid   (used_pointer_valid)
	,.used_pointer_flow    (sideband_in)
						  
	,.s_rready             (s_rready_lat1)    // t_ready coming from the read side (next element down the chain)
	,.s_rvalid             (s_rvalid_lat1)    // so that we know when an item is consumed
	,.s_rlast              (buffer_dout[DATA_WIDTH])   // last element of the packet
						  
	,.freed_pointer        (pointers_wr_din)
	,.freed_pointer_valid  (pointers_wr_req)
						  
	,.p_tready             ()  // probably not needed, we are managing the read from here, was thinking of sending this to the buffer itself, but it makes no sense
	,.b_raddr              (buffer_rd_addr)
	
);

rd_latency1_to_0 #(
   .WIDTH (DATA_WIDTH+2)
) skid_buffer (
 .clk         (clk) 
,.rst_n       (rstn)

,.in_rd_en    (s_rready_lat1)
//,.in_rd_valid (s_rvalid_lat1)
,.in_rd_data  ({s_rvalid_lat1,s_rlast_lat1,s_rdata_lat1})

,.out_rd_en   (s_rready)
//,.out_rd_valid(s_rvalid)
,.out_rd_data ({s_rvalid,s_rlast,s_rdata})
);



// reading side, will create a small module to find the right data, as this will evolve depending on complexity
// we need to give the used pointers and the value of the flow.
// the block will then read from the buffer when the tready is asserted (possibly start by dumping the data)


assign s_rdata_lat1 = buffer_dout[DATA_WIDTH-1:0];
assign s_rlast_lat1 = buffer_dout[DATA_WIDTH];
assign s_rkeep = {(DATA_WIDTH/8){1'b0}};

endmodule
