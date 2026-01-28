// we will use this to store pointers.
// this may be free pointers as well as the pointers per queue
// just a memory at the base
// need to move this to a SC fifo

module pointers #(
     parameter DATA_WIDTH = 10 // the 2 parameters are related and should only be one
	,parameter string INITIALISE_POINTERS = "YES"
	,parameter FIFO_DEPTH = 2**DATA_WIDTH
)(
     input  logic                     clk
    ,input  logic                     rstn
    ,input  logic                     wr_req         // Write enable
    ,input  logic [DATA_WIDTH-1:0]    wr_din         // Write data
    ,input  logic                     rd_req         // Read request
    ,output logic [DATA_WIDTH-1:0]    rd_dout        // Read data
	,output logic                     rd_out_valid
	// will need a rd_out_valid
    ,output logic                     fifo_empty
    ,output logic                     init_done
	,output logic                     full
    ,output logic [DATA_WIDTH-1:0]    usedw

);
// this will require some form of initialisation



logic [DATA_WIDTH-1:0] pointer_counter;
logic                     fifo_wr_req;         // Write enable
logic [DATA_WIDTH-1:0]      fifo_wr_din;        // Write data


logic [DATA_WIDTH-1:0] val_lvl0; // first one to come output
logic                  val_lvl0_valid;
logic [DATA_WIDTH-1:0] val_lvl1; // first one to come output
logic                  val_lvl1_valid;

logic                  fifo_rd_req; 
logic [DATA_WIDTH-1:0] fifo_rd_dout;

logic [DATA_WIDTH-1:0] lvl_rd_out;

logic rd_req_r;
logic rd_req_r2;
logic fill_rd_req;
logic read_request;

//assign rd_dout = lvl_rd_out;
// assign fifo_rd_req = rd_req | fill_rd_req;
 
 
assign fifo_rd_req = rd_req;
assign rd_dout = fifo_rd_dout;


generate
	if (INITIALISE_POINTERS == "YES") begin : GEN_INITIALISE
		always_ff @(posedge clk) begin
			if (init_done == 1'b0) begin //initialise the pointers.
				if (pointer_counter == {DATA_WIDTH{1'b1}} ) begin // all locations are initialised
					init_done <= 1'b1;
				end	else begin
					fifo_wr_req <= 1'b1;
					pointer_counter <= pointer_counter + 1'b1;
				end
				fifo_wr_din <= pointer_counter;
			end else begin
				fifo_wr_req <= 1'b0;
				rd_out_valid <= rd_req && ~fifo_empty;
				fifo_wr_req <= wr_req;
				fifo_wr_din <= wr_din;
				// rd_req_r  <= rd_req | fill_rd_req;
				// rd_req_r2 <= rd_req_r;
				// rd_out_valid <= 1'b0;
				// // when a read request comes in, assign a read to the fifo as we will consume something.
				// // data appears 3 cycles after the request.
				// if ((rd_req == 1'b1 || read_request == 1'b1) && val_lvl0_valid == 1'b1) begin
					// lvl_rd_out <= val_lvl0;
					// val_lvl0 <= val_lvl1;
					// val_lvl0_valid <= val_lvl1_valid;
					// val_lvl1_valid <= 1'b0;
					// rd_out_valid <= 1'b1;
					// read_request <= 1'b0;
				// end else if (rd_req == 1'b1 && val_lvl1_valid == 1'b1) begin
					// lvl_rd_out <= val_lvl1;
					// val_lvl1_valid <= 1'b0;
					// rd_out_valid <= 1'b1;
					// read_request <= 1'b0;
				// end else if (rd_req == 1'b1) begin
					// read_request <= 1'b1;
				// end
				// if (val_lvl0_valid == 1'b0) begin
					// val_lvl0 <= val_lvl1;
					// val_lvl0_valid <= val_lvl1_valid;
					// val_lvl1_valid <= 1'b0;
				// end
				// if (rd_req_r2 == 1'b1) begin // can do a bypass here maybe, need to check if we have sent the data already
					// val_lvl1_valid <= 1'b1; // need to check with empty too
					// val_lvl1 <= fifo_rd_dout;
				// end
				
				// // prefill the pipeline
				// // only request something if we did not get an external request -- timing could be an issue here, need to pay attention on which clock cycle the request came in
				// fill_rd_req <= 1'b0;
				// if (fill_rd_req == 1'b0 && read_request == 1'b0 && val_lvl1_valid == 1'b0) begin
					// fill_rd_req <= 1'b1;
				// end
			end



			if (rstn == 1'b0) begin //reset
				init_done <= 1'b0;
				pointer_counter <= 'b0;
				fifo_wr_req <= 1'b0;
				// val_lvl0_valid <= 1'b0;
				// val_lvl1_valid <= 1'b0;
				// rd_req_r <= 1'b0;
				// rd_req_r2 <= 1'b0;
				// fill_rd_req <= 1'b0;
				rd_out_valid <= 1'b0;
				// read_request <= 1'b0;
			end
		end
	end	
	// else begin : GEN_NO_INITIALISE
		// always_ff @(posedge clk) begin
			// fifo_wr_req <= wr_req;
			// fifo_wr_din <= wr_din;

			// rd_req_r  <= rd_req | fill_rd_req;
			// rd_req_r2 <= rd_req_r;
			// // when a read request comes in, assign a read to the fifo as we will consume something.
			// // data appears 3 cycles after the request.
			// if (rd_req == 1'b1 && val_lvl0_valid == 1'b1) begin
				// lvl_rd_out <= val_lvl0;
				// val_lvl0 <= val_lvl1;
				// val_lvl0_valid <= val_lvl1_valid;
				// val_lvl1_valid <= 1'b0;
			// end else if (rd_req == 1'b1 && val_lvl1_valid == 1'b1) begin
				// lvl_rd_out <= val_lvl1;
				// val_lvl1_valid <= 1'b0;
			// end
			// if (val_lvl1 == 1'b0) begin
				// val_lvl0 <= val_lvl1;
				// val_lvl0_valid <= val_lvl1_valid;
				// val_lvl1_valid <= 1'b0;
			// end
			// if (rd_req_r2 == 1'b1) begin // can do a bypass here maybe, need to check if we have sent the data already
				// val_lvl1_valid <= 1'b1; // need to check with empty too
				// val_lvl1 <= fifo_rd_dout;
			// end
			
			// // prefill the pipeline
			// // only request something if we did not get an external request -- timing could be an issue here, need to pay attention on which clock cycle the request came in
			// fill_rd_req <= 1'b0;
			// if (fill_rd_req == 1'b0 && rd_req_r == 1'b0 && rd_req_r2 == 1'b0 && val_lvl1_valid == 1'b0) begin
				// fill_rd_req <= 1'b1;
			// end

			// if (rstn == 1'b0) begin //reset
				// init_done <= 1'b1;
				// pointer_counter <= 'b0;
				// fifo_wr_req <= 1'b0;
				// val_lvl0_valid <= 1'b0;
				// val_lvl1_valid <= 1'b0;
				// rd_req_r <= 1'b0;
				// rd_req_r2 <= 1'b0;
				// fill_rd_req <= 1'b0;
			// end
		// end
	// end
endgenerate

// need to add 2 level of prefetch, level0 will be the data we are getting, level1 will be the second level
// there will be a need for a bypass function too to accelerate getting the data when we first start or when we fetch from empty


/*    scfifo #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(FIFO_DEPTH)
    ) u_fifo (
        .clk     (clk),
        .reset   (~rstn),
        .wr_en   (wr_req),
        .rd_en   (rd_req),
        .data_in (wr_din),
        .data_out(rd_dout),
        .full    (full),
        .empty   (fifo_empty),
        .usedw   (usedw)
    );
*/
   scfifo #(
         .add_ram_output_register ("ON")
        ,.lpm_numwords            (FIFO_DEPTH)
        ,.lpm_showahead           ("OFF")            // Data available immediately
        ,.lpm_type                ("scfifo")
        ,.lpm_width               (DATA_WIDTH)  
        ,.lpm_widthu              ($clog2(FIFO_DEPTH))
        ,.overflow_checking       ("ON")
        ,.underflow_checking      ("ON")
        ,.use_eab                 ("ON")             // Use block RAMs
		,.intended_device_family  ("agilex7")
    ) scfifo_component (
         .clock      (clk)
        ,.sclr       (~rstn)    // Active-high sync clear
		,.aclr       (1'b0)
        ,.data       (fifo_wr_din)
        ,.wrreq      (fifo_wr_req)
        ,.rdreq      (fifo_rd_req)
        ,.q          (fifo_rd_dout)
        ,.empty      (fifo_empty)
        ,.full       (full)
		,.usedw       (usedw)
		,.almost_empty ()
		,.almost_full  ()
		,.eccstatus ()
		
    );
endmodule
