// we will use this to store pointers.
// this may be free pointers as well as the pointers per queue
// just a memory at the base
// need to move this to a SC fifo

module pointers #(
     parameter DATA_WIDTH = 10 // the 2 parameters are related and should only be one
	,parameter string INITIALISE_POINTERS = "YES"
)(
     input  logic                     clk
    ,input  logic                     rstn
    ,input  logic                     wr_req         // Write enable
    ,input  logic [DATA_WIDTH-1:0]    wr_din         // Write data
    ,input  logic                     rd_req         // Read request
    ,output logic [DATA_WIDTH-1:0]    rd_dout        // Read data
    ,output logic                     fifo_empty
    ,output logic                     init_done
	,output logic                     full
    ,output logic [DATA_WIDTH-1:0]    usedw

);
// this will require some form of initialisation

localparam int FIFO_DEPTH = 2** DATA_WIDTH;

logic [DATA_WIDTH-1:0] pointer_counter;
logic                     fifo_wr_req;         // Write enable
logic [DATA_WIDTH:0]      fifo_wr_din;        // Write data


 
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
				fifo_wr_req <= wr_req;
				fifo_wr_din <= wr_din;
			end

			if (rstn == 1'b0) begin //reset
				init_done <= 1'b0;
				pointer_counter <= 'b0;
				fifo_wr_req <= 1'b0;
			end
		end
	end	else begin : GEN_NO_INITIALISE
		always_ff @(posedge clk) begin
			fifo_wr_req <= wr_req;
			fifo_wr_din <= wr_din;
			if (rstn == 1'b0) begin //reset
				init_done <= 1'b0;
				pointer_counter <= 'b0;
				fifo_wr_req <= 1'b0;
			end
		end
	end
endgenerate


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
        ,.lpm_width               (DATA_WIDTH)  // +1 for TLAST bit
        ,.lpm_widthu              ($clog2(FIFO_DEPTH))
        ,.overflow_checking       ("ON")
        ,.underflow_checking      ("ON")
        ,.use_eab                 ("ON")             // Use block RAMs
		,.intended_device_family  ("agilex7")
    ) scfifo_component (
         .clock      (clk)
        ,.sclr       (~rstn)    // Active-high sync clear
        ,.data       (fifo_wr_din)
        ,.wrreq      (fifo_wr_req)
        ,.rdreq      (rd_req)
        ,.q          (rd_dout)
        ,.empty      (fifo_empty)
        ,.full       (full)
		,.usedw       (usedw)
    );
endmodule
