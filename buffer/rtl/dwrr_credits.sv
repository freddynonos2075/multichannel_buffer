// this is a simple RAM in which the value of the next flow to have credit will be stored

module dwrr_credits #(
     parameter DEPTH_W = 5 // this is the number of entries for the credit update table. It must be greater or equal to FLOW_W 
	,parameter FLOW_W = 3 // must be lower or equal to DEPTH_W
	,parameter MAX_CREDIT_W = 3
	,parameter string INITIALISE_POINTERS = "YES"
)(
     input  logic                     clk
    ,input  logic                     rstn
	// ,input  logic                     packet_tlast  // time to add credits 
    // ,input  logic [FLOW_W-1:0]        flow_check    // which flow are we checking
    // ,output logic [MAX_CREDIT_W-1:0]  flow_credit_value  // how much credit on the flow (latency of 2 most likely -- TBC)
	// ,input  logic                     consume_credit_valid // we are using a credit on this flow
	// ,input  logic [FLOW_W-1:0]        consume_credit_flow // flow number that we are using
	,input  logic                     rd_req
	,output logic [FLOW_W-1:0]        rd_out
    ,output logic                     init_done

);
// this will require some form of initialisation

localparam int FIFO_DEPTH = 2** DEPTH_W;

logic [DEPTH_W-1:0] pointer_counter;
logic [DEPTH_W-1:0] pointer_counter_r;
logic                     fifo_wr_req;         // Write enable
logic [FLOW_W-1:0]        fifo_wr_din;        // Write data



// ---------------------------------------
//     Where the next credits are given
// --------------------------------------- 
generate
	if (INITIALISE_POINTERS == "YES") begin : GEN_INITIALISE
		always_ff @(posedge clk) begin
			fifo_wr_req <= 1'b0;
			if (init_done == 1'b0) begin //initialise the pointers.
				if (pointer_counter == {DEPTH_W{1'b1}} ) begin // all locations are initialised
					init_done <= 1'b1;
				end
				fifo_wr_req <= 1'b1;
				pointer_counter <= pointer_counter + 1'b1;
				fifo_wr_din <= pointer_counter[FLOW_W-1:0];
			end else begin
				if (rd_req == 1'b1) begin
					pointer_counter <= pointer_counter + 1'b1;
				end
			end

			pointer_counter_r <= pointer_counter;
			if (rstn == 1'b0) begin //reset
				init_done <= 1'b0;
				pointer_counter <= {DEPTH_W{1'b0}};
				pointer_counter_r <= {DEPTH_W{1'b0}};
				fifo_wr_req <= 1'b0;
				
			end
			
		end
	end	else begin : GEN_NO_INITIALISE
		always_ff @(posedge clk) begin
			if (rstn == 1'b0) begin //reset
				init_done <= 1'b0;
				pointer_counter <= {DEPTH_W{1'b0}};
				pointer_counter_r <= {DEPTH_W{1'b0}};
				fifo_wr_req <= 1'b0;
			end
		end
	end
endgenerate
   
// this RAM module contains the order on which to add credits next
/* altsyncram #(
        .operation_mode                    ("DUAL_PORT"), //SINGLE_PORT
        .width_a                           (FLOW_W),
        .widthad_a                         (DEPTH_W),
        .numwords_a                        (1 << DEPTH_W),

        .width_b                           (FLOW_W),
        .widthad_b                         (DEPTH_W),
        .numwords_b                        (1 << DEPTH_W),

        .outdata_reg_b                     ("CLOCK1"),  // can set to "CLOCK1" if you want registered output
        .read_during_write_mode_mixed_ports("DONT_CARE"),
        .clock_enable_input_a              ("BYPASS"),
        .clock_enable_input_b              ("BYPASS"),
        .clock_enable_output_b             ("BYPASS"),
        .byte_size                         (8)
    ) credit_order_ram (
        // Write port A
        .clock0    (clk),
        .wren_a    (fifo_wr_req),
        .address_a (pointer_counter),
        .data_a    (fifo_wr_din),

        // Read port B
        .clock1    (clk),
        .address_b (pointer_counter),
        .q_b       (rd_dout),

        // Unused ports
        .aclr0     (1'b0),
        .aclr1     (1'b0),
        .clocken0  (1'b1),
        .clocken1  (1'b1),
        .clocken2  (1'b1),
        .clocken3  (1'b1),
        .byteena_a (1'b1),
        .rden_b    (1'b1)
    );
 */	

    altsyncram #(
        .operation_mode                     ("SINGLE_PORT"),
        .widthad_a                          (DEPTH_W),
        .width_a                            (FLOW_W),
        .numwords_a                         (1 << DEPTH_W),

        // *** REGISTERED OUTPUT ***
        .outdata_reg_a                      ("CLOCK0"),

        // async clear settings for the registered output
        .outdata_aclr_a                     ("NONE"),

        .indata_aclr_a                      ("NONE"),
        .address_aclr_a                     ("NONE"),
        .wrcontrol_aclr_a                   ("NONE"),

        .clock_enable_input_a               ("BYPASS"),
        .clock_enable_output_a              ("BYPASS"),

        // Read-during-write behavior
        .read_during_write_mode_port_a      ("DONT_CARE")
        // or: "NEW_DATA_NO_NBE_READ", "NEW_DATA_WITH_NBE_READ", "DONT_CARE"
    ) ram_inst (
        .clock0          (clk),
        .wren_a          (fifo_wr_req),
        .address_a       (pointer_counter_r),
        .data_a          (fifo_wr_din),
        .q_a             (rd_out),

        .aclr0           (~rstn),
        .aclr1           (1'b0),
        .clock1          (1'b0),
        .clocken0        (1'b1),
        .clocken1        (1'b1),
        .clocken2        (1'b1),
        .clocken3        (1'b1),

        .byteena_a       ('b1),
        .rden_a          (1'b1),

        // Unused dual-port signals
        .data_b          (),
        .address_b       (),
        .wren_b          (),
        .rden_b          (),
        .q_b             (),
        .byteena_b       (),
        .addressstall_b  ()
    );



endmodule
