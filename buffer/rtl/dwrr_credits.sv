// this is a simple RAM in which the value of the next flow to have credit will be stored

module dwrr_credits #(
     parameter DEPTH_W = 5 // this is the number of entries for the credit update table. It must be greater or equal to FLOW_W 
	,parameter FLOW_W = 3 // must be lower or equal to DEPTH_W
	,parameter MAX_CREDIT_W = 3
	,parameter string INITIALISE_POINTERS = "YES"
)(
     input  logic                     clk
    ,input  logic                     rstn
	,input  logic                     packet_tlast  // time to add credits 
    ,input  logic [FLOW_W-1:0]        flow_check    // which flow are we checking
    ,output logic [MAX_CREDIT_W-1:0]  flow_credit_value  // how much credit on the flow (latency of 2 most likely -- TBC)
	,input  logic                     consume_credit_valid // we are using a credit on this flow
	,input  logic [FLOW_W-1:0]        consume_credit_flow // flow number that we are using
    ,output logic                     init_done

);
// this will require some form of initialisation

localparam int FIFO_DEPTH = 2** DEPTH_W;

logic [DEPTH_W-1:0] pointer_counter;
logic                     fifo_wr_req;         // Write enable
logic [DEPTH_W:0]      fifo_wr_din;        // Write data


// ---------------------------------------
//     Where the next credits are given
// --------------------------------------- 
generate
	if (INITIALISE_POINTERS == "YES") begin : GEN_INITIALISE
		always_ff @(posedge clk) begin
			if (init_done == 1'b0) begin //initialise the pointers.
				if (pointer_counter == {DEPTH_W{1'b1}} ) begin // all locations are initialised
					init_done <= 1'b1;
				end	else begin
					fifo_wr_req <= 1'b1;
					pointer_counter <= pointer_counter + 1'b1;
					fifo_wr_din <= pointer_counter[FLOW_WIDTH-1:0];
				end
			end else begin
				if (rd_req == 1'b1) begin
					pointer_counter <= pointer_counter + 1'b1;
				end
			end

			if (rstn == 1'b0) begin //reset
				init_done <= 1'b0;
				pointer_counter <= {DEPTH_W{1'b0}};
				fifo_wr_req <= 1'b0;
				
			end
		end
	end	else begin : GEN_NO_INITIALISE
		always_ff @(posedge clk) begin
			if (rstn == 1'b0) begin //reset
				init_done <= 1'b0;
				pointer_counter <= 'b0;
				fifo_wr_req <= 1'b0;
			end
		end
	end
endgenerate

// this RAM module contains the order on which to add credits next
altsyncram #(
        .operation_mode                    ("SIMPLE_DUAL_PORT"),
        .width_a                           (FLOW_W),
        .widthad_a                         (DEPTH_W),
        .numwords_a                        (1 << DEPTH_W),

        .width_b                           (FLOW_W),
        .widthad_b                         (DEPTH_W),
        .numwords_b                        (1 << DEPTH_W),

        .outdata_reg_b                     ("UNREGISTERED"),  // can set to "CLOCK1" if you want registered output
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


// ---------------------------------------
//     Credits for a given flow
// --------------------------------------- 

// Probably will use some register based counters for the credits. Cost will be a few k registers but will make life a lot simpler. It won't scale past a few 10's or maybe 100's of flows

logic [FLOW_W-1:0]       credit_pointer_counter;
logic [MAX_CREDIT_W-1:0] checked_flow_value;

logic                    credit_init_done;
// logic                    flow_credit_add;
// logic [MAX_CREDIT_W-1:0] flow_credit_add_value;

logic [MAX_CREDIT_W-1:0] flow_credit_table [FLOW_W-1:0];

always_ff (@posedge clk) begin
	rd_req <= 1'b0;
	if (credit_init_done == 1'b0) begin
		flow_credit_table[credit_pointer_counter] <= {1'b0,{MAX_CREDIT_W-1{1'b1}}}; // give half of the max number of credits
		credit_pointer_counter <= credit_pointer_counter + 1'b1;
		if (credit_pointer_counter == 	{FLOW_W{1'b1}}) begin
			credit_init_done <= 1'b1;
		end		
	end else begin
		if (consume_credit_valid == 1'b1 && packet_tlast == 1'b1 && consume_credit_flow == rd_dout) begin // we consume and give back a credit, no net 0 but need to move to the nexr entry
			rd_req <= 1'b1;
		end else begin
			if (consume_credit_valid == 1'b1) begin
				flow_credit_table[consume_credit_flow] <= flow_credit_table[consume_credit_flow] - 1'b1;
			end
			if (packet_tlast == 1'b1) begin // add some credits somewhere
				flow_credit_table[rd_dout] <= flow_credit_table[rd_dout] - 1'b1;
				rd_req <= 1'b1;
			end
		end
	end
	flow_credit_value <= flow_credit_table[flow_check];
	if (rstn == 1'b0) begin
		credit_init_done <= 1'b0;
		credit_pointer_counter <= {FLOW_W{1'b0}};
	end
end

// always_ff @(posedge clk) begin
	// if (credit_init_done == 1'b0) begin
		// flow_credit_add_value <= {1'b0,{MAX_CREDIT_W-1{1'b1}}}; // give half of the max number of credits
		// flow_credit_add <= 1'b1;
		// credit_pointer_counter <= credit_pointer_counter + 1'b1;
		// if (credit_pointer_counter == 	{FLOW_W{1'b1}}) begin
			// credit_init_done <= 1'b1;
		// end		
	// end else begin // init done
		// // consume credits
		// // there may be a race condition between cunsumption and replenishing. This can happen at any time but especially if we had short packets.
		// // as a result we may need to have a queue for the replenishing and add when possible -- will ignore for now and assume best case, but will need to put an assertion to highlight when this happens
		// if (consume_credit_valid == 1'b1) begin // this is a read modify write
			// consume_credit_flow
		
 	// end
	// if (rstn == 1'b0) begin
		// credit_pointer_counter <= {FLOW_W{1'b0}};
		// credit_init_done <= 1'b0;
	// end
// end

	// ,input  logic                     packet_tlast  // time to add credits 
    // ,input  logic [FLOW_W-1:0]        flow_check    // which flow are we checking
    // ,output logic [MAX_CREDIT_W-1:0]  flow_credit_value  // how much credit on the flow (latency of 2 most likely -- TBC)
	// ,input  logic                     consume_credit_valid // we are using a credit on this flow
	// ,input  logic [FLOW_W-1:0]        consume_credit_flow // flow number that we are using

// This RAM module will contain the actual credits for each flow
 // altsyncram #(
        // .operation_mode                    ("SIMPLE_DUAL_PORT"),
        // .width_a                           (MAX_CREDIT_W),
        // .widthad_a                         (FLOW_W),
        // .numwords_a                        (1 << FLOW_W),

        // .width_b                           (MAX_CREDIT_W),
        // .widthad_b                         (FLOW_W),
        // .numwords_b                        (1 << FLOW_W),

        // .outdata_reg_b                     ("UNREGISTERED"),  // can set to "CLOCK1" if you want registered output
        // .read_during_write_mode_mixed_ports("DONT_CARE"),
        // .clock_enable_input_a              ("BYPASS"),
        // .clock_enable_input_b              ("BYPASS"),
        // .clock_enable_output_b             ("BYPASS"),
        // .byte_size                         (8)
    // ) flow_credit_ram (
        // // Write port A
        // .clock0    (clk),
        // .wren_a    (),
        // .address_a (),
        // .data_a    (),

        // // Read port B
        // .clock1    (clk),
        // .address_b (),
        // .q_b       (),

        // // Unused ports
        // .aclr0     (1'b0),
        // .aclr1     (1'b0),
        // .clocken0  (1'b1),
        // .clocken1  (1'b1),
        // .clocken2  (1'b1),
        // .clocken3  (1'b1),
        // .byteena_a (1'b1),
        // .rden_b    (1'b1)
    // );

endmodule
