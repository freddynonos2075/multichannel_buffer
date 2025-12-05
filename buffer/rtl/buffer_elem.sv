// simple dual port RAM
// we'll need to decide if we want to have a multitude of small modules or one large one which will deal with with addressing


//======================================================
// Dual-Port RAM using Altera altsyncram megafunction
//  - Port A: Read/Write
//  - Port B: Read/Write
//======================================================
module buffer_elem #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 10
)(
    input  wire                     clk,
    input  wire                     we,         // Write enable
    input  wire [ADDR_WIDTH-1:0]    wr_addr,    // Write address
    input  wire [DATA_WIDTH-1:0]    din,        // Write data
    input  wire [ADDR_WIDTH-1:0]    rd_addr,    // Read address
    output wire [DATA_WIDTH-1:0]    dout        // Read data
);

    // Derived parameter
    localparam NUM_WORDS = 2**ADDR_WIDTH;

// missing the read address
//dummy_altsyncram #(
//     .WIDTH (DATA_WIDTH)
//    ,.DEPTH (2**ADDR_WIDTH)
//) altsyncram_inst (
//     .clock   (clk) 
//    ,.data    (din) 
//    ,.address (wr_addr) 
//    ,.wren    (we)
//    ,.q       (dout)
//);


    // Instantiate the altsyncram megafunction
    altsyncram #(
        .operation_mode                ("DUAL_PORT"),
        .width_a                       (DATA_WIDTH),
        .widthad_a                     (ADDR_WIDTH),
        .numwords_a                    (NUM_WORDS),
        .width_b                       (DATA_WIDTH),
        .widthad_b                     (ADDR_WIDTH),
        .numwords_b                    (NUM_WORDS),
        .lpm_type                      ("altsyncram"),
        .outdata_reg_b                 ("UNREGISTERED"),
        .indata_aclr_a                 ("NONE"),
        .address_aclr_a                ("NONE"),
        .address_aclr_b                ("NONE"),
        .wrcontrol_aclr_a              ("NONE"),
        .outdata_aclr_b                ("NONE"),
        .read_during_write_mode_mixed_ports ("DONT_CARE"),
        .power_up_uninitialized        ("FALSE")
    ) altsyncram_component (
        // Port A — Write
        .clock0    (clk),
        .wren_a    (we),
        .address_a (wr_addr),
        .data_a    (din),

        // Port B — Read
        .clock1    (clk),
        .address_b (rd_addr),
        .q_b       (dout),

        // Unused connections
        .aclr0     (1'b0),
        .aclr1     (1'b0),
        .byteena_a (1'b1),
        .byteena_b (1'b1),
        .rden_a    (1'b1),
        .rden_b    (1'b1)
    );

endmodule
