`timescale 1ns/1ps

// ============================================================
// AXI-Stream Testbench: Variable-width, multi-packet generator
// ============================================================
module tb_axi_stream;

    // -------------------------
    // Parameters
    // -------------------------
    parameter int DATA_WIDTH = 64;     // Bits per beat
    parameter int MAX_PACKET_BYTES = 512;
    parameter int NUM_PACKETS = 4;

	parameter int SB_WIDTH = 10; // sideband width in bits
	parameter int BUF_SEG_AW = 5; // this will represent the number of segments 2**n
	parameter int SEGMENT_SIZE_W = 3; // 2**n Bytes

    localparam int BYTES_PER_BEAT = DATA_WIDTH / 8;
	

    // -------------------------
    // DUT interface signals
    // -------------------------
    logic                   clk;
    logic                   rst_n;
    logic [DATA_WIDTH-1:0]  tdata;
    logic                   tvalid;
    logic                   tready;
    logic                   tlast;

    // -------------------------
    // receive interface
    // -------------------------
    logic [DATA_WIDTH-1:0]  rdata;
    logic                   rvalid;
    logic                   rready;
    logic                   rlast;
	logic [BYTES_PER_BEAT-1:0] rkeep;
	

    // -------------------------
    // Clock & Reset Generation
    // -------------------------
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 100 MHz
    end

    initial begin
        rst_n = 0;
        repeat (10) @(posedge clk);
        rst_n = 1;
    end

    // -------------------------
    // DUT or AXI-Slave stub
    // -------------------------
    // For now, simulate a slave that always accepts data
    //assign tready = 1'b1;

    // -------------------------
    // Task: send one packet
    // -------------------------
    task automatic send_packet(input int pkt_bytes, input int pkt_number);
        int beats;
        static int count = 0;
		beats = (pkt_bytes + BYTES_PER_BEAT - 1) / BYTES_PER_BEAT; // weird way to check the modulo, but intuitively seems ok
        $display("[%0t] Sending packet: %0d bytes (%0d beats)", $time, pkt_bytes, beats);
		

        for (int i = 0; i < beats; i++) begin
            @(posedge clk);
            tdata  <= {pkt_number[7:0],{(BYTES_PER_BEAT-1){count[7:0]}}}; // random payload
			//tdata  <= {$random, $random} >> (128 - DATA_WIDTH); // random payload
            tvalid <= 1'b1;
            tlast  <= (i == beats - 1);
			count <= count + 1;

            // wait for tready
            wait (tready);
        end

        // Deassert after final beat
        @(posedge clk);
        tvalid <= 0;
        tlast  <= 0;
    endtask

    // -------------------------
    // Stimulus
    // -------------------------
    initial begin
        tdata  = '0;
        tvalid = 0;
        tlast  = 0;

        @(posedge rst_n);
        repeat (3) @(posedge clk);

        // Send multiple packets
        for (int p = 0; p < NUM_PACKETS; p++) begin
            static int pkt_len = $urandom_range(64, MAX_PACKET_BYTES); // 64–512 bytes
            send_packet(pkt_len,p+100);

            // Random idle gap between packets
            repeat ($urandom_range(2, 10)) @(posedge clk);
        end

        $display("[%0t] All packets sent.", $time);
        #100 $finish;
    end

    // -------------------------
    // read data
    // -------------------------

assign rready = 1'b1;
buffer_top #(
	 .DATA_WIDTH (DATA_WIDTH)
	,.BUF_SEG_AW (BUF_SEG_AW) // this will represent the number of segments 2**n
	,.SEGMENT_SIZE_W (SEGMENT_SIZE_W) // 2**n Bytes
	,.SB_WIDTH (SB_WIDTH) // sideband information including flow number in bits
) DUT (
	// clock and reset
	 .clk  (clk)// single clock domain for this module
	,.rstn (rst_n)// syncronous reset
	// write side
    ,.s_wdata   (tdata)// Data from master
    ,.s_wvalid  (tvalid)// Data valid
    ,.s_wready  (tready)// Ready to accept data
    ,.s_wlast   (tlast)// End of frame/packet 
    //,input  wire [(DATA_WIDTH/8)-1:0] s_wkeep // Byte qualifiers -- only bytes not used would be at the end of the packet
    ,.s_wsideband ({SB_WIDTH{1'b0}})
	
	// read side
    ,.s_rdata   (rdata)// Data from master
    ,.s_rvalid  (rvalid)// Data valid
    ,.s_rready  (rready)// Ready to accept data
    ,.s_rlast   (rlast)// End of frame/packet 
    ,.s_rkeep   (rkeep)// Byte qualifiers -- only bytes not used would be at the end of the packet
		
	// control TBD
	
);

endmodule
