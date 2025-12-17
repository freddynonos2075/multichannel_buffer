`timescale 1ns/1ps

module tb_axi_s2;

  // ------------------------------------------------------------
  // Parameters
  // ------------------------------------------------------------
  parameter DATA_W     = 32;
  parameter MAX_PKT_SZ = 128;     // bytes excluding pkt_num + flow byte
  parameter NUM_PKTS   = 257;

	parameter int BUF_SEG_AW = 5; // this will represent the number of segments 2**n
	parameter int SEGMENT_SIZE_W = 3; // 2**n Bytes
	localparam int BYTES_PER_BEAT = DATA_W / 8;
	localparam int FLOWS_W = 3;
	localparam int SB_WIDTH = FLOWS_W; // sideband width in bits

  // ------------------------------------------------------------
  // DUT Signals
  // ------------------------------------------------------------
  logic clk, resetn;

  // AXIS Master TB→DUT
  logic [DATA_W-1:0]   s_axis_tdata;
  logic                s_axis_tvalid;
  logic                s_axis_tready;
  logic                s_axis_tlast;
  logic [SB_WIDTH-1:0] s_axis_tsideband;	
  // AXIS Slave DUT→TB
  logic [DATA_W-1:0]   m_axis_tdata;
  logic                m_axis_tvalid;
  logic                m_axis_tready;
  logic                m_axis_tlast;
 
 // ------------------------------------------------------------
  // log files
  // ------------------------------------------------------------

	integer fd_send;
	integer fd_rcvd;

  // ------------------------------------------------------------
  // Clock and Reset
  // ------------------------------------------------------------
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    resetn = 0;
    repeat(10) @(posedge clk);
    resetn = 1;
  end

  // ------------------------------------------------------------
  // Types and Scoreboard
  // ------------------------------------------------------------
  typedef struct {
    int             pkt_id;        // Unique packet number
    byte            flow_id;       // Flow selector
    logic [31:0]    data[$];        // Payload (first byte is flow_id)
  } packet_t;

  // Store sent and received packets (lookup by pkt_id)
  packet_t sent_pkts    [int];
  packet_t received_pkts[int];

  // ------------------------------------------------------------
  // DUT Instantiation (rename to match your DUT)
  // ------------------------------------------------------------

buffer_top #(
	 .DATA_WIDTH (DATA_W)
	,.BUF_SEG_AW (BUF_SEG_AW) // this will represent the number of segments 2**n
	,.SEGMENT_SIZE_W (SEGMENT_SIZE_W) // 2**n Bytes
	,.FLOWS_W (FLOWS_W)
	,.SB_WIDTH (FLOWS_W) // sideband information including flow number in bits
) DUT (
	// clock and reset
	 .clk  (clk)// single clock domain for this module
	,.rstn (resetn)// syncronous reset
	// write side
    ,.s_wdata   (s_axis_tdata)// Data from master
    ,.s_wvalid  (s_axis_tvalid)// Data valid
    ,.s_wready  (s_axis_tready)// Ready to accept data
    ,.s_wlast   (s_axis_tlast)// End of frame/packet 
    //,input  wire [(DATA_WIDTH/8)-1:0] s_wkeep // Byte qualifiers -- only bytes not used would be at the end of the packet
    ,.s_wsideband (s_axis_tsideband)
	
	// read side
    ,.s_rdata   (m_axis_tdata)// Data from master
    ,.s_rvalid  (m_axis_tvalid)// Data valid
    ,.s_rready  (m_axis_tready)// Ready to accept data
    ,.s_rlast   (m_axis_tlast)// End of frame/packet 
    ,.s_rkeep   ()// Byte qualifiers -- only bytes not used would be at the end of the packet
		
	// control TBD
	
);

  // ------------------------------------------------------------
  // Randomised backpressure on m_axis_tready
  // ------------------------------------------------------------
  always @(posedge clk) begin
    if (!resetn) begin
      m_axis_tready <= 0;
    end else begin // only deassert the ready between packets
		if ( m_axis_tlast == 1'b1 || m_axis_tready == 1'b0) begin
			m_axis_tready <= $urandom_range(0,1);  // Random 0/1 each cycle
		end else begin
			m_axis_tready <= 1;  // Random 0/1 each cycle
		end
	end
  end

  // ------------------------------------------------------------
  // Packet Generator
  // ------------------------------------------------------------
  function packet_t generate_packet(int id);
    
	static packet_t pkt;
    automatic int payload_len = $urandom_range(64/BYTES_PER_BEAT, MAX_PKT_SZ/BYTES_PER_BEAT); // these are clock cycles rather than bytes
	static int flow_id;
	
	pkt.data = {};
	pkt.pkt_id = -1;

	pkt.pkt_id = id;
    flow_id = $urandom_range(0, (2**FLOWS_W)-1);
	pkt.flow_id = flow_id; // 1-byte flow ID
    
    //pkt.data = new[payload_len + 2];

	
    // Byte 0: packet number
    pkt.data[0] = {4'h8,flow_id[3:0],payload_len[7:0],id[7:0],id[7:0]};
	

    // Byte 1: flow ID
    pkt.data[1] = {4'h4,flow_id[3:0],payload_len[7:0],id[7:0],flow_id[7:0]};

	//pkt.data.size = payload_len;
	//$fdisplay(fd_send,"------- GENERARING PACKET %d payload length %d ----------------",id,payload_len);
    // Remaining bytes: random payload
    for (int i = 2; i < payload_len; i++) begin
      //pkt.data[i] = $urandom();
	   	pkt.data[i] = {4'h2,flow_id[3:0],payload_len[7:0],id[7:0],i[7:0]};
	end
    //$display("Task generate packet of size  %0d -- %0d -- flow id %0x -- packet number %0x ...", payload_len, pkt.data.size(), pkt.data[1], pkt.data[0]);
	//$fdisplay(fd_send,"packet generated: %h",pkt);
    return pkt;
  endfunction

  // ------------------------------------------------------------
  // AXI-S Send Task (TB → DUT)
  // ------------------------------------------------------------
  task send_packet(packet_t pkt);
    static int idx_s;

	idx_s <= 0;
    @(posedge clk);
    s_axis_tvalid <= 1;
    //$display("Task Send packet of size  %0d ...", pkt.data.size());
	$fdisplay(fd_send, "***** packet %d flow %0x size %d *****", pkt.pkt_id,pkt.flow_id, pkt.data.size());
    while (idx_s < pkt.data.size()) begin
      s_axis_tdata <= pkt.data[idx_s];
      s_axis_tlast <= (idx_s == pkt.data.size()-1);
	  s_axis_tsideband <= pkt.flow_id;

      @(posedge clk);
      if (s_axis_tvalid && s_axis_tready) begin
		$fdisplay(fd_send, "%d data %x", idx_s,pkt.data[idx_s]);
        idx_s++;
	  end
    end

    s_axis_tvalid <= 0;
    s_axis_tlast  <= 0;
  endtask

  // ------------------------------------------------------------
  // AXI-S Receive Task (Out-of-Order OK)
  // ------------------------------------------------------------
  task receive_packet(output packet_t pkt);
	static int count = 0;
	static int idx_r;
	
    pkt.data = {};
    pkt.pkt_id = -1;
    idx_r = 0;
	wait(m_axis_tvalid);

	count = 0;
	//$display("************ starting size %d ****************", pkt.data.size());
    do begin
      @(posedge clk);
      if (m_axis_tvalid && m_axis_tready) begin
        pkt.data.push_back(m_axis_tdata[31:0]);
	    //$display("receiving packet count %d, data  %04x -- current size %d...", count, m_axis_tdata[31:0], pkt.data.size());
		count++;
		end
    end while (!(m_axis_tlast && m_axis_tvalid)); // should be last and valid
	// Extract packet number and flow_id

    pkt.pkt_id = pkt.data[0][15:8];
    pkt.flow_id = pkt.data[1];
	$fdisplay(fd_rcvd, "***** packet %d flow %0x size %d *****", pkt.pkt_id,pkt.flow_id, pkt.data.size());
	while (idx_r < pkt.data.size()) begin
		$fdisplay(fd_rcvd, "%d data %x", idx_r,pkt.data[idx_r]);
		idx_r++;
	end
	//$display("************ finished receiving packet %d flow %0x size %d ****************", pkt.pkt_id,pkt.flow_id, pkt.data.size());
  endtask

  // ------------------------------------------------------------
  // Scoreboard
  // Packets return out-of-order: match by pkt_id
  // ------------------------------------------------------------
  task check_scoreboard;

	  int error;
      packet_t s;
      packet_t r;

    $display("Checking %0d packets...", NUM_PKTS);
    $fdisplay(fd_rcvd,"Checking %0d packets...", NUM_PKTS);

	error = 0;
    foreach (sent_pkts[id]) begin
      if (!received_pkts.exists(id)) begin
        $display("***** ERROR: Packet %0d not received!", id);
        //$finish;
		error = 1;
      end else begin
		$display("..... Good: Packet %0d received!", id);
	  end

      s = sent_pkts[id];
      r = received_pkts[id];
	  $fdisplay(fd_rcvd,"------------------------------------------\nChecking packet %x \n----- sent: %x \n----- rcvd: %x",sent_pkts[id],s.data,r.data );

      // Length check
      if (s.data.size() != r.data.size()) begin
        $display("***** ERROR: pkt %0d length mismatch %0d != %0d ",
                id, s.data.size(), r.data.size());
		$fdisplay(fd_rcvd,"***** ERROR: pkt %0d length mismatch %0d != %0d ",
                id, s.data.size(), r.data.size());
        //$finish;
		error = 1;
       end else begin
		$display("..... Good: Packet length ok %0d received!", s.data.size());
	  end

      // Byte-by-byte check
      for (int i=0; i<s.data.size(); i++) begin
        if (s.data[i] != r.data[i]) begin
          $display("***** ERROR: pkt %0d byte mismatch at %0d: %0x != %0x",
                  id, i, s.data[i], r.data[i]);
          $fdisplay(fd_rcvd,"***** ERROR: pkt %0d byte mismatch at %0d: %0x != %0x",
                  id, i, s.data[i], r.data[i]);
        //$finish;
		error = 1;
        end
      end
	  if (error == 0) begin
		$display("..... PKT %0d (flow %0d) PASS", id, s.flow_id);
	  end else begin
//		  for (int i=0; i<s.data.size(); i++) begin
//			  $display("pkt %0d byte at %0d: sent: %0x rcvd: %0x", id, i, s.data[i], r.data[i]);
//		  end
		  $finish;
	  end
    end

    $display("ALL PACKETS PASSED ✓");
  endtask

  // ------------------------------------------------------------
  // Main Test Sequence
  // ------------------------------------------------------------
  initial begin
	fd_send = $fopen("tb_send.log", "w");
	if (fd_send == 0) begin	$fatal("Could not open tb_send.log");
	end

	fd_rcvd = $fopen("tb_rcvd.log", "w");
	if (fd_rcvd == 0) begin	$fatal("Could not open tb_rcvd.log");
	end
 
	wait(resetn);

    s_axis_tvalid = 0;
	
    fork
      // ------------------------------
      // SEND THREAD
      // ------------------------------
      begin
        for (int i=0; i<NUM_PKTS; i++) begin
		  packet_t pkt;
          pkt = generate_packet(i);
          sent_pkts[i] = pkt;
          $display(">>>>>>> TB: Sending pkt %0d, flow=%0d, size=%0d ",
                   i, pkt.flow_id, pkt.data.size());
          send_packet(pkt);
          repeat($urandom_range(1,5)) @(posedge clk);
        end
      end

      // ------------------------------
      // RECEIVE THREAD
      // ------------------------------
      begin
        for (int r=0; r<NUM_PKTS; r++) begin
          packet_t pkt;
          receive_packet(pkt);
          received_pkts[pkt.pkt_id] = pkt;
          $display("<<<<<<< TB: Received pkt %0d, flow=%0d, size=%0d -- remaining %d packets",
                   pkt.pkt_id, pkt.flow_id, pkt.data.size(),NUM_PKTS-r-1);
        end
      end
    join

    check_scoreboard();
	$fclose(fd_send);
	$fclose(fd_rcvd);

    $finish;
  end

endmodule
