interface axi4lite_if #(
  parameter int ADDR_WIDTH = 32,
  parameter int DATA_WIDTH = 32
)(
  input logic ACLK,
  input logic ARESETn
);

  // --------------------
  // Write address channel
  // --------------------
  logic [ADDR_WIDTH-1:0] AWADDR;
  logic                  AWVALID;
  logic                  AWREADY;

  // --------------------
  // Write data channel
  // --------------------
  logic [DATA_WIDTH-1:0]   WDATA;
  logic [DATA_WIDTH/8-1:0] WSTRB;
  logic                    WVALID;
  logic                    WREADY;

  // --------------------
  // Write response channel
  // --------------------
  logic [1:0] BRESP;
  logic       BVALID;
  logic       BREADY;

  // --------------------
  // Read address channel
  // --------------------
  logic [ADDR_WIDTH-1:0] ARADDR;
  logic                  ARVALID;
  logic                  ARREADY;

  // --------------------
  // Read data channel
  // --------------------
  logic [DATA_WIDTH-1:0] RDATA;
  logic [1:0]            RRESP;
  logic                  RVALID;
  logic                  RREADY;

  // ============================================================
  // Modports
  // ============================================================

  // AXI4-Lite Master
  modport master (
	input ACLK, ARESETn,
	 
	// Write address
    output AWADDR, AWVALID,
    input  AWREADY,

    // Write data
    output WDATA, WSTRB, WVALID,
    input  WREADY,

    // Write response
    input  BRESP, BVALID,
    output BREADY,

    // Read address
    output ARADDR, ARVALID,
    input  ARREADY,

    // Read data
    input  RDATA, RRESP, RVALID,
    output RREADY
  );

  // AXI4-Lite Slave
  modport slave (
	input ACLK, ARESETn,

    // Write address
    input  AWADDR, AWVALID,
    output AWREADY,

    // Write data
    input  WDATA, WSTRB, WVALID,
    output WREADY,

    // Write response
    output BRESP, BVALID,
    input  BREADY,

    // Read address
    input  ARADDR, ARVALID,
    output ARREADY,

    // Read data
    output RDATA, RRESP, RVALID,
    input  RREADY
  );

endinterface
