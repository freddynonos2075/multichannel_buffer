module rd_latency1_to_0 #(
  parameter int WIDTH = 32
)(
  input  logic               clk,
  input  logic               rst_n,

  // Latency-1 producer interface
  output logic               in_rd_en,    // request (pulse 1 cycle)
  //input  logic               in_rd_valid, // data arrives 1 cycle after request
  input  logic [WIDTH-1:0]   in_rd_data,

  // Latency-0 consumer interface
  input  logic               out_rd_en,   // consumer requests data and expects it same cycle
  //output logic               out_rd_valid,
  output logic [WIDTH-1:0]   out_rd_data
);

logic [WIDTH-1:0] data_reg;
logic out_rd_en_r;

always_ff @(posedge clk) begin
	if (out_rd_en == 1'b0 && out_rd_en_r== 1'b1) begin
		data_reg <= in_rd_data;
	end
	out_rd_en_r <= out_rd_en;
end

assign out_rd_data=(out_rd_en_r==0)?data_reg:in_rd_data;
assign in_rd_en  = out_rd_en;
endmodule
