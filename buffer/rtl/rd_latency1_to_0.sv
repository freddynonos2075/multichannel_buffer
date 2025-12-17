module rd_latency1_to_0 #(
  parameter WIDTH = 32
)(
  input  logic              clk,
  input  logic              rst_n,

  // Latency-1 input interface
  output logic              in_rd_en,
  input  logic              in_rd_valid,
  input  logic [WIDTH-1:0]  in_rd_data,

  // Latency-0 output interface
  input  logic              out_rd_en,
  output logic              out_rd_valid,
  output logic [WIDTH-1:0]  out_rd_data
);

  logic              buf_valid;
  logic [WIDTH-1:0]  buf_data;

  // Prefetch when buffer empty
  assign in_rd_en = ~buf_valid;

  // Output is immediate if buffer has data
  assign out_rd_valid = buf_valid;
  assign out_rd_data  = buf_data;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      buf_valid <= 1'b0;
    end else begin
      // Capture incoming data
      if (in_rd_valid) begin
        buf_data  <= in_rd_data;
        buf_valid <= 1'b1;
      end

      // Consume data
      if (out_rd_en && buf_valid) begin
        buf_valid <= 1'b0;
      end
    end
  end

endmodule
