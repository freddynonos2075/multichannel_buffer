

module simple_scfifo #(
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH      = 16
)(
    input  logic                  clk,
    input  logic                  reset,
    input  logic                  wr_en,
    input  logic                  rd_en,
    input  logic [DATA_WIDTH-1:0] data_in,
    output logic [DATA_WIDTH-1:0] data_out,
    output logic                  full,
    output logic                  empty,
    output logic [$clog2(DEPTH):0] usedw
);

    // ------------------------------------------------------
    // Use localparam for array sizing (Verilator quirk fix)
    // ------------------------------------------------------
    localparam int DEPTH_C = DEPTH;

    // Declare memory using fixed constant bounds
    logic [DATA_WIDTH-1:0] mem [0:DEPTH_C-1];

    logic [$clog2(DEPTH_C)-1:0] wr_ptr, rd_ptr;
    logic [$clog2(DEPTH_C+1)-1:0] count;

    // ------------------------------------------------------
    // Write
    // ------------------------------------------------------
    always_ff @(posedge clk) begin
        if (reset) begin
            wr_ptr <= '0;
        end else if (wr_en && !full) begin
            mem[wr_ptr] <= data_in;
            wr_ptr <= wr_ptr + 1'b1;
        end
    end

    // ------------------------------------------------------
    // Read
    // ------------------------------------------------------
    always_ff @(posedge clk) begin
        if (reset) begin
            rd_ptr   <= '0;
            data_out <= '0;
        end else if (rd_en && !empty) begin
            data_out <= mem[rd_ptr];
            rd_ptr   <= rd_ptr + 1'b1;
        end
    end

    // ------------------------------------------------------
    // Count management
    // ------------------------------------------------------
    always_ff @(posedge clk) begin
        if (reset) begin
            count <= '0;
        end else begin
            unique case ({wr_en && !full, rd_en && !empty})
                2'b10: count <= count + 1'b1;
                2'b01: count <= count - 1'b1;
                default: count <= count;
            endcase
        end
    end

    // ------------------------------------------------------
    // Status
    // ------------------------------------------------------
    assign full  = ({27'b0,count} == DEPTH_C);
    assign empty = (count == 0);
    assign usedw = count;

endmodule
