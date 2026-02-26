module eth_crc_sva (Clk, Reset, Data, Enable, Initialize, Crc, CrcError);

input Clk;
input Reset;
input [3:0] Data;
input Enable;
input Initialize;
input [31:0] Crc;
input CrcError;

wire [31:0] CrcNext;

assign CrcNext[0] = Enable & (Data[0] ^ Crc[28]);
assign CrcNext[1] = Enable & (Data[1] ^ Data[0] ^ Crc[28] ^ Crc[29]);
assign CrcNext[2] = Enable & (Data[2] ^ Data[1] ^ Data[0] ^ Crc[28] ^ Crc[29] ^ Crc[30]);
assign CrcNext[3] = Enable & (Data[3] ^ Data[2] ^ Data[1] ^ Crc[29] ^ Crc[30] ^ Crc[31]);
assign CrcNext[4] = (Enable & (Data[3] ^ Data[2] ^ Data[0] ^ Crc[28] ^ Crc[30] ^ Crc[31])) ^ Crc[0];
assign CrcNext[5] = (Enable & (Data[3] ^ Data[1] ^ Data[0] ^ Crc[28] ^ Crc[29] ^ Crc[31])) ^ Crc[1];
assign CrcNext[6] = (Enable & (Data[2] ^ Data[1] ^ Crc[29] ^ Crc[30])) ^ Crc[2];
assign CrcNext[7] = (Enable & (Data[3] ^ Data[2] ^ Data[0] ^ Crc[28] ^ Crc[30] ^ Crc[31])) ^ Crc[3];
assign CrcNext[8] = (Enable & (Data[3] ^ Data[1] ^ Data[0] ^ Crc[28] ^ Crc[29] ^ Crc[31])) ^ Crc[4];
assign CrcNext[9] = (Enable & (Data[2] ^ Data[1] ^ Crc[29] ^ Crc[30])) ^ Crc[5];
assign CrcNext[10] = (Enable & (Data[3] ^ Data[2] ^ Data[0] ^ Crc[28] ^ Crc[30] ^ Crc[31])) ^ Crc[6];
assign CrcNext[11] = (Enable & (Data[3] ^ Data[1] ^ Data[0] ^ Crc[28] ^ Crc[29] ^ Crc[31])) ^ Crc[7];
assign CrcNext[12] = (Enable & (Data[2] ^ Data[1] ^ Data[0] ^ Crc[28] ^ Crc[29] ^ Crc[30])) ^ Crc[8];
assign CrcNext[13] = (Enable & (Data[3] ^ Data[2] ^ Data[1] ^ Crc[29] ^ Crc[30] ^ Crc[31])) ^ Crc[9];
assign CrcNext[14] = (Enable & (Data[3] ^ Data[2] ^ Crc[30] ^ Crc[31])) ^ Crc[10];
assign CrcNext[15] = (Enable & (Data[3] ^ Crc[31])) ^ Crc[11];
assign CrcNext[16] = (Enable & (Data[0] ^ Crc[28])) ^ Crc[12];
assign CrcNext[17] = (Enable & (Data[1] ^ Crc[29])) ^ Crc[13];
assign CrcNext[18] = (Enable & (Data[2] ^ Crc[30])) ^ Crc[14];
assign CrcNext[19] = (Enable & (Data[3] ^ Crc[31])) ^ Crc[15];
assign CrcNext[20] = Crc[16];
assign CrcNext[21] = Crc[17];
assign CrcNext[22] = (Enable & (Data[0] ^ Crc[28])) ^ Crc[18];
assign CrcNext[23] = (Enable & (Data[1] ^ Data[0] ^ Crc[29] ^ Crc[28])) ^ Crc[19];
assign CrcNext[24] = (Enable & (Data[2] ^ Data[1] ^ Crc[30] ^ Crc[29])) ^ Crc[20];
assign CrcNext[25] = (Enable & (Data[3] ^ Data[2] ^ Crc[31] ^ Crc[30])) ^ Crc[21];
assign CrcNext[26] = (Enable & (Data[3] ^ Data[0] ^ Crc[31] ^ Crc[28])) ^ Crc[22];
assign CrcNext[27] = (Enable & (Data[1] ^ Crc[29])) ^ Crc[23];
assign CrcNext[28] = (Enable & (Data[2] ^ Crc[30])) ^ Crc[24];
assign CrcNext[29] = (Enable & (Data[3] ^ Crc[31])) ^ Crc[25];
assign CrcNext[30] = Crc[26];
assign CrcNext[31] = Crc[27];

// Reset sets Crc to all ones
crc_reset_value : assert property (@(posedge Clk) Reset |=> (Crc == 32'hffffffff));

// Initialize sets Crc to all ones (when no Reset)
crc_initialize_value : assert property (@(posedge Clk) (!Reset && Initialize) |=> (Crc == 32'hffffffff));

// When neither Reset nor Initialize, Crc takes CrcNext
crc_updates_to_crc_next : assert property (@(posedge Clk) disable iff (Reset) (!Initialize) |=> (Crc == $past(CrcNext)));

// Crc is all ones immediately after reset (synchronous check after async reset)
crc_reset_async_value : assert property (@(posedge Clk) $rose(Reset) |-> (Crc == 32'hffffffff));

// CrcError is asserted when Crc does not equal magic number
crc_error_asserted_when_not_magic : assert property (@(posedge Clk) (Crc != 32'hc704dd7b) |-> CrcError);

// CrcError is deasserted when Crc equals magic number
crc_error_deasserted_when_magic : assert property (@(posedge Clk) (Crc == 32'hc704dd7b) |-> !CrcError);

// CrcError is combinational function of Crc
crc_error_combinational : assert property (@(posedge Clk) CrcError == (Crc != 32'hc704dd7b));

// When Enable is low, CrcNext bits that depend only on previous Crc shift correctly (bit 20)
crc_next_bit20_when_disabled : assert property (@(posedge Clk) (!Enable) |-> (CrcNext[20] == Crc[16]));

// When Enable is low, CrcNext bits that depend only on previous Crc shift correctly (bit 21)
crc_next_bit21_when_disabled : assert property (@(posedge Clk) (!Enable) |-> (CrcNext[21] == Crc[17]));

// When Enable is low, CrcNext bits that depend only on previous Crc shift correctly (bit 30)
crc_next_bit30_when_disabled : assert property (@(posedge Clk) (!Enable) |-> (CrcNext[30] == Crc[26]));

// When Enable is low, CrcNext bits that depend only on previous Crc shift correctly (bit 31)
crc_next_bit31_when_disabled : assert property (@(posedge Clk) (!Enable) |-> (CrcNext[31] == Crc[27]));

// When Enable is low, low-order CrcNext bits become 0 (no data XOR)
crc_next_bits0to3_zero_when_disabled : assert property (@(posedge Clk) (!Enable) |-> (CrcNext[3:0] == 4'b0));

// After Initialize, next cycle Crc is all ones regardless of Enable
crc_after_initialize_is_all_ones : assert property (@(posedge Clk) disable iff (Reset) Initialize |=> (Crc == 32'hffffffff));

// Crc remains all ones on consecutive Initialize cycles
crc_stays_all_ones_during_initialize : assert property (@(posedge Clk) disable iff (Reset) (Initialize && (Crc == 32'hffffffff)) |=> (Crc == 32'hffffffff || Initialize == 1'b0 || Reset));

// CrcNext bit 16 when Enable: XOR of Data[0] and Crc[28] XOR'd with Crc[12]
crc_next_bit16_combinational : assert property (@(posedge Clk) CrcNext[16] == ((Enable & (Data[0] ^ Crc[28])) ^ Crc[12]));

// CrcNext bit 0 when Enable
crc_next_bit0_combinational : assert property (@(posedge Clk) CrcNext[0] == (Enable & (Data[0] ^ Crc[28])));

// CrcNext bits 0-3 are purely data XOR with upper Crc bits when Enable
crc_next_bit3_combinational : assert property (@(posedge Clk) CrcNext[3] == (Enable & (Data[3] ^ Data[2] ^ Data[1] ^ Crc[29] ^ Crc[30] ^ Crc[31])));

endmodule

bind eth_crc eth_crc_sva eth_crc_sva_instance (.*);
