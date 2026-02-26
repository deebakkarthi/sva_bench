module eth_random_assert (
    input MTxClk,
    input Reset,
    input StateJam,
    input StateJam_q,
    input [3:0] RetryCnt,
    input [15:0] NibCnt,
    input [9:0] ByteCnt,
    output RandomEq0,
    output RandomEqByteCnt
);

    wire Feedback;
    reg [9:0] x;
    wire [9:0] Random;
    reg [9:0] RandomLatched;

    assign Feedback = ~(x[2] ^ x[9]);

    assign Random[0] = x[0];
    assign Random[1] = (RetryCnt > 1) ? x[1] : 1'b0;
    assign Random[2] = (RetryCnt > 2) ? x[2] : 1'b0;
    assign Random[3] = (RetryCnt > 3) ? x[3] : 1'b0;
    assign Random[4] = (RetryCnt > 4) ? x[4] : 1'b0;
    assign Random[5] = (RetryCnt > 5) ? x[5] : 1'b0;
    assign Random[6] = (RetryCnt > 6) ? x[6] : 1'b0;
    assign Random[7] = (RetryCnt > 7) ? x[7] : 1'b0;
    assign Random[8] = (RetryCnt > 8) ? x[8] : 1'b0;
    assign Random[9] = (RetryCnt > 9) ? x[9] : 1'b0;

    // Reset: x clears to 0
    x_reset_to_zero : assert property (
        @(posedge MTxClk) Reset |=> (x == 10'h000)
    );

    // Reset: RandomLatched clears to 0
    random_latched_reset_to_zero : assert property (
        @(posedge MTxClk) Reset |=> (RandomLatched == 10'h000)
    );

    // LFSR shift: x shifts on each clock (no reset)
    lfsr_shift_register : assert property (
        @(posedge MTxClk) disable iff (Reset)
        (1'b1) |=> (x == {$past(x[8:0]), $past(~(x[2] ^ x[9]))})
    );

    // Feedback is XNOR of x[2] and x[9]
    feedback_xnor : assert property (
        @(posedge MTxClk) disable iff (Reset)
        Feedback == ~(x[2] ^ x[9])
    );

    // RandomLatched updates when StateJam & StateJam_q
    random_latched_capture : assert property (
        @(posedge MTxClk) disable iff (Reset)
        (StateJam && StateJam_q) |=> (RandomLatched == $past(Random))
    );

    // RandomLatched holds when NOT (StateJam & StateJam_q)
    random_latched_hold : assert property (
        @(posedge MTxClk) disable iff (Reset)
        !(StateJam && StateJam_q) |=> (RandomLatched == $past(RandomLatched))
    );

    // RandomEq0 is asserted when RandomLatched is zero
    random_eq0_correct : assert property (
        @(posedge MTxClk) disable iff (Reset)
        RandomEq0 == (RandomLatched == 10'h000)
    );

    // RandomEqByteCnt is asserted when ByteCnt equals RandomLatched and lower 7 NibCnt bits are all 1
    random_eq_bytecnt_correct : assert property (
        @(posedge MTxClk) disable iff (Reset)
        RandomEqByteCnt == ((ByteCnt[9:0] == RandomLatched) && (&NibCnt[6:0]))
    );

    // Random[0] always equals x[0]
    random_bit0_always_x0 : assert property (
        @(posedge MTxClk) disable iff (Reset)
        Random[0] == x[0]
    );

    // Random[1] is x[1] when RetryCnt > 1, else 0
    random_bit1_retryCnt_gt1 : assert property (
        @(posedge MTxClk) disable iff (Reset)
        (RetryCnt > 1) ? (Random[1] == x[1]) : (Random[1] == 1'b0)
    );

    // Random[2] is x[2] when RetryCnt > 2, else 0
    random_bit2_retryCnt_gt2 : assert property (
        @(posedge MTxClk) disable iff (Reset)
        (RetryCnt > 2) ? (Random[2] == x[2]) : (Random[2] == 1'b0)
    );

    // Random[3] is x[3] when RetryCnt > 3, else 0
    random_bit3_retryCnt_gt3 : assert property (
        @(posedge MTxClk) disable iff (Reset)
        (RetryCnt > 3) ? (Random[3] == x[3]) : (Random[3] == 1'b0)
    );

    // Random[4] is x[4] when RetryCnt > 4, else 0
    random_bit4_retryCnt_gt4 : assert property (
        @(posedge MTxClk) disable iff (Reset)
        (RetryCnt > 4) ? (Random[4] == x[4]) : (Random[4] == 1'b0)
    );

    // Random[5] is x[5] when RetryCnt > 5, else 0
    random_bit5_retryCnt_gt5 : assert property (
        @(posedge MTxClk) disable iff (Reset)
        (RetryCnt > 5) ? (Random[5] == x[5]) : (Random[5] == 1'b0)
    );

    // Random[6] is x[6] when RetryCnt > 6, else 0
    random_bit6_retryCnt_gt6 : assert property (
        @(posedge MTxClk) disable iff (Reset)
        (RetryCnt > 6) ? (Random[6] == x[6]) : (Random[6] == 1'b0)
    );

    // Random[7] is x[7] when RetryCnt > 7, else 0
    random_bit7_retryCnt_gt7 : assert property (
        @(posedge MTxClk) disable iff (Reset)
        (RetryCnt > 7) ? (Random[7] == x[7]) : (Random[7] == 1'b0)
    );

    // Random[8] is x[8] when RetryCnt > 8, else 0
    random_bit8_retryCnt_gt8 : assert property (
        @(posedge MTxClk) disable iff (Reset)
        (RetryCnt > 8) ? (Random[8] == x[8]) : (Random[8] == 1'b0)
    );

    // Random[9] is x[9] when RetryCnt > 9, else 0
    random_bit9_retryCnt_gt9 : assert property (
        @(posedge MTxClk) disable iff (Reset)
        (RetryCnt > 9) ? (Random[9] == x[9]) : (Random[9] == 1'b0)
    );

    // When RetryCnt is 0, all Random bits except bit 0 are 0
    random_upper_bits_zero_when_retryCnt_zero : assert property (
        @(posedge MTxClk) disable iff (Reset)
        (RetryCnt == 4'd0) |-> (Random[9:1] == 9'h000)
    );

    // RandomLatched remains 0 after reset until StateJam & StateJam_q
    random_latched_stays_zero_after_reset : assert property (
        @(posedge MTxClk)
        $rose(Reset) |=> (RandomLatched == 10'h000)
    );

    // x is 0 immediately after reset deasserts if Reset was held
    x_zero_after_reset_deasserts : assert property (
        @(posedge MTxClk)
        $rose(Reset) |=> (x == 10'h000)
    );

endmodule

bind eth_random eth_random_assert eth_random_assert_instance (.*);
