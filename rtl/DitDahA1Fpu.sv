// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
module DitDahA1FloatFormat #(parameter W=32, FLEN=64, ZFA=0, ZFHMIN=0)(
  input clock, reset, divideValid,
  input [31:0] instruction,
  input [63:0] a,b,c,
  input [2:0] roundingMode,
  output [63:0] result, divideResult,
  output [4:0] flags, divideFlags,
  output divideReady, divideDone
);
  localparam E=W==32?8:11, S=W-E;
  localparam [W-1:0] NAN=({W{1'b1}} >> 1) ^ ((1 << (S-2))-1);
  localparam [W-1:0] ONE=((1 << (E-1))-1) << (S-1);
  wire [W-1:0] av=W==32 && FLEN==64 && a[63:32]!=32'hffffffff ? NAN : a[W-1:0];
  wire [W-1:0] bv=W==32 && FLEN==64 && b[63:32]!=32'hffffffff ? NAN : b[W-1:0];
  wire [W-1:0] cv=W==32 && FLEN==64 && c[63:32]!=32'hffffffff ? NAN : c[W-1:0];
  wire [4:0] operation=instruction[31:27];
  wire roundInteger=ZFA && operation==8 && instruction[24:21]==2 && !instruction[26];
  wire modularInteger=ZFA && W==64 && operation==24 && instruction[24:20]==8;
  wire [2:0] integerRounding=modularInteger?3'd1:roundingMode;
  wire fused=instruction[6:0]!=7'h53;
  wire add=operation<=1 && !fused, multiply=operation==2 && !fused;
  wire [W-1:0] ma=av, mb=add?ONE:bv;
  wire [W-1:0] mc=add?bv:multiply?{av[W-1]^bv[W-1],{(W-1){1'b0}}}:cv;
  wire [W:0] ar,br,mar,mbr,mcr,fma,quotient,integerFloat;
  wire [W-1:0] fmaRaw,divideRaw,divideDecoded,integerFloatRaw;
  wire [4:0] fmaFlags,integerFloatFlags,compareFlags;
  fNToRecFN #(E,S) encodeA(av,ar),encodeB(bv,br),encodeMa(ma,mar),encodeMb(mb,mbr),encodeMc(mc,mcr);
  mulAddRecFN #(E,S) arithmetic(1'b1,fused?instruction[3:2]:add?{1'b0,operation[0]}:2'b0,mar,mbr,mcr,roundingMode,fma,fmaFlags);
  divSqrtRecFN_small #(E,S,0) division(~reset,clock,1'b1,divideReady,divideValid,operation==11,ar,br,roundingMode,divideDone,,quotient,divideFlags);
  recFNToFN #(E,S) decodeFma(fma,fmaRaw),decodeDivide(quotient,divideDecoded),decodeInteger(integerFloat,integerFloatRaw);
  // Recoded special values permit unspecified low exponent bits.
  assign divideRaw=quotient[W-1:W-3]==0?{quotient[W],{(W-1){1'b0}}}:
    quotient[W-1:W-3]==6?{quotient[W],{E{1'b1}},{(S-1){1'b0}}}:
    quotient[W-1:W-3]==7?NAN:divideDecoded;
  wire [63:0] integerInput=instruction[21]?a:instruction[20]?{32'b0,a[31:0]}:{{32{a[31]}},a[31:0]};
  iNToRecFN #(64,E,S) fromInteger(1'b1,!instruction[20],integerInput,roundingMode,integerFloat,integerFloatFlags);
  wire [31:0] wordInteger;
  wire [63:0] longInteger;
  wire [2:0] wordFlags,longFlags;
  recFNToIN #(E,S,32) toWord(1'b1,ar,integerRounding,!instruction[20],wordInteger,wordFlags);
  recFNToIN #(E,S,64) toLong(1'b1,ar,roundingMode,roundInteger||!instruction[20],longInteger,longFlags);
  wire less,equal,greater,unordered;
  compareRecFN #(E,S) compare(ar,br,operation==20 && instruction[14:12]!=2 && !(ZFA && instruction[14]),less,equal,greater,unordered,compareFlags);
  wire [W-1:0] convertedRaw;
  wire [4:0] conversionFlags;
  generate if(FLEN==64) begin
    localparam OW=W==32?64:32, OE=OW==32?8:11, OS=OW-OE;
    wire [OW-1:0] other=W==64 && a[63:32]!=32'hffffffff ? 32'h7fc00000 : a[OW-1:0];
    wire [OW:0] recoded;
    wire [W:0] converted;
    fNToRecFN #(OE,OS) encodeOther(other,recoded);
    recFNToRecFN #(OE,OS,E,S) convert(1'b1,recoded,roundingMode,converted,conversionFlags);
    recFNToFN #(E,S) decodeConverted(converted,convertedRaw);
  end else begin
    assign convertedRaw=0;
    assign conversionFlags=0;
  end endgenerate
  wire [W-1:0] roundedRaw,halfWidened;
  wire [15:0] halfNarrowed;
  wire [4:0] halfWidenFlags,halfNarrowFlags;
  generate if(ZFA) begin
    wire [W:0] roundedRecoded;
    iNToRecFN #(64,E,S) roundedInteger(1'b1,1'b1,longInteger,roundingMode,roundedRecoded,);
    recFNToFN #(E,S) decodeRounded(roundedRecoded,roundedRaw);
  end else assign roundedRaw=0;
  if(ZFHMIN) begin
    wire [15:0] halfOperand=(FLEN==64 ? a[63:16]!=48'hffffffffffff : a[31:16]!=16'hffff)?16'h7e00:a[15:0];
    wire [16:0] halfRecoded,narrowRecoded;
    wire [W:0] wideRecoded;
    fNToRecFN #(5,11) encodeHalf(halfOperand,halfRecoded);
    recFNToRecFN #(5,11,E,S) widenHalf(1'b1,halfRecoded,roundingMode,wideRecoded,halfWidenFlags);
    recFNToFN #(E,S) decodeWidened(wideRecoded,halfWidened);
    recFNToRecFN #(E,S,5,11) narrowHalf(1'b1,ar,roundingMode,narrowRecoded,halfNarrowFlags);
    recFNToFN #(5,11) decodeNarrowed(narrowRecoded,halfNarrowed);
  end else begin
    assign halfWidened=0; assign halfNarrowed=0; assign halfWidenFlags=0; assign halfNarrowFlags=0;
  end endgenerate
  function automatic [W-1:0] immediateValue(input [4:0] index);
    integer exponent;
    reg [1:0] fraction;
    begin
      exponent=(1<<(E-1))-1; fraction=0;
      case(index)
        1: exponent=1;
        2: exponent=exponent-16; 3: exponent=exponent-15;
        4: exponent=exponent-8; 5: exponent=exponent-7;
        6: exponent=exponent-4; 7: exponent=exponent-3;
        8,9,10,11,12,13,14,15,16,17,18,19,20,21,22: begin exponent=exponent-2+(({27'b0,index}-8)>>2); fraction=index[1:0]; end
        23: exponent=exponent+2; 24: exponent=exponent+3; 25: exponent=exponent+4;
        26: exponent=exponent+7; 27: exponent=exponent+8;
        28: exponent=exponent+15; 29: exponent=exponent+16;
        30,31: begin exponent=(1<<E)-1; fraction=index==31?2:0; end
      endcase
      immediateValue=0;
      immediateValue[W-1]=index==0;
      immediateValue[W-2:S-1]=exponent[E-1:0];
      immediateValue[S-2 -: 2]=fraction;
    end
  endfunction
  localparam BIAS=(1<<(E-1))-1;
  wire integralMagnitude=av[W-2:S-1]>=BIAS+S-1;
  wire signed [E:0] exponent=$signed({1'b0,av[W-2:S-1]})-BIAS;
  wire [63:0] significand={{(64-S){1'b0}},1'b1,av[S-2:0]};
  wire [63:0] modularMagnitude=exponent<0 || exponent>=S-1+32 ? 0 :
    exponent>=S-1 ? significand<<(exponent-(S-1)) : significand>>((S-1)-exponent);
  wire [31:0] modularWord=av[W-1]?-modularMagnitude[31:0]:modularMagnitude[31:0];
  wire nanA=&av[W-2:S-1] && |av[S-2:0], nanB=&bv[W-2:S-1] && |bv[S-2:0];
  wire zeroA=av[W-2:0]==0, zeroB=bv[W-2:0]==0;
  wire [W-1:0] minimum=nanA?(nanB?NAN:bv):nanB?av:zeroA&&zeroB?{av[W-1]|bv[W-1],{(W-1){1'b0}}}:less?av:bv;
  wire [W-1:0] maximum=nanA?(nanB?NAN:bv):nanB?av:zeroA&&zeroB?{av[W-1]&bv[W-1],{(W-1){1'b0}}}:greater?av:bv;
  wire [W-1:0] injected={instruction[13]?av[W-1]^bv[W-1]:instruction[12]?~bv[W-1]:bv[W-1],av[W-2:0]};
  wire expZero=av[W-2:S-1]==0, expOnes=&av[W-2:S-1], fractionZero=av[S-2:0]==0;
  wire [9:0] classification={expOnes&&!fractionZero&&av[S-2],expOnes&&!fractionZero&&!av[S-2],
    !av[W-1]&&expOnes&&fractionZero,!av[W-1]&&!expZero&&!expOnes,!av[W-1]&&expZero&&!fractionZero,!av[W-1]&&zeroA,
    av[W-1]&&zeroA,av[W-1]&&expZero&&!fractionZero,av[W-1]&&!expZero&&!expOnes,av[W-1]&&expOnes&&fractionZero};
  reg [W-1:0] floating;
  reg [63:0] selected;
  reg [4:0] exceptions;
  wire [2:0] integerFlags=instruction[21]?longFlags:wordFlags;
  always @* begin
    floating=fmaRaw; selected=0; exceptions=fmaFlags;
    if(!fused) case(operation)
      4: begin floating=injected; exceptions=0; end
      5: begin floating=ZFA && instruction[13] && (nanA||nanB)?NAN:instruction[12]?maximum:minimum; exceptions=compareFlags; end
      8: begin
        floating=convertedRaw; exceptions=conversionFlags;
        if(ZFHMIN && instruction[26:25]==2) begin floating={{(W-16){1'b1}},halfNarrowed}; exceptions=halfNarrowFlags; end
        else if(ZFHMIN && instruction[24:20]==2) begin floating=halfWidened; exceptions=halfWidenFlags; end
        else if(roundInteger) begin
          floating=nanA?NAN:integralMagnitude?av:roundedRaw[W-2:0]==0?{av[W-1],{(W-1){1'b0}}}:roundedRaw;
          exceptions={nanA&&!av[S-2],3'b0,instruction[20]&&!integralMagnitude&&longFlags[0]};
        end
      end
      20: begin selected=instruction[14:12]==2?equal:instruction[12]?less:less||equal; exceptions=compareFlags; end
      24: begin
        selected=instruction[21]?longInteger:{{32{wordInteger[31]}},wordInteger};
        if(modularInteger) selected=expOnes?0:{{32{modularWord[31]}},modularWord};
        exceptions={|integerFlags[2:1],3'b0,integerFlags[0]&&!(|integerFlags[2:1])};
      end
      26: begin floating=integerFloatRaw; exceptions=integerFloatFlags; end
      28: begin selected=instruction[12]?{54'b0,classification}:ZFHMIN&&instruction[26:25]==2?{{48{a[15]}},a[15:0]}:W==32?{{32{a[31]}},a[31:0]}:a; exceptions=0; end
      30: begin floating=ZFA&&instruction[24:20]==1?immediateValue(instruction[19:15]):ZFHMIN&&instruction[26:25]==2?{{(W-16){1'b1}},a[15:0]}:a[W-1:0]; exceptions=0; end
      default: begin end
    endcase
    if(fused || !(operation==20 || operation==24 || operation==28))
      selected=W==32 && FLEN==64?{32'hffffffff,floating}:floating;
  end
  assign result=selected;
  assign flags=exceptions;
  assign divideResult=W==32 && FLEN==64?{32'hffffffff,divideRaw}:divideRaw;
endmodule

module DitDahA1Fpu #(parameter FLEN=64, ZFA=0, ZFHMIN=0)(
  input clock, reset, input_valid,
  output input_ready,
  input [31:0] input_bits_instruction,
  input [63:0] input_bits_a,input_bits_b,input_bits_c,
  input [2:0] input_bits_roundingMode,
  output output_valid,
  input output_ready,
  output [63:0] output_bits_value,
  output [4:0] output_bits_flags
);
  reg busy,valid;
  reg [63:0] value;
  reg [4:0] flags;
  wire doublePrecision=input_bits_instruction[26:25]==1 || (ZFHMIN && input_bits_instruction[26:25]==2 && input_bits_instruction[31:27]==8 && input_bits_instruction[24:20]==1);
  wire division=input_bits_instruction[6:0]==7'h53 && (input_bits_instruction[31:27]==3 || input_bits_instruction[31:27]==11);
  wire [63:0] singleResult,doubleResult,singleDivide,doubleDivide;
  wire [4:0] singleFlags,doubleFlags,singleDivideFlags,doubleDivideFlags;
  wire singleReady,doubleReady,singleDone,doubleDone;
  wire accept=input_valid&&input_ready;
  DitDahA1FloatFormat #(32,FLEN,ZFA,ZFHMIN) singleUnit(clock,reset,accept&&division&&!doublePrecision,input_bits_instruction,input_bits_a,input_bits_b,input_bits_c,input_bits_roundingMode,
    singleResult,singleDivide,singleFlags,singleDivideFlags,singleReady,singleDone);
  generate if(FLEN==64) begin
    DitDahA1FloatFormat #(64,FLEN,ZFA,ZFHMIN) doubleUnit(clock,reset,accept&&division&&doublePrecision,input_bits_instruction,input_bits_a,input_bits_b,input_bits_c,input_bits_roundingMode,
      doubleResult,doubleDivide,doubleFlags,doubleDivideFlags,doubleReady,doubleDone);
  end else begin
    assign doubleResult=0; assign doubleDivide=0; assign doubleFlags=0; assign doubleDivideFlags=0; assign doubleReady=0; assign doubleDone=0;
  end endgenerate
  assign input_ready=!busy&&!valid&&(!division||(doublePrecision?doubleReady:singleReady));
  assign output_valid=valid;
  assign output_bits_value=value;
  assign output_bits_flags=flags;
  always @(posedge clock) begin
    if(reset) begin busy<=0;valid<=0;end
    else begin
      if(valid&&output_ready)valid<=0;
      if(accept) begin
        if(division) busy<=1;
        else begin valid<=1;value<=doublePrecision?doubleResult:singleResult;flags<=doublePrecision?doubleFlags:singleFlags;end
      end
      if(busy&&(singleDone||doubleDone)) begin
        busy<=0;valid<=1;value<=doubleDone?doubleDivide:singleDivide;flags<=doubleDone?doubleDivideFlags:singleDivideFlags;
      end
    end
  end
endmodule
