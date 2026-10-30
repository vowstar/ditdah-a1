// SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
// SPDX-License-Identifier: MIT
module DitDahA1FloatFormat #(parameter W=32, FLEN=64)(
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
  recFNToIN #(E,S,32) toWord(1'b1,ar,roundingMode,!instruction[20],wordInteger,wordFlags);
  recFNToIN #(E,S,64) toLong(1'b1,ar,roundingMode,!instruction[20],longInteger,longFlags);
  wire less,equal,greater,unordered;
  compareRecFN #(E,S) compare(ar,br,operation==20 && instruction[14:12]!=2,less,equal,greater,unordered,compareFlags);
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
      5: begin floating=instruction[12]?maximum:minimum; exceptions=compareFlags; end
      8: begin floating=convertedRaw; exceptions=conversionFlags; end
      20: begin selected=instruction[14:12]==2?equal:instruction[14:12]==1?less:less||equal; exceptions=compareFlags; end
      24: begin selected=instruction[21]?longInteger:{{32{wordInteger[31]}},wordInteger}; exceptions={|integerFlags[2:1],3'b0,integerFlags[0]&&!(|integerFlags[2:1])}; end
      26: begin floating=integerFloatRaw; exceptions=integerFloatFlags; end
      28: begin selected=instruction[12]?{54'b0,classification}:W==32?{{32{a[31]}},a[31:0]}:a; exceptions=0; end
      30: begin floating=a[W-1:0]; exceptions=0; end
      default: begin end
    endcase
    if(fused || !(operation==20 || operation==24 || operation==28))
      selected=W==32 && FLEN==64?{32'hffffffff,floating}:floating;
  end
  assign result=selected;
  assign flags=exceptions;
  assign divideResult=W==32 && FLEN==64?{32'hffffffff,divideRaw}:divideRaw;
endmodule

module DitDahA1Fpu #(parameter FLEN=64)(
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
  wire doublePrecision=input_bits_instruction[25];
  wire division=input_bits_instruction[6:0]==7'h53 && (input_bits_instruction[31:27]==3 || input_bits_instruction[31:27]==11);
  wire [63:0] singleResult,doubleResult,singleDivide,doubleDivide;
  wire [4:0] singleFlags,doubleFlags,singleDivideFlags,doubleDivideFlags;
  wire singleReady,doubleReady,singleDone,doubleDone;
  wire accept=input_valid&&input_ready;
  DitDahA1FloatFormat #(32,FLEN) singleUnit(clock,reset,accept&&division&&!doublePrecision,input_bits_instruction,input_bits_a,input_bits_b,input_bits_c,input_bits_roundingMode,
    singleResult,singleDivide,singleFlags,singleDivideFlags,singleReady,singleDone);
  generate if(FLEN==64) begin
    DitDahA1FloatFormat #(64,FLEN) doubleUnit(clock,reset,accept&&division&&doublePrecision,input_bits_instruction,input_bits_a,input_bits_b,input_bits_c,input_bits_roundingMode,
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
