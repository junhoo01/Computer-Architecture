//
//  Author: Prof. Taeweon Suh
//          Computer Science & Engineering
//          Korea University
//  Date: July 14, 2020
//  Description: Skeleton design of RV32I Single-cycle CPU

`timescale 1ns/1ns
`define simdelay 1

module rv32i_cpu (
          input         clk, reset,
            output [31:0] pc,         // program counter for instruction fetch
            input  [31:0] inst,       // incoming instruction
            output        Memwrite,   // 'memory write' control signal
            output [31:0] Memaddr,    // memory address 
            output [31:0] MemWdata,   // data to write to memory
            input  [31:0] MemRdata);  // data read from memory

  wire        auipc, lui;
  wire  [31:0] I_D_inst;
  wire        alusrc, regwrite;
  wire [4:0]  alucontrol;
  wire        memtoreg, memwrite;
  wire        branch, jal, jalr;

  // Instantiate Controller
  controller i_controller(

    .opcode   (I_D_inst[6:0]), 
    .funct7   (I_D_inst[31:25]), 
    .funct3   (I_D_inst[14:12]),

    .auipc    (auipc),
    .lui      (lui),
    .memtoreg (memtoreg),
    .memwrite (memwrite),
    .branch   (branch),
    .alusrc   (alusrc),
    .regwrite (regwrite),
    .jal      (jal),
    .jalr     (jalr),
    .alucontrol (alucontrol));

  // Instantiate Datapath
  datapath i_datapath(
    .clk        (clk),
    .reset      (reset),
    .auipc      (auipc),
    .lui        (lui),
    .memtoreg   (memtoreg),
    .memwrite   (memwrite),
    .branch     (branch),
    .alusrc     (alusrc),
    .regwrite   (regwrite),
    .jal        (jal),
    .jalr       (jalr),
    .alucontrol   (alucontrol),
    .pc       (pc),
    .inst       (inst),

    .E_M_aluout      (Memaddr),

    .MemWdata   (MemWdata),
    .MemRdata   (MemRdata),
    //#####start
    .I_D_inst (I_D_inst),
    .E_M_memwrite(Memwrite));
    //#####end

endmodule

//
// Instruction Decoder 
// to generate control signals for datapath
//
module controller(input  [6:0] opcode,
                  input  [6:0] funct7,
                  input  [2:0] funct3,
                  output       auipc,
                  output       lui,
                  output       alusrc,
                  output [4:0] alucontrol,
                  output       branch,
                  output       jal,
                  output       jalr,
                  output       memtoreg,
                  output       memwrite,
                  output       regwrite);

  maindec i_maindec(
    .opcode   (opcode),
    .auipc    (auipc),
    .lui      (lui),
    .memtoreg (memtoreg),
    .memwrite (memwrite),
    .branch   (branch),
    .alusrc   (alusrc),
    .regwrite (regwrite),
    .jal      (jal),
    .jalr     (jalr));

  aludec i_aludec( 
    .opcode     (opcode),
    .funct7     (funct7),
    .funct3     (funct3),
    .alucontrol (alucontrol));

endmodule

//
// RV32I Opcode map = Inst[6:0]
//
`define OP_R      7'b0110011
`define OP_I_ARITH  7'b0010011
`define OP_I_LOAD   7'b0000011
`define OP_I_JALR   7'b1100111
`define OP_S      7'b0100011
`define OP_B      7'b1100011
`define OP_U_LUI    7'b0110111
`define OP_J_JAL    7'b1101111

//
// Main decoder generates all control signals except alucontrol 
//
//
module maindec(input  [6:0] opcode,
               output       auipc,
               output       lui,
               output       regwrite,
               output       alusrc,
               output       memtoreg, memwrite,
               output       branch, 
               output       jal,
               output       jalr);

  reg [8:0] controls;

  assign {auipc, lui, regwrite, alusrc, 
       memtoreg, memwrite, branch, jal, 
       jalr} = controls;

  always @(*)
  begin
    case(opcode)
      `OP_R:      controls <=  9'b0010_0000_0; // R-type
      `OP_I_ARITH:  controls <=  9'b0011_0000_0; // I-type Arithmetic
      `OP_I_LOAD:   controls <=  9'b0011_1000_0; // I-type Load
      `OP_S:      controls <=  9'b0001_0100_0; // S-type Store
      `OP_B:      controls <=  9'b0000_0010_0; // B-type Branch
      `OP_U_LUI:    controls <=  9'b0111_0000_0; // LUI
      `OP_J_JAL:    controls <=  9'b0011_0001_0; // JAL
      `OP_I_JALR: controls <=  9'b0011_0000_1; // JALR

      default:      controls <=  9'b0000_0000_0; // ???
    endcase
  end

endmodule

//
// ALU decoder generates ALU control signal (alucontrol)
//
module aludec(input      [6:0] opcode,
              input      [6:0] funct7,
              input      [2:0] funct3,
              output reg [4:0] alucontrol);

  always @(*)

    case(opcode)

      `OP_R:      // R-type
    begin
      case({funct7,funct3})
       10'b0000000_000: alucontrol <=  5'b00000; // addition (add)
       10'b0100000_000: alucontrol <=  5'b10000; // subtraction (sub)
       10'b0000000_111: alucontrol <=  5'b00001; // and (and)
       10'b0000000_110: alucontrol <=  5'b00010; // or (or)
          default:         alucontrol <=  5'bxxxxx; // ???
        endcase
    end

      `OP_I_ARITH:   // I-type Arithmetic
    begin
      case(funct3)
       3'b000:  alucontrol <=  5'b00000; // addition (addi)

       3'b001:  alucontrol <=  5'b00100; // slli

       3'b110:  alucontrol <=  5'b00010; // or (ori)
       3'b111:  alucontrol <=  5'b00001; // and (andi)
       3'b100:  alucontrol <=  5'b00011; // xor (xori)
          default: alucontrol <=  5'bxxxxx; // ???
        endcase
    end

      `OP_I_LOAD:   // I-type Load (LW, LH, LB...)
        alucontrol <=  5'b00000;  // addition 

      `OP_B:      // B-type Branch (BEQ, BNE, ...)
        alucontrol <=  5'b10000;  // subtraction 

      `OP_S:      // S-type Store (SW, SH, SB)
        alucontrol <=  5'b00000;  // addition 

      `OP_U_LUI:    // U-type (LUI)
        alucontrol <=  5'b00000;  // addition

      `OP_I_JALR:   //I-type JALR
        alucontrol <=  5'b00000; // addition
      default: 
        alucontrol <=  5'b00000;  // 

    endcase
    
endmodule

//
// CPU datapath
//
module datapath(input         clk, reset,
                input  [31:0] inst,
                input         auipc,
                input         lui,
                input         regwrite,
                input         memtoreg,
                input         memwrite,

                input         alusrc, 
                input  [4:0]  alucontrol,
                input         branch,
                input         jal,
                input         jalr,

                output reg [31:0] pc,
                output [31:0] MemWdata,

                input  [31:0] MemRdata,

                //##### start
                output reg [31:0] E_M_aluout, // address
                output reg E_M_memwrite,      // memwrite
                output reg [31:0]I_D_inst);   // instance
                //##### end

  wire [4:0]  rs1, rs2, rd;
  wire [2:0]  funct3;
  reg [31:0]  rs1_data, rs2_data;
  reg  [31:0] rd_data;
  wire [20:1] jal_imm;
  wire [31:0] se_jal_imm;
  wire [12:1] br_imm;
  wire [31:0] se_br_imm;
  wire [31:0] se_imm_itype;
  wire [31:0] se_imm_stype;
  wire [31:0] auipc_lui_imm;
  reg  [31:0] alusrc1;
  reg  [31:0] alusrc2;
  wire [31:0] branch_dest, jal_dest;
  wire      Nflag, Zflag, Cflag, Vflag;

  wire      N1flag, Z1flag, C1flag, V1flag;

  wire      f3beq, f3blt,f3bgeu;

//##### start
  wire      f3bne;
//##### end

  wire      beq_taken;
  wire      blt_taken;
  wire      bgeu_taken;


//##### start
  wire      bne_taken;
  wire      b_taken;

//##### flush
  wire I_D_flush;
  wire D_E_flush;
  wire E_M_flush;
  wire M_W_flush;


//##### end

  //###### start
  //pc regs
  reg  [31:0] I_D_pc;
  reg  [31:0] D_E_pc;
  reg  [31:0] E_M_pc;
  reg  [31:0] M_W_pc;

  //stall
  reg Stall;

  //D->E
  

  reg [31:0] D_E_se_imm_itype;
  reg [31:0] D_E_se_imm_stype;
  reg [31:0] D_E_auipc_lui_imm;

  reg [31:0] D_E_rs1_data;
  reg [31:0] D_E_rs2_data;

  reg D_E_auipc, D_E_lui, D_E_regwrite, D_E_alusrc, D_E_memtoreg, D_E_memwrite, D_E_branch, D_E_jal, D_E_jalr;

  reg [4:0] D_E_alucontrol;
  reg [4:0] D_E_rs1, D_E_rs2;
  reg [4:0] D_E_rd;

  reg D_E_f3beq;
  reg D_E_f3blt;
  reg D_E_f3bgeu;

  // E->M

  reg [31:0] E_M_rs2_data;

  reg [31:0] E_M_branch_dest;
  reg [4:0]  E_M_rd;

  reg E_M_regwrite, E_M_memtoreg, E_M_jal, E_M_jalr;

  // M->W

  reg [31:0] M_W_MemRdata;

  reg [31:0] M_W_aluout;
  reg [4:0]  M_W_rd;
  
  reg M_W_regwrite, M_W_memtoreg, M_W_jal, M_W_jalr;

  wire [31:0] aluout;
  wire [31:0] jalr_dest;

  wire [31:0] rs1_update_data;
  wire [31:0] rs2_update_data;
 
  assign rs1 = I_D_inst[19:15];
  assign rs2 = I_D_inst[24:20];

  assign funct3  = I_D_inst[14:12];

  assign MemWdata = E_M_rs2_data;

  wire [31:0] help;



  adder_32bit pc_alu   (.a   (rs1_data),
			     			      	.b   (~rs2_data),
							        	.cin (alucontrol[4]),
							        	.sum (help),
							        	.N   (N1flag),
							        	.Z   (Z1flag),
							        	.C   (C1flag),
							        	.V   (V1flag));


  //
  // PC (Program Counter) logic 
  //
  assign f3beq  = (funct3 == 3'b000);
  assign f3blt  = (funct3 == 3'b100);
  assign f3bgeu = (funct3 == 3'b111);
  assign f3bne = (funct3 == 3'b001);


  assign beq_taken  = branch & f3beq & (Z1flag);
  assign blt_taken  = branch & f3blt & (N1flag != V1flag);
  assign bgeu_taken = branch & f3bgeu & C1flag;
  assign bne_taken  = branch & f3bne & (~Z1flag);


//##### start

  wire f3bge,f3bltu;
  wire bge_taken, bltu_taken;

  assign f3bge  = (funct3 == 3'b101);
  assign bge_taken  =  branch & f3bge & (N1flag == V1flag);

  assign f3bltu = (funct3 == 3'b110);
  assign bltu_taken =  branch & f3bltu & ~C1flag;
//##### end
  assign btaken     = beq_taken | bne_taken | blt_taken | bgeu_taken | bge_taken | bltu_taken;

  assign I_D_flush  = btaken | jal | jalr ;
  


  assign branch_dest = (I_D_pc + se_br_imm);
  assign jal_dest = (I_D_pc + se_jal_imm);
  assign jalr_dest = (rs1_data + se_imm_itype);


  always @(posedge clk, posedge reset)
  begin
     if (reset)  pc <= 32'b0;
    else 
    begin
        if (btaken)  // branch_taken
          pc <=  branch_dest;
        else if(jal) // jal
          pc <=  jal_dest;
        else if(jalr) // jalr
          pc <=  jalr_dest;
        else if(Stall)
          pc <=  pc;
        else 
          pc <=  pc + 4;
    end
  end

  //##### end

  //##### start
  // added Stall
  always @(posedge clk)
  begin

    if(I_D_flush)
      begin 
       I_D_pc <= 32'b0; 
       I_D_inst <= 32'b0;
      end
    else if(Stall) 
      begin
        I_D_inst <= I_D_inst; 
        I_D_pc <= I_D_pc;
      end
    else
    begin    
      I_D_inst <=  inst;
      I_D_pc <=  pc;
    end
  end
  //##### end
  
  //##### start stall generating (interlock)
 always @(*)
  begin
    if (D_E_memtoreg &
      ( (D_E_rd == rs1) ||
        (D_E_rd == rs2)))  Stall = 1'b1;
    else                   Stall = 1'b0;
  end
  //##### end 


  //##### start D-> E ff
  always @(posedge clk)
  begin
    if(Stall|D_E_flush) 
      begin

        D_E_regwrite <= 1'b0;
        D_E_memtoreg <= 1'b0;
        D_E_memwrite <= 1'b0;

        D_E_branch   <= 1'b0;

      end
    else
    begin


      D_E_rd <=  I_D_inst[11:7];

      D_E_auipc <=  auipc;
      D_E_lui <=  lui;
      D_E_regwrite <=  regwrite;
      D_E_alusrc <=  alusrc;      
      D_E_memtoreg <=  memtoreg;
      D_E_memwrite <=  memwrite;
      D_E_branch <=  branch;
      D_E_jal <=  jal;
      D_E_jalr <=  jalr;

      D_E_alucontrol <=  alucontrol;

      D_E_rs1_data <=  rs1_data;
      D_E_rs2_data <=  rs2_data;
      
      D_E_pc <=  I_D_pc;
      
      D_E_auipc_lui_imm <=  auipc_lui_imm;
      D_E_se_imm_itype <=  se_imm_itype;
      D_E_se_imm_stype <=  se_imm_stype;
      
      D_E_rs1 <=  rs1;
      D_E_rs2 <=  rs2;

      D_E_f3beq <= f3beq;
      D_E_f3blt <= f3blt;
      D_E_f3bgeu <= f3bgeu;

    end
  end

  // E->M ff
  always @(posedge clk)
  begin

      E_M_pc <=  D_E_pc;

      E_M_rd <=  D_E_rd;

      E_M_rs2_data <=  D_E_rs2_data;
      E_M_aluout <=  aluout;

      E_M_regwrite <=  D_E_regwrite;
      E_M_memtoreg <=  D_E_memtoreg;
      E_M_memwrite <=  D_E_memwrite;

      E_M_jal <=  D_E_jal;
      E_M_jalr <=  D_E_jalr;

  end

  // M-> W ff
  always @(posedge clk)
  begin

      M_W_pc <= E_M_pc;

      M_W_MemRdata <=  MemRdata;
      M_W_aluout <=  E_M_aluout;

      M_W_rd <=  E_M_rd;

      M_W_regwrite <=  E_M_regwrite;
      M_W_memtoreg <=  E_M_memtoreg;

      M_W_jal <=  E_M_jal;
      M_W_jalr <=  E_M_jalr;

  end
  //#####ff ends

  // JAL immediate
  assign jal_imm[20:1] = {I_D_inst[31],I_D_inst[19:12],I_D_inst[20],I_D_inst[30:21]};
  assign se_jal_imm[31:0] = {{11{jal_imm[20]}},jal_imm[20:1],1'b0};

  // Branch immediate
  assign br_imm[12:1] = {I_D_inst[31],I_D_inst[7],I_D_inst[30:25],I_D_inst[11:8]};
  assign se_br_imm[31:0] = {{19{br_imm[12]}},br_imm[12:1],1'b0};

  //##### start data forwarding logics (rs1,rs2 update)


  //##### start
	always@(*)
	begin 
		if	    (M_W_jal)	        rd_data[31:0] = M_W_pc + 4;
		else if (M_W_memtoreg)	  rd_data[31:0] = M_W_MemRdata; 
		else					          	rd_data[31:0] = M_W_aluout; 
	end
  //##### end



  always @(*)
  begin
    if ((D_E_rd != 0)&&(rs1 == D_E_rd) & (~D_E_memwrite))       rs1_data = aluout;
    else if ((E_M_rd != 0)&&(rs1 == E_M_rd) & E_M_memtoreg)     rs1_data = MemRdata[31:0];
    else if ((E_M_rd != 0)&&(rs1 == E_M_rd) & (~E_M_memtoreg))  rs1_data = E_M_aluout[31:0];
    else if ((M_W_rd != 0)&&(rs1 == M_W_rd))                    rs1_data = rd_data[31:0];
    else                                                        rs1_data = rs1_update_data;
  end
  always @(*)
  begin 
    if ((D_E_rd != 0)&&(rs2 == D_E_rd) & (~D_E_memwrite))       rs2_data = aluout; 
    else if ((E_M_rd != 0)&&(rs2 == E_M_rd) & E_M_memtoreg)     rs2_data = MemRdata[31:0];
    else if ((E_M_rd != 0)&&(rs2 == E_M_rd) & (~E_M_memtoreg))  rs2_data = E_M_aluout[31:0];
    else if ((M_W_rd != 0)&&(rs2 == M_W_rd))                    rs2_data = rd_data[31:0];
    else                                                        rs2_data = rs2_update_data;
      
  end
  //##### end 

  // 
  // Register File 
  //
  regfile i_regfile(
    .clk      (clk),
    .we       (M_W_regwrite),
    .rs1      (rs1),
    .rs2      (rs2),
    .rd       (M_W_rd),
    .rd_data  (rd_data),
    .rs1_data (rs1_update_data),
    .rs2_data (rs2_update_data));



  //
  // ALU 
  //
  alu i_alu(
    .a        (alusrc1),
    .b        (alusrc2),
    .alucont  (D_E_alucontrol),
    .result   (aluout),
    .N        (Nflag),
    .Z        (Zflag),
    .C        (Cflag),
    .V        (Vflag));

  
  //##### start data forwarding (alisrc select)

  // alusrc1
  always@(*)
  begin
    if((E_M_rd != 5'b0)&&(E_M_rd == D_E_rs1)&&(E_M_regwrite == 1))      alusrc1[31:0] = E_M_aluout;
    else if((M_W_rd != 5'b0)&&(M_W_rd == D_E_rs1)&&(M_W_regwrite == 1)) alusrc1[31:0] = rd_data;
    else if (D_E_auipc)                                                 alusrc1[31:0] = D_E_pc;
    else if (D_E_lui)                                                   alusrc1[31:0] = 32'b0;
    else                                                                alusrc1[31:0] = D_E_rs1_data[31:0];
  end
  
  // alusrc2
  always@(*)
  begin
    if((E_M_rd != 5'b0)&&(E_M_rd == D_E_rs2)&&(E_M_regwrite == 1)&(~D_E_alusrc))      alusrc2[31:0] = E_M_aluout;
    else if((M_W_rd != 5'b0)&&(M_W_rd == D_E_rs2)&&(M_W_regwrite == 1)&(~D_E_alusrc)) alusrc2[31:0] = rd_data;
    else if (D_E_auipc | D_E_lui)                                                     alusrc2[31:0] = D_E_auipc_lui_imm[31:0];
    else if (D_E_alusrc & D_E_memwrite)                                               alusrc2[31:0] = D_E_se_imm_stype[31:0];
    else if (D_E_alusrc)                                                              alusrc2[31:0] = D_E_se_imm_itype[31:0];
    else                                                                              alusrc2[31:0] = D_E_rs2_data[31:0];
  end
  
  assign se_imm_itype[31:0] = {{20{I_D_inst[31]}},I_D_inst[31:20]};
  assign se_imm_stype[31:0] = {{20{I_D_inst[31]}},I_D_inst[31:25],I_D_inst[11:7]};
  assign auipc_lui_imm[31:0] = {I_D_inst[31:12],12'b0};


endmodule
//##### end

