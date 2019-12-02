
//Write Buffer Built as FIFO


module FIFO #(AWIDTH=4)
//AWIDTH is the address width to address the fifo so 4 gives 16 entries, 
//5 give 32 entries, 6 gives 64 entries and 7 give 128
(
  input wire clk,
  input wire HRESETn,
  input wire HWRITE,
  input HSEL,
  input [1:0] HTRANS,
  input [2:0] HSIZE,
  input wire [31:0] HWDATA,
  input [31:0] HADDR,
  input wire YACK,
  input wire PARTYSEL,

  output wire YPARITY,
  output wire YREQ,
  output wire empty,
  output wire full,
  output wire [31:0] YDATA,
  output wire [31:0] HRDATA
);

//Internal Signal declarations

  reg [32:0] array_reg [2**AWIDTH-1:0];
  reg [AWIDTH-1:0] w_ptr_reg;
  reg [AWIDTH-1:0] w_ptr_next;
  reg [AWIDTH-1:0] w_ptr_succ;
  reg [AWIDTH-1:0] r_ptr_reg;
  reg [AWIDTH-1:0] r_ptr_next;
  reg [AWIDTH-1:0] r_ptr_succ;

  //Status all parts of status registers A and B as internal registers
  // Then concant them before sending the AHBLITE interface
  
  //Status Register A
  reg [20:0] Parity_error
  reg fifo_75pc,
  reg fifo_50pc,
  reg fifo_25pc, 
  reg [7:0] fifo_depth

//Status Register B
  reg [15:0] Cycle_count
  reg [15:0] WB_cycle_count

  //rd as a wire 
  wire rd,

  reg full_reg;
  reg empty_reg;
  reg full_next;
  
  reg empty_next;
  
  wire w_en;
  wire parity;
  wire parity_check;
  wire parity_out;

  always @ (posedge clk)
    if(w_en)
    begin
    //Calculate the parity bit and concant it to the input data
      parity = ^HWDATA;

      parity = parity & PARTYSEL

      array_reg[w_ptr_reg] <= {parity, HWDATA};
    end

  assign YDATA = array_reg[r_ptr_reg][31:0];   
   
  assign parity_out = array_reg[r_ptr_reg][32];

  assign w_en = HWRITE & ~full_reg;           


  //set rd to high when YACK goes low so that 
  

  always @ (posedge clk)
    begin
    //if HWRITE is low and the address being read is 0 then assign the outdata to the AHBLITE interface as
    //status register A
    if(!HADDR[0] && !HWRITE)
    begin
    //FIFO depth will be equal in value to the write pointer as this starts at 0 and incremnets
    //on each write
     fifo_depth <= w_ptr_reg
     HRDATA = {Parity_error, fifo_75pc, fifo_50pc, fifo_25pc, fifo_depth}
    end
    //If the address is 1 then assign it to status register B
    if(HADDR[0] && !HWRITE)
    begin
     HRDATA = {Cycle_count, WB_cycle_count}
    end
    end

//State Machine
  always @ (posedge clk, negedge HRESETn)
  begin
    if(!HRESETn)
      begin
        w_ptr_reg <= 0;
        r_ptr_reg <= 0;
        full_reg <= 1'b0;
        empty_reg <= 1'b1;
        Parity_error <= 20'b0'
        fifo_75pc <= 1'b0,
        fifo_50pc <= 1'b0,
        fifo_25pc <= 1'b0,
        Cycle_count <= 16'b0,
        WB_cycle_count <= 16'b0
      end
    else
      begin
        w_ptr_reg <= w_ptr_next;
        r_ptr_reg <= r_ptr_next;
        full_reg <= full_next;
        empty_reg <= empty_next;
      end
  end

//Update the status registers
 always @ (posedge clk)
 begin
    Cycle_count = Cycle_count + 1;

    if(full_reg)
    begin
        WB_cycle_count = WB_cycle_count + 1;
    end

    if(!empty_reg)
    begin
        YREQ = ~YACK
    end
    else
    begin
        YREQ = 1'b0
    end 
    //Calculate the parity and set YPARITY to high if it is incorrect 
    parity_check = ^YDATA;

    parity_check = parity_check & PARTYSEL;

    if(parity_check != parity_out)
    begin   
        YPARITY = 1'b1
    end
    else
    begin
        YPARITY = 1'b0
    end

end

//Set status register A percentage full to by using the 2 MSBs of the write pointer
case({w_ptr_reg[AWIDTH],w_ptr_reg[AWIDTH-1]})
    2'b00:
        fifo_75pc <= 1'b0;
        fifo_50pc <= 1'b0;
        fifo_25pc <= 1'b0;
    2'b01:
        fifo_75pc <= 1'b0;
        fifo_50pc <= 1'b0;
        fifo_25pc <= 1'b1;
    2'b10:
        fifo_75pc <= 1'b0;
        fifo_50pc <= 1'b1;
        fifo_25pc <= 1'b1;
    2'b11:
        fifo_75pc <= 1'b1;
        fifo_50pc <= 1'b1;
        fifo_25pc <= 1'b1;
 end

//Next State Logic
  always @*
  begin
    w_ptr_succ = w_ptr_reg + 1;
    r_ptr_succ = r_ptr_reg + 1;

    w_ptr_next = w_ptr_reg;
    r_ptr_next = r_ptr_reg;
    full_next = full_reg;
    empty_next = empty_reg;

    //When YACK is high we can increment the pointer to the next input to the FIFO as the previous has been read 
    case({w_en,YACK})
      //2'b00: nop
      2'b01:
        if(~empty_reg)
          begin
            r_ptr_next = r_ptr_succ;
            full_next = 1'b0;
            if (r_ptr_succ == w_ptr_reg)
              empty_next = 1'b1;
          end
        if(YPARITY)
            begin
            //Only Update parity_error once for a given data that has error by only
            //Updating before the pointer is incremented 
            Parity_error = Parity_error + 1;
            end 
      2'b10:
        if(~full_reg)
          begin
            w_ptr_next = w_ptr_succ;
            empty_next = 1'b0;
            if (w_ptr_succ == r_ptr_reg)
              full_next = 1'b1;
          end
      2'b11:
        begin
          w_ptr_next = w_ptr_succ;
          r_ptr_next = r_ptr_succ;
          if(YPARITY)
            begin
            Parity_error = Parity_error + 1;
            end
        end
    endcase
  end

//Set Full and Empty

  assign full = full_reg;
  assign empty = empty_reg;
  
endmodule

 
 

  
