
//Write Buffer Built as FIFO


module writebuffer #(AWIDTH=4)
//AWIDTH is the address width to address the fifo so 4 gives 16 entries, 
//5 give 32 entries, 6 gives 64 entries and 7 give 128
(
  input wire HCLK,
  input wire HRESETn,
  input wire HWRITE,
  input wire HSEL,
  input [1:0] HTRANS,
  input [2:0] HSIZE,
  input wire [31:0] HWDATA,
  input [31:0] HADDR,
  input wire YACK,
  input wire PARTYSEL,
  input wire HREADY,

  output wire HREADYOUT,
  output wire YPARITY,
  output wire YREQ,
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
  
  //Status Register A split in to parts and merged together when requested
  reg [20:0] Parity_error
  reg fifo_75pc,
  reg fifo_50pc,
  reg fifo_25pc, 
  reg [7:0] fifo_depth

  //Status Register B split in to parts
  reg [15:0] Cycle_count
  reg [15:0] WB_cycle_count

  reg full_reg;
  reg empty_reg;
  reg full_next;
  
  reg empty_next;
  
  wire w_en;
  wire parity;
  wire parity_check;
  wire parity_out;

  always @ (posedge HCLK)
    begin
    if(w_en)
    begin
    //Calculate the parity bit and concant it to the input data
      parity = ^HWDATA;

      parity = parity ~^ PARTYSEL;

      array_reg[w_ptr_reg] <= {parity, HWDATA};
    end
    end

//set the data on the bus to the Y-port to the next item in the fifo and find the parity bit stored with this data entry 
  assign YDATA = array_reg[r_ptr_reg][31:0];   
   
  assign parity_out = array_reg[r_ptr_reg][32];

//When the AHBLITE interface doesn't want to read and the register is not full then allow it the write to the next free space
// Can only write with this combination of signals to ensure the bus is not being used 
  assign w_en = HWRITE & ~full_reg & HSEL & HREADY;             

  always @ (posedge HCLK)
    begin
    //if HWRITE is low and the address being read is 0 then assign the outdata to the AHBLITE interface as
    //status register A
    if(!HADDR[0] && !HWRITE)
    begin
    //FIFO depth will be equal in value to the write pointer as this starts at 0 and incremnets
    //on each write
     fifo_depth <= w_ptr_reg;
     HRDATA = {Parity_error, fifo_75pc, fifo_50pc, fifo_25pc, fifo_depth};
    end
    //If the address is 1 then assign it to status register B
    if(HADDR[0] && !HWRITE)
    begin
     HRDATA = {Cycle_count, WB_cycle_count};
    end
    end

//State Machine
  always @ (posedge HCLK, negedge HRESETn)
  begin
    if(!HRESETn)
      begin
        //Set all paramters back to 0
        w_ptr_reg <= 0;
        r_ptr_reg <= 0;
        full_reg <= 1'b0;
        empty_reg <= 1'b1;
        Parity_error <= 20'b0;
        fifo_75pc <= 1'b0;
        fifo_50pc <= 1'b0;
        fifo_25pc <= 1'b0;
        Cycle_count <= 16'b0;
        WB_cycle_count <= 16'b0;
      end
    else
      begin
        w_ptr_reg <= w_ptr_next;
        r_ptr_reg <= r_ptr_next;
        full_reg <= full_next;
        empty_reg <= empty_next;
      end
  end

//Update the status registers increaseing the counts
 always @ (posedge HCLK)
 begin
    Cycle_count = Cycle_count + 1;

    //If the buffer is full set HREADYOUT to high otherwise 
    if(full_reg)
    begin
        HREADYOUT = 1'b0
        WB_cycle_count = WB_cycle_count + 1;
    end
    else
    begin
        HREADYOUT = 1'b1
    end

    //set YREQ to high if the YACK is not asserted and the fifo is not empty 
    if(!empty_reg)
    begin
        YREQ = ~YACK;
    end
    else
    begin
        YREQ = 1'b0;
    end 
    //Calculate the parity and set YPARITY to high if it is incorrect 
    parity_check = ^YDATA;

    parity_check = parity_check ~^ PARTYSEL;

    if(parity_check != parity_out)
    begin   
        YPARITY = 1'b1;
    end
    else
    begin
        YPARITY = 1'b0;
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
  //set the next pointers
    w_ptr_succ = w_ptr_reg + 1;
    r_ptr_succ = r_ptr_reg + 1;

    w_ptr_next = w_ptr_reg;
    r_ptr_next = r_ptr_reg;
    full_next = full_reg;
    empty_next = empty_reg;

    //When YACK is high we can increment the pointer to the next input to the FIFO as the previous has been read, setting the YDATA output bus to the next
    //item in the FIFO 
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
            //Only Update parity_error once for a given data item that has error by one
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

 
 

  
