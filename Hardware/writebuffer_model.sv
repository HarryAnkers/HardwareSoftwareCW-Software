`include "writebuffer_tb_interface.sv"


//Set status registers as packed variables
typedef struct packed{
    logic [10:0] PEC;
    logic fifo_75pc;
    logic fifo_50pc;
    logic fifo_25pc;
    logic [7:0] fifo_depth;  
} statusregisterA;

typedef struct packed{
    logic [15:0] cycle_count;
    logic [15:0] WB_full_count;
} statusregisterB;


//Create a Class of the fifo with the properties we require
class FIFO;
//Model fifo around a queue
    static logic [32:0] queue1[$];
    static logic [7:0] size;
    static statusregisterA sregA;
    static statusregisterB sregB;

    function void FIFO(input logic [7:0] size_in=16, odd_in=1);
        size=size_in;
        this.reset();
    endfunction

    function void push(input logic [31:0] data_in, odd);
        if (queue1.size() >= this.size)
        begin       
            $error ("ERROR FIFO FULL");
        end
        if(data_in[0] == odd)
        begin
            queue1.push_back({1'b1,data_in});
        end
        else
        begin
            queue1.push_back({1'b0,data_in});
        end
        this.update_regA();
    endfunction
    
    //return number of items in fifo
    function int depth();
        return queue1.size();
    endfunction
    

    //remove item from fifo
    function void remove();
        if (queue1.size() <= 0)
        begin        
            $error ("ERROR FIFO EMPTY");
        end
        
        queue1.delete(0);

        this.update_regA();
    endfunction

    //return item from fifo
    function logic[31:0] read();
        if (queue1.size() <= 0)
        begin       
            $error ("ERROR FIFO EMPTY");
        end
        return queue1[0][32:0];
    endfunction

    //return the parity bit from the current data 
    function bit read_parity();
        if (queue1.size() <= 0)
        begin        
            $error ("ERROR FIFO EMPTY");
        end
        return queue1[0][32];
    endfunction
    
    //increade the parity errror count
    function void parity_error();
        sregA.PEC = sreA.PEC + 1'b1;
    endfunction

    //reset status registers
    function void reset();
        sregA.PEC = 20'b0; sregA.fifo_75pc = 1'b0; sregA.fifo_50pc = 1'b0; sregA.fifo_25pc = 1'b0; sregA.fifo_depth = 8'b0;
        sregB.cycle_count = 16'b0; sregB.WB_full_count = 16'b0;
    endfunction

    //Update all parts of status regifer A
    function void update_regA();
        if (queue1.size >= 0.25*size)
        begin
            sregA.fifo_25pc = 1;
        end
        if (queue1.size >= 0.5*size)
        begin
            sregA.fifo_50pc = 1;
        end
    
        if (queue1.size >= 0.75*size)
        begin
            sregA.fifo_75pc = 1;
        end
        sregA.fifo_depth = queue1.size();
    endfunction

    function void update_regB();
        sregB.cycle_count =  sregB.cycle_count + 1;
        if (queue1.size = size)
        begin
            sregB.WB_full_count = sregB.WB_full_count + 1;
        end
    endfunction
endclass



module write_buffer_model
    #(parameter BUFF_SIZE = 16)     // Width of buffer
    (writebuffer_if.DUT writebuf_if);

    initial begin
        automatic FIFO F1 = new();
        // Change this 
        F1.FIFO(.size_in(BUFF_SIZE));
        YREQ = 1'b0;
        writebuf_if.HREADY = 1'b0;
    end

    //If reset is high set everything back to 0
    always @(posedge writebuf_if.clk or posedge writebuf_if.rst)
        if(writebuf_if.rst)
        begin
            F1.reset();
        end

    //If the correct combination of signals are high then write the data to fifo    
    always @ (posedge writebuf_if.clk)
        if(writebuf_if.HREADY == 1'b1 && writebuf_if.HSEL == 1'b1 && F1.depth() < BUFF_SIZE &&  writebuf_if.HWRITE == 1'b1)
        begin
            F1.push(writebuf_if.HRDATA, writebuf_if.PARITYSEL);
        end

    //Put the next item from the fifo on the ouput bus until it is confirmed read 
    always @ (posedge writebuf_if.clk)
        if (writebuf_if.YACK == 1'b0 && F1.depth() > 0)
        begin
            writebuf_if.data_out = F1.read();
            YPARITY = F1.read_parity();

            if(writebuf_if.data_out[0] == writebuf_if.PARITYSEL)
            begin
                if(YPARITY!=1'b1)
                begin
                    F1.parity_error();
                end
            end
            else
            begin
                if(YPARITY!=1'b0)
                begin
                    F1.parity_error();
                end
            end
            writebuf_if.YREQ = 1'b1;
        end
        //if YACK goes high then remove the item from the FIFO
    always @ (posedge writebuf_if.clk)  
        if (writebuf_if.YACK == 1'b1)
        begin
            F1.remove();
            writebuf_if.YREQ = 1'b0;
        end

    //update the cycle count 
    always @ (posedge writebuf_if.clk)
    begin    
        F1.update_regB(); 
        if(F1.depth() == BUFF_SIZE)
            writebuf_if.HREADYOUT = 1'b0
        else
            writebuf_if.HREADYOUT = 1'b1

    //Depending on the address set the value of HRDATA to the value of status register A or B
    always @ (posedge writebuf_if.clk)
    begin
        if (writebuf_if.HADDR[0] == 1'b0 &&  writebuf_if.HWRITE == 1'b0)
        begin
             writebuf_if.HRDATA = F1.sregB
        end

        if (writebuf_if.HADDR[0] == 1'b1 &&  writebuf_if.HWRITE == 1'b1)
        begin
             writebuf_if.HRDATA = F1.sregA
        end
    end
endmodule

        

    




    
    
    
    
