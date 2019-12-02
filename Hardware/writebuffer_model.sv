
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


class FIFO;
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
    
    function int depth();
        return queue1.size();
    endfunction
    
    function void remove();
        if (queue1.size() <= 0)
        begin        
            $error ("ERROR FIFO EMPTY");
        end
        
        queue1.delete(0);

        this.update_regA();
    endfunction

    function logic[31:0] read();
        if (queue1.size() <= 0)
        begin       
            $error ("ERROR FIFO EMPTY");
        end
        return queue1[0][32:0];
    endfunction

    function bit read_parity();
        if (queue1.size() <= 0)
        begin        
            $error ("ERROR FIFO EMPTY");
        end
        return queue1[0][32];
    endfunction
    
    function void parity_error();
        sregA.PEC = sreA.PEC + 1'b1;
    endfunction

    function void reset();
        sregA.PEC = 20'b0; sregA.fifo_75pc = 1'b0; sregA.fifo_50pc = 1'b0; sregA.fifo_25pc = 1'b0; sregA.fifo_depth = 8'b0;
        sregB.cycle_count = 16'b0; sregB.WB_full_count = 16'b0;
    endfunction

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
endclass

module write_buffer
    #(parameter BUFF_SIZE = 16)     // Width of buffer
    (writebuf_if.DUT writebuf_if);

    initial begin
        automatic FIFO F1 = new();
        // Change this 
        F1.FIFO(.size_in(BUFF_SIZE));
        YREQ = 1'b0;
        writebuf_if.HREADY = 1'b0;
    end

    always @(posedge writebuf_if.clk or posedge writebuf_if.rst)
        if(writebuf_if.rst)
        begin
            F1.reset();
        end
        
    always @ (posedge writebuf_if.clk)
        if(writebuf_if.HREADYOUT == 1'b1 && writebuf_if.HREADY == 1'b0 && F1.depth() < BUFF_SIZE)
        begin
            F1.push(writebuf_if.HRDATA, writebuf_if.PARITYSEL);
            writebuf_if.HREADY = 1'b1;
        end
  
    always @ (posedge writebuf_if.clk)
        if(writebuf_if.HREADYOUT == 1'b0 && writebuf_if.HREADY == 1'b1)
        begin
            writebuf_if.HREADY = 1'b0;
        end

    always @ (posedge writebuf_if.clk)
        if (writebuf_if.YREQ == 1'b0 && writebuf_if.YACK == 1'b0 && F1.depth() > 0)
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
        
    always @ (posedge writebuf_if.clk)  
        if (writebuf_if.YREQ == 1'b1 && writebuf_if.YACK == 1'b1)
        begin
            F1.remove();
            writebuf_if.YREQ = 1'b0;
        end
endmodule

        

    




    
    
    
    
