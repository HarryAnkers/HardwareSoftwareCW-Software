
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
    logic [32:0] queue1[$];
    logic [7:0] size;
    statusregisterA sregA;
    statusregisterB sregB;

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

module write_buffer(
    input logic clk,
    input logic rst,
    input logic [31:0] HRDATA,
    input bit HREADYOUT,
    input bit YACK,
    input bit PARITYSEL,
    
    output bit YPARITY,
    output bit HREADY,
    output bit YREQ,
    output logic [31:0] data_out
    );

    initial begin
        automatic FIFO F1 = new();
        F1.FIFO(.size_in(16));
        YREQ = 1'b0;
        HREADY = 1'b0;
    end

    always @(posedge clk or posedge rst)
        if(rst)
        begin
            F1.reset();
        end
        
    always @ (posedge clk)
        if(HREADYOUT == 1'b1 && HREADY == 1'b0)
        begin
            F1.push(HRDATA, PARITYSEL);
            HREADY = 1'b1;
        end
  
    always @ (posedge clk)
        if(HREADYOUT == 1'b0 && HREADY == 1'b1)
        begin
            HREADY = 1'b0;
        end

    always @ (posedge clk)
        if (F1.depth() > 0 && YREQ == 1'b0 && YACK == 1'b0)
        begin
            data_out = F1.read();
            YPARITY = F1.read_parity();

            if(data_out[0] == PARITYSEL)
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
            YREQ = 1'b1;
        end
        
    always @ (posedge clk)  
        if (YREQ == 1'b1 && YACK == 1'b1)
        begin
            F1.remove();
            YREQ = 1'b0;
        end
endmodule

        

    




    
    
    
    
