
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


class FIFO:
    logic [32:0] queue1[$];
    logic [7:0] size;
    statusregisterA sregA;
    statusregisterB sregB;

    function new(input logic [7:0] size_in=16, odd_in=1);
        size=size_in
        this.reset()
    endfunction

    function push(input logic [31:0] data_in, odd);
        if queue1.size() >= size:        
            $error ('ERROR FIFO FULL')
        if(data_in[0] == odd);
            queue1.push_back(1'b1,data_in)
        else;
            queue1.push_back(1'b0,data_in)
        this.update_regA()
    endfunction
    
    function depth();
        return queue1.size()
    
    function remove();
        if queue1.size() <= 0:        
            $error ('ERROR FIFO EMPTY')

        queue1.pop_front() 

        this.update_regA()
    endfunction

    function read();
        if queue1.size() <= 0:        
            $error ('ERROR FIFO EMPTY')

        return queue1[31:0]
    endfunction

    function read_parity();
        if queue1.size() <= 0:        
            $error ('ERROR FIFO EMPTY')
        return queue1[32]
    endfunction
    
    function parity_error();
        sregA.PEC = sreA.PEC + 1'b1
    endfunction

    function reset();
        sregA.PEC = 20'b0; sregA.fifo_75pc = 1'b0; sregA.fifo_50pc = 1'b0; sregA.fifo_25pc = 1'b0; sregA.fifo_depth = 8'b0;
        sregB.cycle_count = 16'b0; sregB.WB_full_count = 16'b0;
    endfunction

    function update_regA();
        if queue1.size >= 0.25*size:
            sregA.fifo_25pc = 1;

        if queue1.size >= 0.5*size:
            sregA.fifo_50pc = 1;
    
    
        if queue1.size >= 0.75*size:
            sregA.fifo_75pc = 1;
    
        sregA.fifo_depth = queue1.size()
    endfunction

module write_buffer(
    input logic clk,
    input logic rst,
    input logic [31:0] HRDATA,
    output logic [31:0] data_out,
    input bit YACK,
    output bit YREQ,
    input bit PARITYSEL,
    output bit YPARITY
    input bit HREADYOUT
    output bit HREADY
    );
    

    initial begin
        FIFO F1;
        F1 = new(.size_in(16);
    end
    
    assign YREQ = 1'b0
    assign rst = 1'b0

    always @(posedge clk or posedge rst_n)
        if(rst)
            F1.reset()

    always @ (posedge clk)
        if(HREADYOUT == 1'b1 && HREADY == 1'b0)
            F1.push(HRDATA, PARITYSEL)
            HREADY = 1'b1

        if(HREADYOUT == 1'b0)
            HREADY = 1'b0


    always @ (posedge clk)
        if (F1.depth() > 0 && YREQ == 1'b0 && YACK == 1'b0);
            Pdata_out = F1.read()
            YPARITY = F1.read_parity()

            if(data_out[0] == PARITYSEL);
                if(YPARITY!=1'b1);
                    F1.parity_error()
            else;
                if(YPARITY!=1'b0);
                    F1.parity_error()

            YREQ = 1'b1

        if (YREQ == 1'b1 && YACK == 1'b1);
            F1.remove()
            YREQ = 1'b0

endmodule

        

    




    
    
    
    
