`include "writebuffer_tb_interface.sv"
`include "writebuffer.v"
`include "writebuffer_model.sv"
`include "writebuffer_randomvalues.sv"

class randon_values;

    rand bit HWRITE;
    rand bit HSEL;
    rand bit [1:0] HTRANS;
    rand bit [2:0] HSIZE;
    rand bit [31:0] HWDATA;
    rand bit [31:0] HADDR;
    rand bit PARTYSEL;
    rand bit HREADY;
    
    rand bit YACK;
    
    constraint input_range{
        HWRITE inside {0,1}; 
        HSEL dist {0:=1, 1:=4};
        HSEL inside {0,1}; HSEL dist {0:=2, 1:=8};
        HTRANS = 1'b1;
        HSIZE = 1'b1;
        HADDER inside {0,1};
        PARITYSEL = 1'b1;
        HREADY = 1'b1;
    
        YACK inside {[0:7]};
        YACK dist {
            [0:0] := 10,
            [1:2] := 50,
            [3:3] := 30,
            [4:5] := 10
        };
    }
endclass

class random_delay;
    
    rand bit [2:0] YACK_DELAY;

    constraint delay{   
        YACK inside {[0:7]};
        YACK dist {
            [0:0] := 10,
            [1:2] := 50,
            [3:3] := 30,
            [4:5] := 10
    }

program automatic write_buffer_tb(
    writebuffer_if.TEST wb_if_model, 
    writebuffer_if.TEST wb_if_dut,
);

    //Reset after 1000ns seconds
	initial begin
		wb_if_model.hRESETn = 0;
        wb_if_dut.hRESETn = 0;
		#1000 wb_if_model.hRESETn = 1;
        #1000 wb_if_dut.hRESETn = 1;
	end

    //Number of random combinations tried

    logic [5:0] count;
    logic [2:0] delay 
    randomvalues randval;
    random_delay randdel;

    //set the inputs of both the model and dut to the same random values and 
    //keep them at those values until the output is read 
    initial begin
        for (count = 0; count < 20; count=count+1) begin
            randval = new()
            
            assert (randval.randomize) else $fatal;
            
            wb_if_model.HWRITE = randval.HWRITE;
            wb_if_model.HSEL = randval.HSEL;
            wb_if_model.HTRANS = randval.HTRANS;
            wb_if_model.HSIZE = randval.HSIZE;
            wb_if_model.HWDATA = randval.HWDATA;
            wb_if_model.HADDR = randval.HADDR;
            wb_if_model.PARTYSEL = randval.PARTYSEL;
            wb_if_model.HREADY = randval.HREADY;

            wb_if_dut.HWRITE = randval.HWRITE;
            wb_if_dut.HSEL = randval.HSEL;
            wb_if_dut.HTRANS = randval.HTRANS;
            wb_if_dut.HSIZE = randval.HSIZE;
            wb_if_dut.HWDATA = randval.HWDATA;
            wb_if_dut.HADDR = randval.HADDR;
            wb_if_dut.PARTYSEL = randval.PARTYSEL;
            wb_if_dut.HREADY = randval.HREADY;
            wait(wb_if_model.YACK == 1'b1 && wb_if_dut.YACK == 1'b1)
        end
        $finish
    end 

    inital begin
        randdel = new();
        @(posedge wb_if_dut.HCLK)
        delay = randdel.delay;

        wb_if_model.YACK = 1'b0;
        wb_if_dut.YACK = 1'b0;
        wait(wb_if_dut.YREQ == 1'b1 && wb_if_model.YREQ == 1'b1)
        #delay
        wb_if_model.YACK = 1'b1;
        wb_if_dut.YACK = 1'b1;
        #1
        wb_if_model.YACK = 1'b0;
        wb_if_dut.YACK = 1'b0;
    end