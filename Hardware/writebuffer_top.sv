interface wirtebuf_if(
    input bit clk
    );

  logic rst, YREQ, YACK, PARITYSEL, YPARITY, HREADYOUT, HREADY;
  logic [31:0] HRDATA, YDATA;


  clocking cb @(posedge clk);
    input YREQ, PARITYSEL, HREADYOUT;
    output YACK, HREADY;
  endclocking
  
  modport DUT (input clk, YACK, PARITYSEL, HREADYOUT, HRDATA, output YREQ, YPARITY, HREADY, YDATA);
                
endinterface


module writebuffer_top();
    bit clk;

    initial begin 
        clk = 0;
        forever #100 clk = ! clk;
    end

writebuf_if writebufif(clk);
write_buffer WB (writebuf_if);

endmodule