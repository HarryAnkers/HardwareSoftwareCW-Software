interface wirtebuf_if( input bit clk );

  logic rst, YREQ, YACK, PARITYSEL, YPARITY, HREADYOUT, HREADY;
  logic [31:0] HRDATA, YDATA;


  clocking cb_in @(posedge clk);
    input HREADY;
    output HREADYOUT;
  endclocking

  clocking cb_out @(posedge clk);
    input YREQ;
    output YACK;
  endclocking
  
  modport DUT (input clk, rst, YACK, PARITYSEL, HREADYOUT, HRDATA, output YREQ, YPARITY, HREADY, YDATA);
  modport TEST (input cb_in, cb_out, HRDATA, output rst, PARITYSEL, YPARITY, YDATA);
                
endinterface


module writebuffer_top();
    bit clk;

    initial begin 
        clk = 0;
        forever #100 clk = ! clk;
    end

writebuf_if writebufif(clk);
write_buffer WB (writebuf_if);
write_buffer_TB WB_TB (writebuf_if);

endmodule