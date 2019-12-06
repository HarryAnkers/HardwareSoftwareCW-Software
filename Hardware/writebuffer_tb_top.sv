`include "writebuffer_tb_interface.sv"
`include "writebuffer.v"
`include "writebuffer_model.sv"

module write_buffer_testbench_top;

    bit clk

    wire CLK_DUT
    wire RESET_DUT
    wire HREADYOUT_DUT
    wire [31:0] HRDATA_DUT
    wire [31:0] YDATA_DUT
    wire YPARITY_DUT
    wire YREQ_DUT
    initial begin                
        clk = 0;
        forever #100 clk = ! clk;
	end

//check all signals from both the model and dut are the same
initial begin
  assert(wb_if_dut.HRESET == wb_if_model.HRESET)
    else $error ("HRESET:", wb_if_dut.HRESET, wb_if_model.HRESET);
 
  assert(wb_if_dut.HWRITE == wb_if_model.HWRITE)
    else $error ("HWRITE:", wb_if_dut.HWRITE, wb_if_model.HWRITE);
 
  assert(wb_if_dut.HSEL == wb_if_model.HSEL)
    else $error ("HSEL:", wb_if_dut.HSEL, wb_if_model.HSEL);

  assert(wb_if_dut.HTRANS == wb_if_model.HTRANS)
    else $error ("HTRANS:", wb_if_dut.HTRANS, wb_if_model.HTRANS);

  assert(wb_if_dut.HSIZE == wb_if_model.HSIZE)
    else $error ("HSIZE:", wb_if_dut.HSIZE, wb_if_model.HSIZE);

  assert(wb_if_dut.HWDATA == wb_if_model.HWDATA)
    else $error ("HWDATA:", wb_if_dut.HWDATA, wb_if_model.HWDATA);

  assert(wb_if_dut.HADDR == wb_if_model.HADDR)
    else $error ("HADDR:", wb_if_dut.HADDR, wb_if_model.HADDR);

  assert(wb_if_dut.YACK == wb_if_model.YACK)
    else $error ("YACK:", wb_if_dut.YACK, wb_if_model.YACK);

  assert(wb_if_dut.PARTYSEL == wb_if_model.PARTYSEL)
    else $error ("PARTYSEL:", wb_if_dut.PARTYSEL, wb_if_model.PARTYSEL);

  assert(wb_if_dut.HREADY == wb_if_model.HREADY)
    else $error ("HREADY:", wb_if_dut.HREADY, wb_if_model.HREADY);

  assert(wb_if_dut.HREADYOUT == wb_if_model.HREADYOUT)
    else $error ("HREADYOUT:", wb_if_dut.HREADYOUT, wb_if_model.HREADYOUT);

  assert(wb_if_dut.YPARITY == wb_if_model.YPARITY)
    else $error ("YPARITY:", wb_if_dut.YPARITY, wb_if_model.YPARITY);

  assert(wb_if_dut.YREQ == wb_if_model.YREQ)
    else $error ("YREQ:", wb_if_dut.YREQ, wb_if_model.YREQ);

  assert(wb_if_dut.YDATA == wb_if_model.YDATA)
    else $error ("YDATA:", wb_if_dut.YDATA, wb_if_model.YDATA);

  assert(wb_if_dut.HRDATA == wb_if_model.HRDATA)
    else $error ("HRDATA:", wb_if_dut.HRDATA, wb_if_model.HRDATA);
end

//create two instanes of the interface, one to be used by the model and one by the test bench
//check the outputs and inputs are equal 
writebuffer_if wb_if_model(clk);

writebuffer_if wb_if_dut(clk);

writebuffer_testbench wb_tb(wb_if_model, wb_if_dut);

write_buffer_model wb_model(wb_if_model);

writebuffer dut(
  clk,
  wb_if_dut.HRESET,
  wb_if_dut.HWRITE,
  wb_if_dut.HSEL,
  wb_if_dut.HTRANS,
  wb_if_dut.HSIZE,
  wb_if_dut.HWDATA,
  wb_if_dut.HADDR,
  wb_if_dut.YACK,
  wb_if_dut.PARTYSEL,
  wb_if_dut.HREADY,

  wb_if_dut.HREADYOUT,
  wb_if_dut.YPARITY,
  wb_if_dut.YREQ,
  wb_if_dut.YDATA,
  wb_if_dut.HRDATA
);
