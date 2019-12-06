interface writebuffer_if(input bit HCLK);
    logic HRESETn;
    logic HWRITE;
    logic HSEL;
    logic [1:0] HTRANS;
    logic [2:0] HSIZE;
    logic [31:0] HWDATA;
    logic [31:0] HADDR;
    logic YACK;
    logic PARTYSEL;
    logic HREADY;

    logic HREADYOUT;
    logic YPARITY;
    logic YREQ;
    logic [31:0] YDATA;
    logic [31:0] HRDATA;

    clocking cb @(posedge HCLK);
	endclocking

//Inputs to writebuffer are outputs of the test bench
modport TESTBENCH(
    clocking cb
    output HRESETn,
    output HWRITE,
    output HSEL,
    output HTRANS,
    output HSIZE,
    output HWDATA,
    output HADDR,
    output YACK,
    output PARTYSEL,
    output HREADY,
    //
    input HREADYOUT,
    input YPARITY,
    input YREQ,
    input YDATA,
    input HRDATA
);

modport DUT(
    output HCLK
    output HRESETn,
    output HWRITE,
    output HSEL,
    output HTRANS,
    output HSIZE,
    output HWDATA,
    output HADDR,
    output YACK,
    output PARTYSEL,
    output HREADY,
    //
    input HREADYOUT,
    input YPARITY,
    input YREQ,
    input YDATA,
    input HRDATA
);

endinterface
