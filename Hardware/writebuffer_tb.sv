// Multiplier testbench


program automatic write_buff_tb
    #(parameter BUFF_SIZE = 16)     // Width of buffer
    (writebuf_if.TEST writebuf_if); 
       
	parameter int buffer_size = BUFF_SIZE;  // maximum value of operand a

  integer test_count;                 // Counter for number of operand pairs to test
 
  class input_values;                   // Declare a class to randomise the operand values
    rand logic [32:0]	i;
    static logic [32:0] test_queue[$];
//        int count = 0;                      // Uncomment these 6 lines to force multiplication of max values every 100th test
//	 constraint c_maxa {(count%100 == 0) -> i==maxa;}
//         constraint c_maxb {(count%100 == 0) -> j==maxb;}
//         function void post_randomize();
//           count++;
//         endfunction
    function void add_input_to_list();
      test_queue.push_back(i);
    endfunction

    function logic [32:0] get_element_i();
      return test_queue[i]
    endfunction
  endclass

  input_values invalues;                   // Instantiate the class

  // covergroup cover_a_values;              // Functional coverage point to check range of operand a values
  //   coverpoint writebuf_if.a {
  //     bins zero = {0};
  //     bins lo   = {[1:7]};
  //     bins med  = {[8:23]};
  //     bins hi   = {[24:30]};
  //     bins max  = {31};
  //   }
  // endgroup

  // covergroup cover_max_vals;              // Functional coverage point to check for multiplication of max values
  //   coverpoint  writebuf_if.ab {
  //     bins max = {maxa*maxb};
  //     bins misc = default;
  //   }
  // endgroup

	initial begin                         // Pulse reset
    writebuf_if.rst = 0;
    #500 
      muwritebuf_ifltif.rst = 1;
	end

	initial begin                         // Initial check of multiplier
		#450
		writebuf_if.cb_out.YACK <= 1;

		writebuf_if.HRDATA = 5;
    writebuf_if.PARITYSEL = 0
		writebuf_if.cb_in.HREADYOUT <= 0;
		wait (HREADY == 1);
    writebuf_if.cb.req <= 0;
		wait (HREADY == 0);

		writebuf_if.cb_out.YACK <= 0;
		wait (YREQ == 1);

		$display ("push and pulled result = %0d, expected result 5", multwritebuf_if.YDATA);
		$display ("push and pulled parity = %0d, expected result 0", multwritebuf_if.YPARITY);
    writebuf_if.cb.YACK <= 1;
		wait (YREQ == 0);
    writebuf_if.cb.req <= 0;
	end

  // initial begin
  //   // cover_a_values cova;              // Instantiate the functional coverage points
  //   // cover_max_vals covmax;
  //   // cova = new();
  //   // covmax = new();
  //   invalues = new();                   // Allocate a random operand values object

  //   for (test_count = 0; test_count < 128;test_count++)
  //   begin
  //     @writebuf_if.cb;
  //     assert (opvals.randomize) else $fatal;
  //     writebuf_if.a=opvals.i;
  //     writebuf_if.b=opvals.j;
  //     cova.sample();                  // Collect coverage of operand a values
  //     writebuf_if.cb.req <= 1;
  //     wait (writebuf_if.done == 1);
  //     covmax.sample();                // Collect coverage of multiplication of maximum values
  //     writebuf_if.cb.req <= 0;
  //   end
  //   @writebuf_if.cb;
  //   $finish;
  // end

endprogram

