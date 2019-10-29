predicate sorted(A:array<int>)
  reads A
{
  true // TODO: write this predicate properly
}

method bubble_sort(A:array<int>)
  ensures sorted(A)
  modifies A
{
  var i := 0;
  while i < A.Length {
    var j := 1;
    while j < A.Length - i {
      if A[j-1] > A[j] {
        A[j-1], A[j] := A[j], A[j-1];
      }
      j := j+1;
    }
    i := i+1;
  }
}

method selection_sort(A:array<int>)
  ensures sorted(A)
  modifies A
{
  var i := 0;
  while i < A.Length {
    var k := i;
    var j := i+1;
    while j < A.Length {
      if A[k] > A[j] {
        k := j;
      }
      j := j+1;
    }
    A[k], A[i] := A[i], A[k];
    i := i + 1;
  }
}

method insertion_sort(A:array<int>)
  ensures sorted(A)
  modifies A
{
  var i := 0;
  while i < A.Length {
    var j := i;
    var tmp := A[j];
    while 1 <= j && tmp < A[j-1] {
      A[j] := A[j-1];
      j := j-1;
    }
    A[j] := tmp;
    i := i+1;
  }
}

method shellsort(A:array<int>)
  modifies A
  ensures sorted(A)
{
  var stride := A.Length / 2;
  while 0 < stride {
    var i := 0;
    while i < A.Length {
      var j := i;
      var tmp := A[j];
      while stride <= j && tmp < A[j-stride] {
        A[j] := A[j-stride];
        j := j-stride;
      }
      A[j] := tmp;
      i := i+1;
    }
    stride := stride / 2;
  }
}

method Main() {
  var A:array<int> := new int[7] [4,0,1,9,7,1,2];
  print "Before: ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
  bubble_sort(A);
  print "After:  ", A[0], A[1], A[2], A[3], 
        A[4], A[5], A[6], "\n";
}