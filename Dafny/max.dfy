predicate contains(A:array<int>, v:int)
  reads A
{
  contains_upto(A, A.Length, v)
}

predicate contains_upto(A:array<int>, hi:int, v:int)
  requires hi <= A.Length
  reads A
{
  exists j :: 0 <= j < hi && v == A[j]
}

method maxarray (A:array<int>) returns (r:int)
  requires 0 < A.Length
  ensures contains(A,r)
  ensures forall j :: 0 <= j < A.Length ==> r >= A[j]
{
  r := A[0];
  var i := 1;
  while i < A.Length 
    invariant 1 <= i <= A.Length
    invariant contains_upto(A,i,r)
    invariant forall j :: 0 <= j < i ==> r >= A[j]
    decreases A.Length - i
  {
    if r < A[i] {
      r := A[i];
    }
    i := i+1;
  }
}















method max(x:int, y:int) returns (r:int)
  ensures r >= x 
  ensures r >= y
  ensures r == x || r == y
{
  if x < y {
    return y;
  } else {
    return x;
  }
}

method Main() {
  var m:int := max(3,5);
  print m, "\n";
}