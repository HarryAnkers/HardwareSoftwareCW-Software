predicate sorted(A: array?<int>, l: int)
  reads A
  requires A != null
  {
    forall i, j :: 0 <= l <= i <= j < A.Length ==> A[i] <= A[j]
  }
  
predicate partition(A: array?<int>, i: int)
  reads A
  requires A != null
  {
    forall k, k' :: 0 <= k <= i < k' < A.Length ==> A[k] <= A[k']
  }

method BubbleSort(A: array?<int>)
  modifies A
  requires A != null
  requires A.Length>0
  ensures sorted(A, 0)
  {
    var i := A.Length - 1;
    while(i > 0)
      invariant i < 0 ==> A.Length == 0
      invariant sorted(A, i)
      invariant partition(A, i)
      decreases i
      {
        var j := 0;
        while (j < i)
          invariant 0 < i < A.Length && 0 <= j <= i
          invariant sorted(A, i)
          invariant partition(A, i)
          invariant forall k :: 0 <= k <= j ==> A[k] <= A[j]
          decreases i-j
          {
            if(A[j] >  A[j+1])
              {
                A[j], A[j+1] := A[j+1], A[j];
              }
              j := j + 1;
          }
          i := i -1;
      }
  }
method Main() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 9, 4, 6, 3, 8;
  BubbleSort(a);
  var k := 0;
  while(k < 5) { print a[k], "\n"; k := k+1;}
}