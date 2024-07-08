method abs(x: int) returns (y : int)
  ensures  0 <= y
  ensures x >= 0 ==> y == x
{
  if (x < 0) {
    return -x;
  } else {
    return x;
  }
}

/** Call abs */
method foo(x : int)
  requires x >= 0
{
  var y := abs(x);
  assert( y == x);
}