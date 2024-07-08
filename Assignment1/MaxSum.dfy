method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y && (m == x || m == y) && m == if x > y then x else y
{
  s := x + y;
  if x > y {
    m := x;
  } else {
    m := y;
  }
}

method TestMaxSum()
{
  var s,m := MaxSum(2024, 247);

  assert s == 2271;
  assert m == 2024;
}