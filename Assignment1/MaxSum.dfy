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

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires s > m
  ensures s == x + y
  ensures (m == x || m == y) && x <= m && y <= m
{
  x := m;
  y := s - m;

  // Assertions to help the verifier
  assert y >= 0; // Since s > m, y = s - m is non-negative
  assert s == x + y; // x is m and y is s - m, so s == x + y
  assert m == x || m == y; // m is assigned to x
  assert x <= m; // x is m
  assert y <= m;
}