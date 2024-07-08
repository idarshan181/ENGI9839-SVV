
// Method to compute the sum (s) and maximum (m) of two integers x and y.
method MaxSum(x: int, y: int) returns (s: int, m: int)
  // Postcondition: The sum s should be equal to x + y
  ensures s == x + y
  // Postcondition: The maximum m should be the greater of x and y
  ensures m == if x > y then x else y
{
  // Compute the sum of x and y
  s := x + y;
  // Determine the maximum of x and y
  if x > y {
    m := x;
  } else {
    m := y;
  }
}

// Test method to verify the correctness of MaxSum method
// We will pass x = 2024, and y = 247 as the arguments to the MaxSum method
method TestMaxSum()
{
  // Declare variables s and m to hold the results of MaxSum
  var s, m := MaxSum(2024, 247);

  // Assert that the sum is correct (2024 + 247 = 2271 => sum of x + y is 2271)
  assert s == 2271;
  // Assert that the maximum is correct (max(2024, 247) = 2024 => 2024 is greater than 247)
  assert m == 2024;
}

// Method to reconstruct the original integers x and y from their sum s and maximum m.
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  // Precondition: The sum s must be greater than or equal to the maximum m
  requires s >= m && m >= 0
  // Precondition: The difference s - m must be less than or equal to m
  requires s - m <= m
  // Postcondition: m must be equal to either x or y, and x and y should be less than or equal to m
  ensures (m == x || m == y) && x <= m && y <= m
{
  // If the difference s - m is less than or equal to m, set x to m and y to s - m
  if s - m <= m {
    x := m;
    y := s - m;
  } else {
    // Otherwise, set y to m and x to s - m
    y := m;
    x := s - m;
  }

  // Additional assertions to ensure the postconditions are met
  assert s == x + y;
  assert (m == x || m == y) && (x <= m) && (y <= m);
}