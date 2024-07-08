
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
  var s, m := MaxSum(-2, 0);

  // Assert that the sum is correct (2024 + 247 = 2271 => sum of x + y is 2271)
  assert s == -2;
  // Assert that the maximum is correct (max(2024, 247) = 2024 => 2024 is greater than 247)
  assert m == 0;
}



// Note:  Q2: Consider a method that attempts to reconstruct the arguments x and y from the return values of MaxSum in the previous task.
// In other words, consider a method with the following type signature and
// postcondition: method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int) ensures s == x + y ensures (m == x || m == y) && x <= m && y <= m
// Try to write the body for this method. You will find you cannot. Write an appropriate precondition for the method that allows you to implement the method.

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

// Note: Question 3: Verify that the following program correctly swaps, where ^ denotes xor:
//                x := x ^ y;
//                y := x ^ y;
//                x := x ^ y;
// You can use the commutativity and associativity of xor, as well as the properties x ^ x == 0 and x ^ 0 == x.



method SwapUsingXOR(x: bv32, y: bv32) returns (a: bv32, b: bv32)
  ensures a == (y) && b == (x)
{
  var tempX := x;
  var tempY := y;

  tempX := tempX ^ tempY;
  tempY := tempX ^ tempY;
  tempX := tempX ^ tempY;

  a := tempX;
  b := tempY;
}

method TestSwap()
{
  var x: bv32 := 5;
  var y: bv32 := 10;

  var a, b := SwapUsingXOR(x, y);

  assert a == 10;
  assert b == 5;
}


// method ProveNonNegative(x: int)
// {
//   var y: int;
//   // At this point, x is an uninitialized integer, so it can be any integer value.
//   y := x * x * x * x;
//   // Since x can be any integer value, consider the following cases:
//   // - If x is positive, x * x * x * x is positive.
//   // - If x is zero, x * x * x * x is zero.
//   // - If x is negative, x * x * x * x is positive (negative multiplied an even number of times is positive).
//   // Therefore, 0 <= y holds true in all cases after the assignment.
//   var x := y;
//   assert 0 <= x;
// }

// method TestNonNegative()
// {
//   var x: int := 5;
//   var y: int;
//   y := ProveNonNegative(5);

//   assert a == 10;
//   assert b == 5;
// }
