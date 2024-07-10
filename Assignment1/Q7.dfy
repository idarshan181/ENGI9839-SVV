// Method to find the maximum of two integers x and y
method Max(x: int, y: int) returns (m: int)
  // Ensures that the result m is either x or y
  ensures m == x || m == y
  // Ensures that the result m is greater than or equal to both x and y
  ensures x <= m && y <= m
{
  // If x is greater than or equal to y, assign m to x
  if x >= y {
    m := x;
  } else {
    // Otherwise, assign m to y
    m := y;
  }
}

// Method to compute the weakest precondition for the call t := Max(2 * u, u + 7)
// with respect to the postcondition t % 2 == 0
method WeakestPrecondition(u: int) returns (pre: bool)
  // Ensures that the precondition correctly reflects the condition under which
  // the postcondition t % 2 == 0 will be true
  ensures pre == (u >= 7 || u % 2 != 0)
{
  // The precondition is true if u is greater than or equal to 7, or if u is odd
  pre := u >= 7 || u % 2 != 0;
}

// Test method to verify the WeakestPrecondition method
method TestWeakestPrecondition() {
  var u: int;
  var result: bool;

  // Test case 1: u < 7 and even
  u := 6;
  result := WeakestPrecondition(u);
  // Precondition should be false because u < 7 and u is even
  assert result == false;

  // Test case 2: u < 7 and odd
  u := 5;
  result := WeakestPrecondition(u);
  // Precondition should be true because u < 7 and u is odd
  assert result == true;

  // Test case 3: u = 7
  u := 7;
  result := WeakestPrecondition(u);
  // Precondition should be true because u is equal to 7
  assert result == true;

  // Test case 4: u > 7
  u := 8;
  result := WeakestPrecondition(u);
  // Precondition should be true because u is greater than 7
  assert result == true;

  // Test case 5: u is a large even number
  u := 10;
  result := WeakestPrecondition(u);
  // Precondition should be true because u is greater than 7
  assert result == true;

  // Test case 6: u is a large odd number
  u := 11;
  result := WeakestPrecondition(u);
  // Precondition should be true because u is greater than 7
  assert result == true;
}