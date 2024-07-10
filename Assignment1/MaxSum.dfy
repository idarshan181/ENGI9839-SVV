
// Method to compute the sum (s) and maximum (m) of two integers x and y.
method MaxSum(x: int, y: int) returns (s: int, m: int)
  // Postcondition: The sum s should be equal to x + y
  ensures s == x + y
  ensures m == x || m == y
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
  ensures s == x + y
  ensures (m == x || m == y) && x <= m && y <= m
{
  // Assign x to be the maximum m, and y to be the difference s - m.
  // This ensures that x + y equals s, and one of the variables is the maximum m.
  x, y := m, s - m;

  // Additional assertions to ensure the postconditions are met
  // Check that the sum of x and y equals s
  assert s == x + y;
  // Check that m is either x or y, and both x and y are less than or equal to m
  assert (m == x || m == y) && (x <= m) && (y <= m);
}

// Note: Question 3: Verify that the following program correctly swaps, where ^ denotes xor:
//                x := x ^ y;
//                y := x ^ y;
//                x := x ^ y;
// You can use the commutativity and associativity of xor, as well as the properties x ^ x == 0 and x ^ 0 == x.



// Method to swap two bv32 (bit-vector of 32 bits) integers using XOR operation
method SwapUsingXOR(x: bv32, y: bv32) returns (a: bv32, b: bv32)
  // Ensures that the values are swapped: the returned 'a' should be 'y' and 'b' should be 'x'
  ensures a == y && b == x
{
  // Initialize 'a' with 'x' and 'b' with 'y'
  a := x;
  b := y;

  // Perform the XOR swap algorithm
  a := a ^ b; // Step 1: a becomes x XOR y
  b := a ^ b; // Step 2: b becomes (x XOR y) XOR y, which simplifies to x
  a := a ^ b; // Step 3: a becomes (x XOR y) XOR x, which simplifies to y
}

// Test method to verify the SwapUsingXOR method
method TestSwap()
{
  // Initialize two bv32 integers
  var x: bv32 := 5;
  var y: bv32 := 10;

  // Call SwapUsingXOR and get the swapped values
  var a, b := SwapUsingXOR(x, y);

  // Assert that the values are correctly swapped
  assert a == 10;
  assert b == 5;
}


// Method to prove that the fourth power of an integer is non-negative
method ProveNonNegative(x: int) returns (y: int)
  // Ensures that the result y is non-negative
  ensures 0 <= y
  // Ensures that the result y is equal to x * x * x * x
  ensures y == x * x * x * x
{
  // Calculate the fourth power of x and assign it to y
  y := x * x * x * x;
  // Since x can be any integer value, consider the following cases:
  // - If x is positive, x * x * x * x is positive.
  // - If x is zero, x * x * x * x is zero.
  // - If x is negative, x * x * x * x is positive (negative multiplied an even number of times is positive).
  // Therefore, 0 <= y holds true in all cases after the assignment.
  assert 0 <= y;
}

// Test method to verify the ProveNonNegative method
method TestNonNegative()
{
  // Test with a positive integer
  var x: int := 5;
  var y: int := ProveNonNegative(x);
  // Assert that the result is non-negative
  assert y >= 0;

  // Test with a negative integer
  x := -2;
  y := ProveNonNegative(x);
  // Assert that the result is non-negative
  assert y >= 0;

  // Test with zero
  x := 0;
  y := ProveNonNegative(x);
  // Assert that the result is non-negative
  assert y >= 0;
}


// Method that returns a value based on the input x with a strong postcondition
method StrongPostCondition(x: int) returns (y: int)
  // Precondition: x must be less than 88
  requires x < 88
  // Postcondition: y should be 7 if x is less than 14, otherwise y should be 5
  ensures ((x < 14 && y == 7) || (x >= 14 && y == 5))
{
  // If x is less than 88 and also less than 14, set y to 7
  if x < 88 && x < 14 {
    y := 7;
  } else {
    // Otherwise, set y to 5
    y := 5;
  }
}

// Test method to verify the StrongPostCondition method
method TestStrongPostCondition() {

  var x: int;
  var y: int;
  var ans: int;

  // Test Case 1
  // Test with x set to -24
  x := -24;
  // Call StrongPostCondition with x
  ans := StrongPostCondition(x);
  // Assert that the returned value is 7
  assert 7 == ans;

  // Test Case 2
  // Test with x set to 26
  x := 26;
  // Call StrongPostCondition with x
  ans := StrongPostCondition(x);
  // Assert that the returned value is 5
  assert 5 == ans;

  // Test Case 3
  // Test with x set to 14 (equal to or greater than 14)
  x := 14;
  ans := StrongPostCondition(x);
  assert 5 == ans;

  // Test Case 4
  // Test with x set to 7 (less than 14)
  x := 7;
  ans := StrongPostCondition(x);
  assert 7 == ans;


  // Test Case 5
  // Test with x set to 87 (less than 88 but greater than or equal to 14)
  x := 87;
  ans := StrongPostCondition(x);
  assert 5 == ans;
}

// Note: Q6

method ComputeWeakestPrecondition(x: int) returns (pre: bool)
  // Precondition ensures the weakest precondition that y will be even
  ensures pre == ((x < 8 && x >= 4) || (x >= 32))
{
  // Define the condition to be simplified
  var y: int;
  var newX: int := x;
  // Analyze the nested conditions and their impact on y
  if x < 8 {
    if x < 4 {
      newX := x + 1;
      // y remains unchanged, so its parity does not change
      pre := true;
    } else {
      y := 2;
      // y is set to 2, which is even
      pre := true;
    }
  } else {
    if x < 32 {
      y := 1;
      // y is set to 1, which is odd
      pre := false;
    } else {
      // y remains unchanged, so its parity does not change
      pre := true;
    }
  }


  // Simplify the precondition to capture the scenarios where y is even
  pre := (x < 8 && x >= 4) || (x >= 32);
}

method TestComputeWeakestPrecondition() {
  var x: int;
  var result: bool;

  // Test case 1: x < 4
  x := 3;
  result := ComputeWeakestPrecondition(x);
  // Precondition should be true because x < 4 implies y is unchanged and remains valid
  assert result == false;

  // Test case 2: 4 <= x < 8
  x := 5;
  result := ComputeWeakestPrecondition(x);
  // Precondition should be true because 4 <= x < 8 implies y is set to 2
  assert result == true;

  // Test case 3: 8 <= x < 32
  x := 20;
  result := ComputeWeakestPrecondition(x);
  // Precondition should be false because 8 <= x < 32 implies y is set to 1
  assert result == false;

  // Test case 4: x >= 32
  x := 40;
  result := ComputeWeakestPrecondition(x);
  // Precondition should be true because x >= 32 implies y is unchanged and assumed to be even
  assert result == true;

  // Test case 5: x == 32
  x := 32;
  result := ComputeWeakestPrecondition(x);
  // Precondition should be true because x == 32 implies y is unchanged and assumed to be even
  assert result == true;

  // Test case 6: x == 7
  x := 7;
  result := ComputeWeakestPrecondition(x);
  // Precondition should be true because 4 <= x < 8 implies y is set to 2
  assert result == true;

  // Test case 7: x == 0
  x := 0;
  result := ComputeWeakestPrecondition(x);
  // Precondition should be false because x < 4 implies y is unchanged and remains valid
  assert result == false;

  // Test case 8: x == 15
  x := 15;
  result := ComputeWeakestPrecondition(x);
  // Precondition should be false because 8 <= x < 32 implies y is set to 1
  assert result == false;
}



method Max(x: int, y: int) returns (m: int)
  ensures m == x || m == y
  ensures x <= m && y <= m
{
  if x >= y {
    m := x;
  } else {
    m := y;
  }
}

method TestWeakestPrecondition(u: int)
  requires u % 2 == 1 // Weakest precondition
{
  var t := Max(2 * u, u + 7);
  assert t % 2 == 0; // Postcondition
}
