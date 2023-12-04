include "GaussianMechanism.dfy"

// In this variant of DP-GD, we add noise to the summation gradient instead of adding noise to gradient of each sample point
// Includes matrices instead of lists
method DPGD (x:array<array<real>>, rows:int, columns:int, learning_rate:real, noise_scale:real, gradient_norm_bound:real, iterations:int) returns (Para:real, PrivacyLost:real)
  requires iterations>=0
  requires rows>0
  requires columns > 0
  requires WellFormedMatrix(x, rows, columns)
  requires noise_scale >= 1.0
  requires -1.0 <= gradient_norm_bound <= 1.0
{
  var thetha:array<real> := new real[iterations+1];
  thetha[0] := *;
  var alpha:real := 0.0;
  var tau:real := *;
  assume tau <= 1.0;
  var out:array<real>;
  var t :int := 0;
  while (t < iterations)
    invariant t <= iterations
    invariant alpha <= t as real * tau
  {
    var summation_gradient:array<real>, gradient_hat:array<real> := gradientBlackBox(x, rows, columns);
    var tau2:real;
    out, tau2 := gaussian(columns, summation_gradient, gradient_hat);
    assert tau2 <= 1.0;
    alpha := alpha + tau;
    // thetha[t+1] := thetha[t] - learning_rate*summation_gradient;
    t := t+1;
  }
  assert(t==iterations);
  assert(alpha <= iterations as real * tau);
  Para := thetha[iterations];
  PrivacyLost := alpha;
}

method gradientBlackBox(x:array<array<real>>, rows:int, columns:int) returns (gradient: array<real>, gradient_hat:array<real>)
  requires rows > 0
  requires columns > 0
  requires MatrixSensitivity(x, rows, columns)
  ensures gradient.Length == gradient_hat.Length == columns
  ensures arraySquaredSum(gradient_hat[..]) <= 1.0
{
  var i :int := 0;
  var summation_gradient:array<real> := new real[columns];
  var alignment:array<real> := new real[columns];
  while (i < rows)
    invariant i <= rows
  {
    var j:int := 0;
    while (j < columns)
      invariant j <= columns
    {
      var grad_j:real := *;
      var grad_jAlignment:real := *;
      summation_gradient[j] := summation_gradient[j] + grad_j;
      alignment[j] := grad_jAlignment;
      j := j + 1;
    }
    i := i + 1;
  }
  gradient_hat := alignment;
  assume arraySquaredSum(gradient_hat[..]) <= 1.0;
  gradient := summation_gradient;
}

// ensuring number of rows and columns are of the right rows
ghost predicate WellFormedMatrix(x:array<array<real>>, rows:int, columns:int)
  reads x
{
  x.Length == rows &&
  forall i:nat | i < rows :: x[i].Length == columns
}

// adjacent matrices are defined such that only one row is different, and the row that differs can be arbitiraly different
// L2 sensitivty of each row is bounded by 1 -- requirement of the Gaussian mechanism
ghost predicate MatrixSensitivity(x:array<array<real>>, rows:int, columns:int)
  reads x
{
  WellFormedMatrix(x, rows, columns)

}

method MatrixAddition(x:array<real>, y:array<real>) returns (z:array<real>)
  requires x.Length == y.Length
{
  var zl:array<real> := new real[x.Length];
  var i:int := 0;
  while (i < x.Length)
  {
    zl[i] := x[i] + y[i];
    i := i + 1;
  }
  z := zl;
}