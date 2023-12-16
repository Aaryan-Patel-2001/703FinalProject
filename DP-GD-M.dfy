include "GaussianMechanism.dfy"
include "Matrix.dfy"

// In this variant of DP-GD, we add noise to the summation gradient instead of adding noise to gradient of each sample point
// Includes matrices instead of lists
method DPGD (x:Matrix, rows:int, columns:int, learning_rate:real, noise_scale:real, gradient_norm_bound:real, iterations:int) returns (Para:Matrix, PrivacyLost:real)
  requires iterations>=0
  requires rows>0
  requires columns > 0
  requires WellFormedMatrix(x)
  requires |x| == rows
  requires |x[0]| == columns
  requires noise_scale >= 1.0
  requires -1.0 <= gradient_norm_bound <= 1.0
{
  var thetha:Matrix := seq(1, i requires 0<=i< 1 => seq(columns, j requires 0 <= j < columns => 0.0));
  var alpha:real := 0.0;
  var tau:real := *;
  assume tau <= 1.0;
  var out:array<real>;
  var t :int := 0;
  while (t < iterations)
    invariant t <= iterations
    invariant alpha <= t as real * tau
  {
    var summation_gradient:Matrix, gradient_hat:Matrix := gradientBlackBox(x, rows, columns);
    var tau2:real;
    out, tau2 := gaussian(columns, summation_gradient[0], gradient_hat[0]);
    assert tau2 <= 1.0;
    alpha := alpha + tau;
    // thetha := subMatrices(thetha , scalarMultiplication(summation_gradient, learning_rate));
    t := t+1;
  }
  assert(t==iterations);
  assert(alpha <= iterations as real * tau);
  Para := thetha;
  PrivacyLost := alpha;
}
 

method gradientBlackBox(x:Matrix, rows:int, columns:int) returns (gradient: Matrix, gradient_hat:Matrix)
  requires rows > 0
  requires columns > 0
  requires WellFormedMatrix(x)
  requires |x| == rows
  requires |x[0]| == columns
  ensures |gradient| == |gradient_hat| == 1
  ensures |gradient[0]| == |gradient_hat[0]| == columns
  ensures L2Norm(gradient_hat[0]) <= 1.0
{
  var i :int := 0;
  var summation_gradient:Matrix := seq(1, i requires 0<=i< 1 => seq(columns, j requires 0 <= j < columns => 0.0));
  var alignment:Matrix  := seq(1, i requires 0<=i< 1 => seq(columns, j requires 0 <= j < columns => 0.0));
  while (i < columns)
  {
    // summation_gradient[0][i] := *;
    // alignment[0][i]
    i := i + 1;
  }
  gradient_hat := alignment;
  assert |gradient_hat[0]| > 0;
  assume L2Norm(gradient_hat[0]) <= 1.0;
  gradient := summation_gradient;
}
