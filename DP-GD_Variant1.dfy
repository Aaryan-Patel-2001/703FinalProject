// In this variant of DP-GD, we add noise to the summation gradient instead of adding noise to gradient of each sample point
method DPGD_SummationGradientPerturbation (size:int, learning_rate:real, noise_scale:real, gradient_norm_bound:real, iterations:int) returns (Para:real, PrivacyLost:real)
  requires iterations>=0
  requires size>=0
  requires noise_scale >= 1.0
  requires -1.0 <= gradient_norm_bound <= 1.0
{
  var thetha:array<real> := new real[iterations+1];
  thetha[0] := *;
  var alpha:real := 0.0;
  var tau:real := *;
  assume(tau>=0.0);
  var t :int := 0;
  while (t < iterations)
    invariant t <= iterations
    invariant alpha == t as real * tau
  {
    var i :int := 0;
    var beta:real := 0.0;
    var summation_gradient:real := 0.0;
    while (i< size)
      invariant i <= size
    {
      var gradient:real := *;
      // Note: We do not need to clip the value of the gradient.
      // Instead, we clip the sensitivity of the gradient by the gradient_norm_bound provided by the user
      summation_gradient := summation_gradient + gradient;
      i := i + 1;
    }
    var eta:real := *;
    var eta_hat:real := - gradient_norm_bound;
    assert (gradient_norm_bound + eta_hat == 0.0);
    summation_gradient := summation_gradient + eta;
    alpha := alpha + tau;
    thetha[t+1] := thetha[t] - learning_rate*summation_gradient;
    t := t+1;
  }
  assert(t==iterations);
  assert(alpha == iterations as real * tau);
  Para := thetha[iterations];
  PrivacyLost := alpha;
}

