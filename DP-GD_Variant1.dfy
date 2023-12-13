// In this variant of DP-GD, we add noise to the summation gradient instead of adding noise to gradient of each sample point
method DPGD_SummationGradientPerturbation (size:int, learning_rate:real, noise_scale:real, gradient_norm_bound:real, iterations:int) returns (Para:real, PrivacyLost:real)
  requires iterations>=0
  requires size>0
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
    var gradient_alignment:array<real> :=  new real[size];
    assume gradient_alignment.Length == size;
    var summation_gradient_alignement:real := sum(gradient_alignment[..1]);
    assume forall i:int | 0 <= i < gradient_alignment.Length :: (-1.0 <= gradient_alignment[i] <= 1.0);
    assume forall i:int | 0 <= i <  gradient_alignment.Length :: gradient_alignment[i] != 0.0 ==> (forall j:int | 0 <= j <  gradient_alignment.Length && j != i :: gradient_alignment[j] == 0.0);
    while (i< size)
      invariant i <= size
      invariant i < size ==> -1.0 <= gradient_alignment[i] <= 1.0
      invariant i < size ==>  gradient_alignment[i] != 0.0 ==> (forall j:int | 0 <= j <  gradient_alignment.Length && j != i :: gradient_alignment[j] == 0.0)
      invariant i > 0 ==> summation_gradient_alignement == sum(gradient_alignment[..i])
    {
      var gradient:real := *;
      gradient_alignment[i] := *; 
      assume forall i:int | 0 <= i < gradient_alignment.Length :: (-1.0 <= gradient_alignment[i] <= 1.0);
      assume forall i:int | 0 <= i <  gradient_alignment.Length :: gradient_alignment[i] != 0.0 ==> (forall j:int | 0 <= j <  gradient_alignment.Length && j != i :: gradient_alignment[j] == 0.0);
      summation_gradient := summation_gradient + gradient;
      summation_gradient_alignement := sum(gradient_alignment[..i+1]);
      i := i + 1;
    }
    assert summation_gradient_alignement == sum(gradient_alignment[..size]);
    assert gradient_alignment[..size] == gradient_alignment[..];
    assert summation_gradient_alignement == sum(gradient_alignment[..]);
    assume -1.0 <= sum(gradient_alignment[..]) <= 1.0; 
    assert -1.0 <= summation_gradient_alignement <= 1.0; 
    var eta:real := *;
    var eta_hat:real := - summation_gradient_alignement;
    assert (summation_gradient_alignement + eta_hat == 0.0);
    summation_gradient := summation_gradient + eta;
    summation_gradient_alignement := summation_gradient_alignement + eta_hat;
    alpha := alpha + tau;
    thetha[t+1] := thetha[t] - learning_rate*summation_gradient;
    t := t+1;
  }
  assert(t==iterations);
  assert(alpha == iterations as real * tau);
  Para := thetha[iterations];
  PrivacyLost := alpha;
}

function sum(a:seq<real>) : real
requires |a| > 0
{
  if |a| == 1 then
    a[0]
  else
    a[0] + sum(a[1..])
}