include "Matrix.dfy"

method gaussian (size:int, q: seq<real>, q_hat: seq<real>) returns (out: array<real>, alpha:real)
  requires |q_hat|==size
  requires |q|==size
  requires size > 0
  requires L2Norm(q_hat[..]) <= 1.0
  ensures alpha <= 1.0
{
  var i : int := 0;
  alpha := L2Norm(q_hat[..1]);
  var eta: real := 0.0;
  var eta_hat: real := 0.0;
  out := new real[size];
  while (i <size)
    invariant 0 < i <= size ==> alpha <= L2Norm(q_hat[..i])
    invariant i<=size
  {
    eta := *;
    eta_hat := - q_hat[i];
    alpha := L2Norm(q_hat[..i+1]);
    assert (q_hat[i] + eta_hat ==0.0);
    out[i] := q[i] + eta;
    i := i+1;
  }
  assert i==size;
  assert alpha <= L2Norm(q_hat[..size]);
  assert q_hat[..size] == q_hat[..];
  assert alpha <= L2Norm(q_hat[..]);
  assert alpha <= 1.0;
}