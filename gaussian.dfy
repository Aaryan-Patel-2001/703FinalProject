// VERIFY USING DAFNY:
// /Applications/dafny/dafny /Users/apple/GaussianDP/Dafny/gaussian.dfy
method gaussian (epsilon:real, delta:real, size:int, q: array<real>, SHADOWDP_ALIGNED_DISTANCE_q: array<real>, SHADOWDP_SHADOW_DISTANCE_q: array<real>) returns (out: real)
requires size>0
requires epsilon>0.0
requires forall k: int :: 0 <= k < SHADOWDP_ALIGNED_DISTANCE_q.Length ==> -1.0 <= SHADOWDP_ALIGNED_DISTANCE_q[k] <= 1.0
requires SHADOWDP_ALIGNED_DISTANCE_q.Length==size
requires q.Length==size
requires SHADOWDP_SHADOW_DISTANCE_q.Length==size

{
 var alpha : real := 0.0;
 var i : int := 0;
 var tau : real := *;
 var eta: real := 0.0;
 var eta_hat: real := 0.0;
 while (i <size)
 invariant alpha == (i as real) * tau
 invariant i<=size
 invariant i<size ==>-1.0 <= SHADOWDP_ALIGNED_DISTANCE_q[i] <= 1.0
 {
  assume (forall x : real :: -1.0 <= x <= 1.0 ==> x * x <= 1.0 );
  eta := *;
  eta_hat := - SHADOWDP_ALIGNED_DISTANCE_q[i];
  assert (eta_hat * eta_hat <= 1.0);
//   assert (-1.0 <= eta_hat <= 1.0);
//   assert ( squaredValueAxiom(eta_hat))
  alpha := alpha + tau;
  assert (SHADOWDP_ALIGNED_DISTANCE_q[i] + eta_hat ==0.0);
  out := q[i] + eta;
  i := i+1;
 }
 assert i==size;
 assert alpha == (size as real) * tau;
}



function {:axiom} squaredValueAxiom(x:real) : bool 
requires  -1.0 <= x <= 1.0
ensures x * x <= 1.0


/*
predicate P1(x:real)
{
 (x*x) <= 1.0 
}

predicate P2(x:real)
{
 -1.0 <= x <= 1.0
}

method myfun2(x:real) returns (out:int)
requires -1.0<=x<=1.0
{
 assert -1.0<= -1.0*x <= 1.0;
 out := 0;
}

method myfunc(x:real) returns (out:int) 
requires -1.0<=x<=1.0
{
 assert(x*x<=1.0);
 out := 0;
}
*/
// add axioms for line 22
