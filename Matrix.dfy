type Matrix = seq<seq<real>>

predicate WellFormedMatrix(m:Matrix)
{
    && forall i:nat | i < |m| :: |m[i]|==|m[0]|
}

function addMatrices(m1: Matrix, m2:Matrix): Matrix
requires WellFormedMatrix(m1)
requires WellFormedMatrix(m2)
requires |m1| > 0 
requires |m2| > 0
requires |m1| == |m2|
requires |m1[0]| == |m2[0]|
{
    seq(|m1|, i requires 0 <= i < |m1| => seq(|m1[i]|, j requires 0 <= j < |m1[i]| => m1[i][j] + m2[i][j]))
}

function subMatrices(m1: Matrix, m2:Matrix): Matrix
requires WellFormedMatrix(m1)
requires WellFormedMatrix(m2)
requires |m1| > 0 
requires |m2| > 0
requires |m1| == |m2|
requires |m1[0]| == |m2[0]|
{
    seq(|m1|, i requires 0 <= i < |m1| => seq(|m1[i]|, j requires 0 <= j < |m1[i]| => m1[i][j] - m2[i][j]))
}

function scalarMultiplication(m: Matrix, alpha:real): Matrix
requires WellFormedMatrix(m)
requires |m| > 0 
{
    seq(|m|, i requires 0 <= i < |m| => seq(|m[i]|, j requires 0 <= j < |m[i]| => m[i][j] * alpha))
}


function L2Norm(a: seq<real>): real
  requires |a| > 0
{
  if |a| == 1 then
    a[0]*a[0]
  else
    (a[0]*a[0]) + L2Norm(a[1..])
}