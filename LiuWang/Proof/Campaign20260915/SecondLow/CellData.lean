import LiuWang.Proof.Campaign20260915.SecondLow.FixedCertificate
import Lean.Elab.Command

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.SecondLow

private def down (n : ℕ) (x : ℚ) : ℚ := (⌊x * 10 ^ n⌋ : ℚ) / 10 ^ n
private def up (n : ℕ) (x : ℚ) : ℚ := (⌈x * 10 ^ n⌉ : ℚ) / 10 ^ n

private def directedExp (x : ℚ) : ℚ × ℚ := Id.run do
  let t := x / 256
  let p := (List.range 32).foldl (fun r k => r + t ^ k / (k.factorial : ℚ)) 0
  let e := |t| ^ (32 : ℕ) * (33 / ((Nat.factorial 32 : ℚ) * 32))
  return (max 0 (down 80 ((max 0 (down 40 (p - e))) ^ (256 : ℕ))),
    up 80 ((up 40 (p + e)) ^ (256 : ℕ)))

private def affineBudget (A B a c m u v : ℚ) : ℚ := Id.run do
  let s := c + a / m ^ (2 : ℕ)
  let b := -2 * a / m
  let amplitude := fun y => A * ((y - 1 / s) / s) + B / s
  let eu := directedExp (s * u + b)
  let ev := directedExp (s * v + b)
  return amplitude v * (if 0 ≤ amplitude v then ev.2 else ev.1) -
    amplitude u * (if 0 ≤ amplitude u then eu.1 else eu.2)

private def rationalCell (i : ℕ) : ℚ := Id.run do
  let point := fun j : ℕ => (25 : ℚ) + (36510750 / 1000000 - 25) * j / 16
  let u := point i
  let v := point (i + 1)
  let m := (u + v) / 2
  let a : ℚ := 478 / 1000 * (3093092244719 / 1000000000)
  let ell : ℚ := 24117472185 / 1000000000
  let p : ℚ := 3141592 / 1000000
  let A₁ : ℚ := 3100 / p
  let B₁ : ℚ := 3100 * (ell / p - 874 / 1000)
  let A₂ : ℚ := 68423 / 10000 * (3100 : ℚ) ^ (4 : ℕ)
  let B₂ : ℚ := (3100 : ℚ) ^ (4 : ℕ) * (68423 / 10000 * ell + 15)
  return up 20 (affineBudget A₁ B₁ a (1 / 2) m u v +
    affineBudget A₂ B₂ a (-1 / 2) m u v)

macro "certify_low_cell " i:num : command => do
  if i.getNat ≥ 16 then Lean.Macro.throwError "low cell index must be below 16"
  let value := rationalCell i.getNat
  if value < 0 then Lean.Macro.throwError "unexpected negative low-cell upper value"
  let n := Lean.Syntax.mkNumLit (toString value.num.natAbs)
  let d := Lean.Syntax.mkNumLit (toString value.den)
  let name := Lean.mkIdent (Lean.Name.mkSimple ("low_cell_" ++ toString i.getNat))
  `(set_option maxHeartbeats 0 in
    set_option maxRecDepth 0 in
    theorem $name : lowFixedCellUpper $i = ($n : ℝ) / $d := by
      norm_num [lowFixedCellUpper, affineExpUpper, affineAmplitude,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.primitiveCoefficient,
        tangentSlope, tangentIntercept, lowFixedPoint, lowFixedMidpoint,
        fixedA₁, fixedB₁, fixedA₂, fixedB₂, fixedParameter,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.expLower,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.expUpper,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.expBaseLower,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.expBaseUpper,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.roundDown,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.roundUp,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.expSeries,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.expError,
        Finset.sum_range_succ])

end LiuWang.Proof.Campaign20260915.SecondLow
