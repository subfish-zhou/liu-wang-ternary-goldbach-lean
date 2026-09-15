import LiuWang.Proof.Campaign20260915.SecondTerminal.LastFixedCertificate
import Lean.Elab.Command

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

private def lastDown (n : ℕ) (x : ℚ) : ℚ := (⌊x * 10 ^ n⌋ : ℚ) / 10 ^ n
private def lastUp (n : ℕ) (x : ℚ) : ℚ := (⌈x * 10 ^ n⌉ : ℚ) / 10 ^ n

private def lastDirectedExp (x : ℚ) : ℚ × ℚ := Id.run do
  let t := x / 256
  let p := (List.range 32).foldl (fun r k => r + t ^ k / (k.factorial : ℚ)) 0
  let e := |t| ^ (32 : ℕ) * (33 / ((Nat.factorial 32 : ℚ) * 32))
  return (max 0 (lastDown 80 ((max 0 (lastDown 40 (p - e))) ^ (256 : ℕ))),
    lastUp 80 ((lastUp 40 (p + e)) ^ (256 : ℕ)))

private def lastRationalCell (i : ℕ) : ℚ := Id.run do
  let point := fun j : ℕ => (25329413 : ℚ) / 1000000 +
    (59721417 / 1000000 - 25329413 / 1000000) * j / 32
  let u := point i
  let v := point (i + 1)
  let m := (u + v) / 2
  let a : ℚ := (3093092244719 / 1000000000) / (9645908801 / 1000000000)
  let b : ℚ := 2067 / 10000 * 3100
  let s := -1 / 2 + a / m ^ (2 : ℕ)
  let intercept := -2 * a / m
  let eu := lastDirectedExp (s * u + intercept)
  let ev := lastDirectedExp (s * v + intercept)
  let en := lastDirectedExp (-v / 2 - b / u)
  let first := (1 / s) * (if 0 ≤ 1 / s then ev.2 else ev.1) -
    (1 / s) * (if 0 ≤ 1 / s then eu.1 else eu.2)
  return lastUp 30 (first - (v - u) * en.1)

macro "certify_last_cell " i:num : command => do
  if i.getNat ≥ 32 then Lean.Macro.throwError "last cell index must be below 32"
  let value := lastRationalCell i.getNat
  if value < 0 then Lean.Macro.throwError "unexpected negative last-cell upper value"
  let n := Lean.Syntax.mkNumLit (toString value.num.natAbs)
  let d := Lean.Syntax.mkNumLit (toString value.den)
  let name := Lean.mkIdent (Lean.Name.mkSimple ("last_cell_" ++ toString i.getNat))
  `(set_option maxHeartbeats 0 in
    set_option maxRecDepth 0 in
    theorem $name : lastFixedCellUpper $i = ($n : ℝ) / $d := by
      norm_num [lastFixedCellUpper, lastFixedPoint, lastFixedMidpoint, lastFixedA, lastFixedB,
        SecondLow.affineExpUpper, SecondLow.affineAmplitude,
        SecondLow.tangentSlope, SecondLow.tangentIntercept,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.primitiveCoefficient,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.expLower,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.expUpper,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.expBaseLower,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.expBaseUpper,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.roundDown,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.roundUp,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.expSeries,
        SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.expError,
        Finset.sum_range_succ])

end LiuWang.Proof.Campaign20260915.SecondTerminal
