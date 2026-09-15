import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RefinedCertificate
import Lean.Elab.Command

set_option autoImplicit false

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

private def downQ (n : ℕ) (x : ℚ) : ℚ := (⌊x * 10 ^ n⌋ : ℚ) / 10 ^ n
private def upQ (n : ℕ) (x : ℚ) : ℚ := (⌈x * 10 ^ n⌉ : ℚ) / 10 ^ n

private def expQ (x : ℚ) : ℚ × ℚ := Id.run do
  let t := x / 256
  let s := (List.range 32).foldl (fun a k => a + t ^ k / (Nat.factorial k : ℚ)) 0
  let e := |t| ^ (32 : ℕ) * (33 / ((Nat.factorial 32 : ℚ) * 32))
  return (max 0 (downQ 80 ((max 0 (downQ 40 (s - e))) ^ (256 : ℕ))),
    upQ 80 ((upQ 40 (s + e)) ^ (256 : ℕ)))

private def coefficientQ (s : ℚ) : ℕ → ℚ → ℚ
  | 0, _ => 1 / s
  | n + 1, y => (y ^ (n + 1) - (n + 1) * coefficientQ s n y) / s

private def cellBudgetQ (n i : ℕ) : ℚ := Id.run do
  let H : ℚ := 3093092244719 / 1000000000
  let u : ℚ := 25329413 / 1000000 + (59721417 - 25329413) / 1000000 * i / n
  let v : ℚ := 25329413 / 1000000 + (59721417 - 25329413) / 1000000 * (i + 1) / n
  let m := (u + v) / 2
  let s := -1 / 2 + 239 / 500 * H / m ^ (2 : ℕ)
  let b := -239 / 250 * H / m
  if s = 0 then
    let a := H / ((H - 4 * u) * (H - 4 * v)) *
      ((H - 4 * v) * (254231 * ((v ^ (6 : ℕ) - u ^ (6 : ℕ)) / 6) +
        33643 * ((v ^ (7 : ℕ) - u ^ (7 : ℕ)) / 7)) +
        4 * (254231 * ((v ^ (7 : ℕ) - u ^ (7 : ℕ)) / 7 -
          u * ((v ^ (6 : ℕ) - u ^ (6 : ℕ)) / 6)) +
          33643 * ((v ^ (8 : ℕ) - u ^ (8 : ℕ)) / 8 -
            u * ((v ^ (7 : ℕ) - u ^ (7 : ℕ)) / 7))))
    let e := expQ b
    return upQ 25 (a * (if 0 ≤ a then e.2 else e.1))
  let amp := fun y =>
    H / ((H - 4 * u) * (H - 4 * v)) *
      ((H - 4 * v) * (254231 * coefficientQ s 5 y + 33643 * coefficientQ s 6 y) +
        4 * (254231 * (coefficientQ s 6 y - u * coefficientQ s 5 y) +
          33643 * (coefficientQ s 7 y - u * coefficientQ s 6 y)))
  let ev := expQ (s * v + b)
  let eu := expQ (s * u + b)
  let value := amp v * (if 0 ≤ amp v then ev.2 else ev.1) -
    amp u * (if 0 ≤ amp u then eu.1 else eu.2)
  return upQ 25 value

private def rationalSyntax (x : ℚ) : Lean.MacroM (Lean.TSyntax `term) := do
  let n := Lean.Syntax.mkNumLit (toString x.num.natAbs)
  let d := Lean.Syntax.mkNumLit (toString x.den)
  if x < 0 then `((-($n : ℝ)) / $d) else `(($n : ℝ) / $d)

macro "certify_fixed_cell " i:num : command => do
  let index := i.getNat
  if index ≥ 256 then Lean.Macro.throwError "fixed cell index outside the admitted partition"
  let budget := cellBudgetQ 256 index
  let rhs ← rationalSyntax budget
  let name := Lean.mkIdent (Lean.Name.mkSimple ("cell_" ++ toString index))
  `(theorem $name : fixedCellUpper $i ≤ $rhs := by
      norm_num [fixedCellUpper, cellUpper, fixedPoint, fixedMidpoint,
        FixedIntegral.phaseSlope, FixedIntegral.phaseIntercept,
        primitiveAmplitude, primitiveCoefficient, expLower, expUpper, expBaseLower, expBaseUpper,
        roundDown, roundUp, expSeries, expError, Finset.sum_range_succ])

macro "certify_fixed_block " j:num : command => do
  let start := j.getNat * 32
  if start ≥ 256 then Lean.Macro.throwError "fixed block index outside the admitted partition"
  let budget := (List.range 32).foldl (fun a k => a + cellBudgetQ 256 (start + k)) 0
  let rhs ← rationalSyntax budget
  let offset := Lean.Syntax.mkNumLit (toString start)
  let name := Lean.mkIdent (Lean.Name.mkSimple ("block_" ++ toString j.getNat))
  let cells := (List.range 32).map fun k =>
    Lean.mkIdent (Lean.Name.mkSimple ("cell_" ++ toString (start + k)))
  let proofs : Array (Lean.TSyntax `term) := cells.toArray.map fun c => ⟨c.raw⟩
  `(theorem $name :
      (∑ k ∈ Finset.range 32, fixedCellUpper ($offset + k)) ≤ $rhs := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, zero_add]
      linarith only [$proofs,*])

macro "certify_refined_cell " i:num : command => do
  let index := i.getNat
  if index ≥ 1024 then Lean.Macro.throwError "refined cell index outside the fixed partition"
  let rhs ← rationalSyntax (cellBudgetQ 1024 index)
  let name := Lean.mkIdent (Lean.Name.mkSimple ("refined_cell_" ++ toString index))
  `(theorem $name : refinedCellUpper $i ≤ $rhs := by
      norm_num [refinedCellUpper, cellUpper, refinedPoint, refinedMidpoint,
        FixedIntegral.phaseSlope, FixedIntegral.phaseIntercept,
        primitiveAmplitude, primitiveCoefficient, zeroAmplitude,
        expLower, expUpper, expBaseLower, expBaseUpper,
        roundDown, roundUp, expSeries, expError, Finset.sum_range_succ])

macro "certify_refined_block " j:num : command => do
  let start := j.getNat * 64
  if start ≥ 1024 then Lean.Macro.throwError "refined block index outside the fixed partition"
  let budget := (List.range 64).foldl (fun a k => a + cellBudgetQ 1024 (start + k)) 0
  let rhs ← rationalSyntax budget
  let offset := Lean.Syntax.mkNumLit (toString start)
  let name := Lean.mkIdent (Lean.Name.mkSimple ("refined_block_" ++ toString j.getNat))
  let cells := (List.range 64).map fun k =>
    Lean.mkIdent (Lean.Name.mkSimple ("refined_cell_" ++ toString (start + k)))
  let proofs : Array (Lean.TSyntax `term) := cells.toArray.map fun c => ⟨c.raw⟩
  `(theorem $name :
      (∑ k ∈ Finset.range 64, refinedCellUpper ($offset + k)) ≤ $rhs := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, zero_add]
      linarith only [$proofs,*])

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
