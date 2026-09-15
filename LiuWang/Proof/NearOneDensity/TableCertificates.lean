import LiuWang.Proof.NearOneDensity.RationalBudget

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.NearOneDensity

inductive DensityRow
  | r027 | r028 | r030 | r031 | r032 | r033 | r036 | r039 | r042
  | r045 | r046 | r047 | r0475 | r0478
  deriving DecidableEq

def rowLambda : DensityRow → ℝ
  | .r027 => 0.27 | .r028 => 0.28 | .r030 => 0.3
  | .r031 => 0.31 | .r032 => 0.32 | .r033 => 0.33
  | .r036 => 0.36 | .r039 => 0.39 | .r042 => 0.42
  | .r045 => 0.45 | .r046 => 0.46 | .r047 => 0.47
  | .r0475 => 0.475 | .r0478 => 0.478

def rowA : DensityRow → ℝ
  | .r027 | .r028 | .r030 => 0.365
  | .r031 => 0.3519 | .r032 => 0.3382 | .r033 => 0.3238
  | .r036 => 0.2825 | .r039 => 0.2413 | .r042 => 0.2003
  | .r045 => 0.34 | .r046 => 0.33 | .r047 => 0.32
  | .r0475 => 0.315 | .r0478 => 0.311

def rowSelectedBound : DensityRow → ℕ
  | .r027 => 7 | .r028 => 8 | .r030 => 9
  | .r031 => 10 | .r032 => 11 | .r033 => 13
  | .r036 => 20 | .r039 => 35 | .r042 => 89
  | .r045 => 91 | .r046 => 146 | .r047 => 332
  | .r0475 => 834 | .r0478 => 7000

def rowMultiplicity : DensityRow → ℕ
  | .r045 | .r046 | .r047 | .r0475 | .r0478 => 2
  | _ => 1

def rowBound (r : DensityRow) : ℕ := rowMultiplicity r * rowSelectedBound r

theorem row_endpoint_certificate (r : DensityRow) :
    0 ≤ (rowSelectedBound r + 1 : ℝ) * 0.0755 ^ 2 - 0.8973 ^ 2 +
        rowSelectedBound r * 0.8973 * 0.7647 ∧
    -2 * (rowSelectedBound r + 1 : ℝ) * (1 / (rowA r + rowLambda r) - 0.2763932023) * 0.0755 +
      2 * (1 / rowA r) * 0.8973 -
      rowSelectedBound r * ((1 / rowA r) * 0.7647 - 0.8973 * 0.2763932023) +
      2 * ((rowSelectedBound r + 1 : ℝ) * 0.0755 ^ 2 - 0.8973 ^ 2 +
        rowSelectedBound r * 0.8973 * 0.7647) * (1 / 25.328436) ≤ 0 ∧
    massBudget (rowA r) (1 / 25.328436) ^ 2 +
        rowSelectedBound r * massBudget (rowA r) (1 / 25.328436) * crossBudget 0.2763932023 (1 / 25.328436) <
      (rowSelectedBound r + 1 : ℝ) * zeroBudget (rowA r) (rowLambda r) 0.2763932023 (1 / 25.328436) ^ 2 := by
  cases r <;> norm_num [rowSelectedBound, rowA, rowLambda, massBudget, crossBudget, zeroBudget]

theorem row_basic_certificate (r : DensityRow) :
    0 < rowA r ∧ rowLambda r ≤ 0.5 ∧
    0 ≤ massBudget (rowA r) (1 / 25.328436) ∧
    crossBudget 0.2763932023 (1 / 25.328436) ≤ massBudget (rowA r) (1 / 25.328436) ∧
    0 ≤ zeroBudget (rowA r) (rowLambda r) 0.2763932023 (1 / 25.328436) := by
  cases r <;> norm_num [rowA, rowLambda, massBudget, crossBudget, zeroBudget]

theorem row_continuous_budget (r : DensityRow) {lam x k : ℝ}
    (hlam : 0.262132 ≤ lam) (hupper : lam ≤ rowLambda r)
    (hx : 0 ≤ x) (hxH : x ≤ 1 / 25.328436) (hk : k ≤ 0.2763932023) :
    0 ≤ massBudget (rowA r) x ∧
    crossBudget k x ≤ massBudget (rowA r) x ∧
    0 ≤ zeroBudget (rowA r) lam k x ∧
    0 < zeroBudget (rowA r) lam k x ^ 2 - massBudget (rowA r) x * crossBudget k x ∧
    (massBudget (rowA r) x ^ 2 - massBudget (rowA r) x * crossBudget k x) /
      (zeroBudget (rowA r) lam k x ^ 2 - massBudget (rowA r) x * crossBudget k x) <
        rowSelectedBound r + 1 := by
  have he := row_endpoint_certificate r
  have hb := row_basic_certificate r
  have hmass : massBudget (rowA r) (1 / 25.328436) ≤ massBudget (rowA r) x := by
    unfold massBudget
    linarith
  have hcross : crossBudget k x ≤ crossBudget 0.2763932023 (1 / 25.328436) := by
    unfold crossBudget
    linarith
  have hrec := one_div_le_one_div_of_le
    (show 0 < rowA r + lam by linarith [hb.1])
    (show rowA r + lam ≤ rowA r + rowLambda r by linarith)
  have hD : zeroBudget (rowA r) (rowLambda r) 0.2763932023 (1 / 25.328436) ≤
      zeroBudget (rowA r) (rowLambda r) 0.2763932023 x := by
    unfold zeroBudget
    linarith
  have hDlam : zeroBudget (rowA r) (rowLambda r) 0.2763932023 x ≤
      zeroBudget (rowA r) lam k x := by
    unfold zeroBudget
    linarith
  have hA := hb.2.2.1.trans hmass
  have hBA := hcross.trans (hb.2.2.2.1.trans hmass)
  have hD0 := hb.2.2.2.2.trans hD
  have hbudget := strict_budget_on_interval hx hxH he.1 he.2.1 he.2.2
  have hB : crossBudget k x ≤ crossBudget 0.2763932023 x := by
    unfold crossBudget
    linarith
  have hK : 0 ≤ (rowSelectedBound r : ℝ) := Nat.cast_nonneg _
  have hpaid : massBudget (rowA r) x ^ 2 +
        rowSelectedBound r * massBudget (rowA r) x * crossBudget k x <
      (rowSelectedBound r + 1 : ℝ) * zeroBudget (rowA r) lam k x ^ 2 := by
    have hleft := mul_le_mul_of_nonneg_left hB (mul_nonneg hK hA)
    have hsq : zeroBudget (rowA r) (rowLambda r) 0.2763932023 x ^ 2 ≤
        zeroBudget (rowA r) lam k x ^ 2 := by nlinarith
    have hright := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ rowSelectedBound r + 1 by positivity)
    linarith
  exact ⟨hA, hBA, hD0.trans hDlam, ratio_lt_of_strict_budget hA hBA hpaid⟩

theorem row_source_budget (r : DensityRow) {z lam : ℝ}
    (hz : 100000000000 ≤ z) (hlam : 0.262132 ≤ lam) (hupper : lam ≤ rowLambda r) :
    let x := 1 / Real.log z
    let k := (1 - 1 / Real.sqrt 5) / 2
    0 ≤ massBudget (rowA r) x ∧ crossBudget k x ≤ massBudget (rowA r) x ∧
    0 ≤ zeroBudget (rowA r) lam k x ∧
    0 < zeroBudget (rowA r) lam k x ^ 2 - massBudget (rowA r) x * crossBudget k x ∧
    (massBudget (rowA r) x ^ 2 - massBudget (rowA r) x * crossBudget k x) /
      (zeroBudget (rowA r) lam k x ^ 2 - massBudget (rowA r) x * crossBudget k x) <
        rowSelectedBound r + 1 :=
  row_continuous_budget r hlam hupper (source_inverse_log_bounds hz).1
    (source_inverse_log_bounds hz).2 kappa_le_rational

theorem corrected_table5_first : rowSelectedBound .r045 = 91 ∧ rowBound .r045 = 182 := by
  norm_num [rowSelectedBound, rowBound, rowMultiplicity]

end LiuWang.Proof.NearOneDensity
