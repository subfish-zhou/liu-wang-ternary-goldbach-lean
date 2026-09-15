import LiuWang.Proof.Campaign20260915.SecondTerminal.LastFixedEnvelope

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

theorem last_fixed_tangent_domain {m z : ℝ}
    (hm : m ∈ Set.Icc (25.329413 : ℝ) 60)
    (hz : z ∈ Set.Icc (25.329413 : ℝ) 60) :
    SecondLow.tangentSlope lastFixedA (-1 / 2) m ≠ 0 ∧
      |SecondLow.tangentSlope lastFixedA (-1 / 2) m * z +
        SecondLow.tangentIntercept lastFixedA m| ≤ 256 := by
  have hm0 : 0 < m := by linarith [hm.1]
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hm2 : (25.329413 : ℝ) ^ (2 : ℕ) ≤ m ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hm.1 2
  have ha0 : 0 ≤ lastFixedA / m ^ (2 : ℕ) := by unfold lastFixedA; positivity
  have ha : lastFixedA / m ^ (2 : ℕ) < 1 / 2 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    norm_num [lastFixedA] at hm2 ⊢
    linarith
  have hslo : -1 / 2 ≤ SecondLow.tangentSlope lastFixedA (-1 / 2) m := by
    unfold SecondLow.tangentSlope
    linarith
  have hshi : SecondLow.tangentSlope lastFixedA (-1 / 2) m < 0 := by
    unfold SecondLow.tangentSlope
    linarith
  have hbhi : SecondLow.tangentIntercept lastFixedA m ≤ 0 := by
    unfold SecondLow.tangentIntercept lastFixedA
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hm0.le
  have hblo : -26 ≤ SecondLow.tangentIntercept lastFixedA m := by
    unfold SecondLow.tangentIntercept
    apply (le_div_iff₀ hm0).mpr
    norm_num [lastFixedA]
    linarith [hm.1]
  have hp := mul_le_mul_of_nonneg_right hslo hz0
  have hn := mul_nonpos_of_nonpos_of_nonneg hshi.le hz0
  exact ⟨hshi.ne, abs_le.mpr ⟨by linarith [hz.2], by linarith⟩⟩

def lastFixedCellUpper (i : ℕ) : ℝ :=
  Fixed032281.roundUp 30
    (SecondLow.affineExpUpper 0 1 lastFixedA (-1 / 2) (lastFixedMidpoint i)
      (lastFixedPoint i) (lastFixedPoint (i + 1)) -
    (lastFixedPoint (i + 1) - lastFixedPoint i) *
      Fixed032281.expLower (-lastFixedPoint (i + 1) / 2 - lastFixedB / lastFixedPoint i))

theorem lastFixedCellValue_le_upper {i : ℕ} (hi : i < 32) :
    lastFixedCellValue i ≤ lastFixedCellUpper i := by
  have hu : lastFixedPoint i ∈ Set.Icc (25.329413 : ℝ) 60 := by
    refine ⟨lastFixedPoint_ge i, ?_⟩
    exact (lastFixedPoint_monotone hi.le).trans (by norm_num [lastFixedPoint])
  have hv : lastFixedPoint (i + 1) ∈ Set.Icc (25.329413 : ℝ) 60 := by
    refine ⟨lastFixedPoint_ge (i + 1), ?_⟩
    exact (lastFixedPoint_monotone (show i + 1 ≤ 32 from hi)).trans (by norm_num [lastFixedPoint])
  have hm : lastFixedMidpoint i ∈ Set.Icc (25.329413 : ℝ) 60 := by
    unfold lastFixedMidpoint
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  have htu := last_fixed_tangent_domain hm hu
  have htv := last_fixed_tangent_domain hm hv
  have hu0 : 0 < lastFixedPoint i := by linarith [hu.1]
  have hb0 : 0 ≤ lastFixedB / lastFixedPoint i := by unfold lastFixedB; positivity
  have hb26 : lastFixedB / lastFixedPoint i ≤ 26 := by
    apply (div_le_iff₀ hu0).mpr
    norm_num [lastFixedB]
    linarith [hu.1]
  have hex : |-lastFixedPoint (i + 1) / 2 - lastFixedB / lastFixedPoint i| ≤ 256 :=
    abs_le.mpr ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have hsecond := mul_le_mul_of_nonneg_left (Fixed032281.exp_bounds hex).1
    (sub_nonneg.mpr (lastFixedPoint_monotone (Nat.le_succ i)))
  exact (sub_le_sub (SecondLow.affineExpValue_le_upper htu.1 htu.2 htv.2)
    hsecond).trans (Fixed032281.le_roundUp _ _)

theorem originalLastScalar_fixed_rational_reduction :
    originalLastScalar 3100 ≤ lastFixedCoefficient *
      ∑ i ∈ Finset.range 32, lastFixedCellUpper i :=
  originalLastScalar_fixed_partition.trans
    (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun _ hi => lastFixedCellValue_le_upper (Finset.mem_range.mp hi)))
      (by norm_num [lastFixedCoefficient]))

#print axioms originalLastScalar_fixed_rational_reduction

end LiuWang.Proof.Campaign20260915.SecondTerminal
