import LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.PositiveKernel
import LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.CutoffBudget
import LiuWang.Proof.Campaign20260915.RosserCount.OriginalCountConsumers

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.RosserCount
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel

theorem positive_tail_A_lt_exp :
    (∑' p, rsPositivePhiTerm rsA 1 0 p) < Real.exp (-9.61) := by
  have h := rosser_positive_inverse_square_tail (le_refl rsA)
  have hb := original_boundary_integral_budget
  rw [(unweighted_phi_integral (le_refl rsA)).2] at hb
  unfold rosserError at h
  exact h.trans (by convert hb using 1 <;> ring)

theorem two_sided_tail_lt_rosser {K : ℝ} (hK : rsA ≤ K) :
    (∑' p, rsHighTerm K 1 0 p) <
      4 * rosserError K / K ^ 2 +
        0.3184 * (1 + Real.log (K / (2 * Real.pi))) / K := by
  rw [zero_weight_tail_eq_two_positive hK]
  have h := mul_lt_mul_of_pos_left (rosser_positive_inverse_square_tail hK)
    (by norm_num : (0 : ℝ) < 2)
  exact h.trans_eq (by ring)

theorem positive_tail_A_lt_rational :
    (∑' p, rsPositivePhiTerm rsA 1 0 p) < (7 / 100000 : ℝ) := by
  have he := exp_neg_budget (a := 9.61) (c := 100000 / 7) 9
    (r := 61 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact positive_tail_A_lt_exp.trans_le (by convert he using 1 <;> norm_num)

theorem two_sided_tail_A_lt_rational :
    (∑' p, rsHighTerm rsA 1 0 p) < (7 / 50000 : ℝ) := by
  rw [zero_weight_tail_eq_two_positive (le_refl rsA)]
  linarith [positive_tail_A_lt_rational]

/-- All unbounded spectral tails are paid; only the actual finite closed window remains. -/
theorem originalK_paid_tail {x K : ℝ} (hx : 1 ≤ x) (hK : rsA ≤ K) :
    originalK 1 x <
      (∑' p, closedMomentTerm rsA (Real.log x) p) +
        Real.exp (-9.61) / Real.sqrt x +
          Real.exp (-9.61) * x ^ (-(1 / (rsR * Real.log K))) +
            2 * rosserError K / K ^ 2 +
              0.1592 * (1 + Real.log (K / (2 * Real.pi))) / K := by
  have hs := originalK_positive_cutoff hx hK
  have hA := positive_tail_A_lt_exp
  have hT := rosser_positive_inverse_square_tail hK
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hdiv := div_lt_div_of_pos_right hA hsqrt
  have hpow : 0 ≤ x ^ (-(1 / (rsR * Real.log K))) :=
    Real.rpow_nonneg (by linarith) _
  have hmul := mul_le_mul_of_nonneg_left hA.le hpow
  nlinarith

theorem originalK_one_lt_closed_add_rational :
    originalK 1 1 < (∑' p, closedMomentTerm rsA 0 p) + 7 / 50000 := by
  rw [originalK_eq_moment 1 (by norm_num), Real.log_one, actual_moment_split (le_refl 0)]
  exact add_lt_add_left two_sided_tail_A_lt_rational _

#print axioms positive_tail_A_lt_exp
#print axioms two_sided_tail_lt_rosser
#print axioms originalK_paid_tail
#print axioms originalK_one_lt_closed_add_rational

end LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel
