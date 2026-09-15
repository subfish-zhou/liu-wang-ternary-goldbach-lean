import LiuWang.Proof.PerronRecovery.Psi
import LiuWang.Proof.NonprincipalExpansion.Consumer

/-! Actual closed-window oscillation consumes the recovered nonprincipal psi.
The first output retains pi, both Abel endpoints and the half in integral t. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace LiuWang.Proof.PerronRecovery

open Interfaces Parameters FixedHeightZeroSum NonprincipalExpansion

def oscillatoryError (N : ℕ) (eta : ℝ) : ℝ :=
  (0.961616 / sourceT N * sourceL N ^ 2) * ((N : ℝ) + sourceWindowLower N) +
    Real.pi * |eta| * (0.961616 / sourceT N * sourceL N ^ 2) *
      ((N : ℝ) ^ 2 - sourceWindowLower N ^ 2) + sourceL N

theorem nonprincipal_oscillation_function {N q : ℕ} [NeZero q]
    (chi : Character q) (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (hchi : chi ≠ 1) (eta : ℝ) :
    ‖S_chi N chi eta +
      ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) eta‖ ≤
      oscillatoryError N eta := by
  have hF : ∀ t ∈ Set.Icc (sourceWindowLower N) (N : ℝ),
      ‖ExplicitPerron.psi chi t + highZeroSum chi t (sourceT N)‖ ≤
        (0.961616 / sourceT N * sourceL N ^ 2) * t := by
    intro t ht
    convert nonprincipal_psi_le chi hN hqUpper hchi ht.1 ht.2 using 1
    ring
  rw [expansion_error_identity (nat_pos_of_exp_le hN) hchi]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_abelTransform_le N eta _ hF) (norm_lowerTerm_le_log hN chi eta))

theorem oscillatoryError_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (eta : ℝ) :
    oscillatoryError N eta ≤
      (0.96258 + 3.02102 * (N : ℝ) * |eta|) * (N : ℝ) / sourceT N * sourceL N ^ 2 := by
  have hT0 := sourceT_pos hN
  have hscale : 0 ≤ (N : ℝ) / sourceT N * sourceL N ^ 2 := by positivity
  have hquad : 0 ≤ (N : ℝ) ^ 2 - sourceWindowLower N ^ 2 := by
    have := lower_le N
    have := lower_nonneg N
    nlinarith
  have hpi :
      Real.pi * |eta| * (0.961616 / sourceT N * sourceL N ^ 2) *
          ((N : ℝ) ^ 2 - sourceWindowLower N ^ 2) ≤
        3.1416 * |eta| * (0.961616 / sourceT N * sourceL N ^ 2) * (N : ℝ) ^ 2 := by
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right Real.pi_lt_d4.le (abs_nonneg eta))
        (by positivity)) hquad).trans
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) (by positivity)
  calc
    _ ≤ (0.961616 / sourceT N * sourceL N ^ 2) * ((N : ℝ) + sourceWindowLower N) +
        3.1416 * |eta| * (0.961616 / sourceT N * sourceL N ^ 2) * (N : ℝ) ^ 2 +
        0.000001 * (N : ℝ) / sourceT N * sourceL N ^ 2 :=
      add_le_add (add_le_add le_rfl hpi) (lowerTerm_cost_source_le hN)
    _ = (0.962578616 + 3.0210128256 * (N : ℝ) * |eta|) *
        ((N : ℝ) / sourceT N * sourceL N ^ 2) := by
      unfold sourceWindowLower
      ring
    _ ≤ _ := by
      have hcoef : 0.962578616 + 3.0210128256 * (N : ℝ) * |eta| ≤
          0.96258 + 3.02102 * (N : ℝ) * |eta| := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg eta)]
      simpa only [mul_assoc, mul_div_assoc] using mul_le_mul_of_nonneg_right hcoef hscale

theorem nonprincipal_oscillation_le {N q : ℕ} [NeZero q]
    (chi : Character q) (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (hchi : chi ≠ 1) (eta : ℝ) :
    ‖S_chi N chi eta +
      ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) eta‖ ≤
      (0.96258 + 3.02102 * (N : ℝ) * |eta|) * (N : ℝ) / sourceT N * sourceL N ^ 2 :=
  (nonprincipal_oscillation_function chi hN hqUpper hchi eta).trans (oscillatoryError_le hN eta)

end LiuWang.Proof.PerronRecovery
