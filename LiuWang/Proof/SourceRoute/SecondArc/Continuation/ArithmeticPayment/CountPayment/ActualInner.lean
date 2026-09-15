import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.StrongPacket
import LiuWang.Proof.DirichletZeroCount.Remainder.SourceFamily

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Remainder

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment

def densityGate (q : ℕ) : ℝ := max (100000 / (q : ℝ)) (10000 * Real.log q)

def lowHeightIntegral (N q : ℕ) [NeZero q] : ℝ :=
  ∫ y in omegaCutoff N q..densityGate q, heightKernel y *
    ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
      alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)

theorem actual_inner_reversed {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ}
    (ha : stripLower q y ≤ 59 / 60) :
    (∫ alpha in (59 / 60 : ℝ)..stripLower q y,
      alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤ 0 := by
  rw [intervalIntegral.integral_symm]
  apply neg_nonpos.mpr
  apply intervalIntegral.integral_nonneg_of_forall ha
  intro alpha
  have hh := Real.log_nonneg (window_base_ge_one hN)
  unfold alphaKernel
  positivity

theorem actual_inner_le_count_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y M : ℝ} (hM : 0 ≤ M)
    (hcount : ∀ alpha, 59 / 60 ≤ alpha → (familyCount q alpha y : ℝ) ≤ M) :
    (∫ alpha in (59 / 60 : ℝ)..stripLower q y,
      alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      M * Real.exp (-0.478 * Real.log (0.001 * (N : ℝ)) / Real.log ((q : ℝ) * y)) := by
  by_cases ha : stripLower q y ≤ 59 / 60
  · exact (actual_inner_reversed hN ha).trans (by positivity)
  have hab := le_of_lt (lt_of_not_ge ha)
  have hNp := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have hi := intervalIntegral.integral_mono_on hab (count_alpha_integrable hx hab y)
    (((continuous_alphaKernel hx).const_mul M).intervalIntegrable _ _)
    (fun alpha halpha => (mul_le_mul_of_nonneg_left (hcount alpha halpha.1)
      (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg (window_base_ge_one hN)))).trans_eq
        (mul_comm _ _))
  rw [intervalIntegral.integral_const_mul, integral_alphaKernel hx] at hi
  have hp : (0.001 * (N : ℝ)) ^ (stripLower q y - 1) =
      Real.exp (-0.478 * Real.log (0.001 * (N : ℝ)) / Real.log ((q : ℝ) * y)) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    unfold stripLower
    ring
  rw [hp] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left
    (sub_le_self _ (Real.rpow_nonneg hx.le _)) hM)

theorem actual_inner_le_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : 0 ≤ y) :
    (∫ alpha in (59 / 60 : ℝ)..stripLower q y,
      alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      sourceModulusFamilyBound q y *
        Real.exp (-0.478 * Real.log (0.001 * (N : ℝ)) / Real.log ((q : ℝ) * y)) := by
  have hc (alpha : ℝ) (ha : 0 ≤ alpha) :=
    (familyCount_le_source q ha hy).trans (sourceFamilyBound_le_modulus q hy)
  exact actual_inner_le_count_bound hN
    ((Nat.cast_nonneg (familyCount q 0 y)).trans (hc 0 le_rfl))
    (fun alpha ha => hc alpha (by linarith))

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
