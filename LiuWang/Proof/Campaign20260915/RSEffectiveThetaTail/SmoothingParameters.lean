import LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.SaddleIntegral
import LiuWang.Proof.Campaign20260915.Totient.RSEpsilonTerminal

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail

def smoothingStep (L : ℝ) : ℝ := 3 * saddle L * Real.exp (-saddle L)

theorem saddle_exp_small {s : ℝ} (hs : 16 ≤ s) :
    s * Real.exp (-s) ≤ 1 / 2000 := by
  have hp : s ≤ s ^ 3 := by nlinarith [sq_nonneg (s - 1)]
  exact (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans (cubic_exp_tail hs)

theorem smoothingStep_bounds {L : ℝ} (hL : 5000 ≤ L) :
    0 < smoothingStep L ∧ smoothingStep L ≤ 1 / 10 := by
  have hs := saddle_ge_sixteen hL
  have he := saddle_exp_small hs
  unfold smoothingStep
  constructor
  · exact mul_pos (by linarith) (Real.exp_pos _)
  · nlinarith

theorem smoothingStep_cut {L : ℝ} (hL : 5000 ≤ L) :
    1 + (1 : ℝ) * smoothingStep L * Real.exp L < Real.exp L := by
  have hδ := (smoothingStep_bounds hL).2
  have he : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hm := mul_le_mul_of_nonneg_right hδ (Real.exp_pos L).le
  nlinarith

theorem smoothingStep_moment_budget (L : ℝ) :
    (smoothingStep L / 2) ^ (1 + 1 : ℕ) =
      (9 / 4 : ℝ) * saddle L ^ 2 * Real.exp (-2 * saddle L) := by
  unfold smoothingStep
  rw [show (1 + 1 : ℕ) = 2 by rfl, div_pow, mul_pow, mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * -saddle L = -2 * saddle L by ring]
  ring

theorem smoothing_epsilon_small {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 10) :
    rsEpsilon 1 δ ≤ 7 / 6 * δ := by
  have hδ2 : δ ^ 2 ≤ 1 / 100 := by nlinarith
  have hfac : 1 + δ / 2 + δ ^ 2 / 4 ≤ (7 / 6 : ℝ) := by linarith
  have he : rsEpsilon 1 δ = δ * (1 + δ / 2 + δ ^ 2 / 4) := by
    unfold rsEpsilon
    norm_num only [Nat.cast_one, pow_one]
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hfac hδ0).trans_eq (mul_comm _ _)

theorem original_epsilon_lower {x : ℝ} (hx : 5000 ≤ Real.log x) :
    4 * saddle (Real.log x) * Real.exp (-saddle (Real.log x)) ≤ epsilon x := by
  have hL : 0 ≤ Real.log x := by linarith
  have hs := saddle_ge_sixteen hx
  have hsid : Real.log x = rsR * saddle (Real.log x) ^ 2 := by
    rw [saddle_sq hL]
    field_simp [rsR_pos.ne']
  have hroot : 4 * saddle (Real.log x) ≤ Real.sqrt (Real.log x) := by
    have hl := mul_le_mul_of_nonneg_right (show (16 : ℝ) ≤ rsR by
      linarith [rsR_interval.1]) (sq_nonneg (saddle (Real.log x)))
    have he := Real.sq_sqrt hL
    have hn := Real.sqrt_nonneg (Real.log x)
    nlinarith
  exact mul_le_mul_of_nonneg_right hroot (Real.exp_pos _).le

theorem smoothing_epsilon_reserve {x : ℝ} (hx : 5000 ≤ Real.log x) :
    rsEpsilon 1 (smoothingStep (Real.log x)) ≤ (7 / 8 : ℝ) * epsilon x := by
  have hδ := smoothingStep_bounds hx
  have he := smoothing_epsilon_small hδ.1.le hδ.2
  have hl := original_epsilon_lower hx
  unfold smoothingStep at he ⊢
  nlinarith

theorem integral_budget_reserve {L : ℝ} (hL : 5000 ≤ L) :
    2 * (rsQ (spectralCutoff L) *
      (∫ t in Ioi (spectralCutoff L), rsPhi 1 L t * Real.log (t / (2 * Real.pi)))) +
      (9 / 10 : ℝ) * saddle L ^ 2 * Real.exp (-2 * saddle L) ≤
        (smoothingStep L / 2) ^ (1 + 1 : ℕ) := by
  have h := Q_phi_integral_selected_cutoff hL
  have hn : 0 ≤ saddle L ^ 2 * Real.exp (-2 * saddle L) := by positivity
  rw [smoothingStep_moment_budget]
  nlinarith

#print axioms smoothingStep_cut
#print axioms smoothingStep_moment_budget
#print axioms smoothing_epsilon_reserve
#print axioms integral_budget_reserve

end LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail
