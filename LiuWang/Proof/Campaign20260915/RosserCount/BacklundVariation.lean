import LiuWang.Proof.Campaign20260915.RosserCount.BacklundPhaseLift
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.ArgumentVariation

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex Filter Metric MeasureTheory MeromorphicOn
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

def backlundSmallSupport (T : ℝ) (n : ℕ) : Finset ℂ :=
  ((divisor (backlundAux T n) (closedBall 0 (3 / 4 : ℝ))).finiteSupport
    (isCompact_closedBall (0 : ℂ) (3 / 4 : ℝ))).toFinset

theorem backlundAux_small_divisor_pos_of_zero {T : ℝ} (hT : rsA ≤ T) {n : ℕ}
    (hn : backlundAux T n 0 ≠ 0) {z : ℂ}
    (hz : z ∈ closedBall 0 (3 / 4 : ℝ)) (hzero : backlundAux T n z = 0) :
    0 < divisor (backlundAux T n) (closedBall 0 (3 / 4 : ℝ)) z := by
  have ha := (backlundAux_analyticOnNhd hT n).mono
    (closedBall_subset_closedBall (by norm_num : (3 / 4 : ℝ) ≤ 33 / 25))
  have h0 : (0 : ℂ) ∈ closedBall 0 (3 / 4 : ℝ) := by norm_num
  have hfinite := ha.analyticOrderAt_ne_top_of_isPreconnected
    (convex_closedBall (0 : ℂ) (3 / 4 : ℝ)).isPreconnected h0 hz
    (by rw [(ha 0 h0).analyticOrderAt_eq_zero.mpr hn]; simp)
  have hnat : 0 < analyticOrderNatAt (backlundAux T n) z := by
    apply Nat.pos_of_ne_zero
    intro he
    have ho : analyticOrderAt (backlundAux T n) z = 0 := by
      rw [← Nat.cast_analyticOrderNatAt hfinite, he, Nat.cast_zero]
    exact ((ha z hz).analyticOrderAt_eq_zero.mp ho) hzero
  rw [ha.divisor_apply hz, ← Nat.cast_analyticOrderNatAt hfinite]
  simpa using (show (0 : ℤ) < (analyticOrderNatAt (backlundAux T n) z : ℤ) by
    exact_mod_cast hnat)

theorem backlundSmallSupport_card_le_divisor {T : ℝ} (hT : rsA ≤ T) (n : ℕ) :
    ((backlundSmallSupport T n).card : ℝ) ≤
      ∑ᶠ z, (divisor (backlundAux T n) (closedBall 0 (3 / 4 : ℝ)) z : ℝ) := by
  classical
  let D := divisor (backlundAux T n) (closedBall 0 (3 / 4 : ℝ))
  have ha := (backlundAux_analyticOnNhd hT n).mono
    (closedBall_subset_closedBall (by norm_num : (3 / 4 : ℝ) ≤ 33 / 25))
  have he : (∑ᶠ z, (D z : ℝ)) = ∑ z ∈ backlundSmallSupport T n, (D z : ℝ) := by
    apply finsum_eq_sum_of_support_subset
    intro z hz
    apply (D.finiteSupport (isCompact_closedBall ..)).mem_toFinset.mpr
    simp only [Function.mem_support, ne_eq, Int.cast_eq_zero] at hz ⊢
    exact hz
  change _ ≤ ∑ᶠ z, (D z : ℝ)
  rw [he]
  calc
    _ = ∑ _z ∈ backlundSmallSupport T n, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro z hz
      have hne : D z ≠ 0 :=
        (D.finiteSupport (isCompact_closedBall ..)).mem_toFinset.mp hz
      have hnon : (0 : ℤ) ≤ D z := ha.divisor_nonneg z
      exact_mod_cast (by omega : (1 : ℤ) ≤ D z)

theorem backlundAux_phase_variation_divisor {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {n : ℕ} (hn : backlundAux T n 0 ≠ 0) :
    (n : ℝ) * |(backlundLog T (5 / 4)).im - (backlundLog T (1 / 2)).im| ≤
      ((∑ᶠ z, (divisor (backlundAux T n) (closedBall 0 (3 / 4 : ℝ)) z : ℝ)) + 1) *
        Real.pi := by
  have hpos : 0 < T := by linarith [rsA_ge_thousand]
  let A : ℝ → ℝ := fun t => (n : ℝ) * (backlundLog T (t + 5 / 4)).im
  have hc : ContinuousOn A (Set.Icc (-3 / 4 : ℝ) 0) := by
    apply continuousOn_const.mul
    apply Complex.continuous_im.comp_continuousOn
    apply (backlundLog_continuousOn hpos hr).comp (by fun_prop)
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hS : ∀ t ∈ Set.Icc (-3 / 4 : ℝ) 0, Real.cos (A t) = 0 →
      (t : ℂ) ∈ backlundSmallSupport T n := by
    intro t ht hc0
    change Real.cos ((n : ℝ) * (backlundLog T (t + 5 / 4)).im) = 0 at hc0
    have hx : t + 5 / 4 ∈ Set.Icc (1 / 2 : ℝ) 2 := by
      constructor <;> linarith [ht.1, ht.2]
    have he := backlundAux_phase_formula hpos hr hx n
    have hz : backlundAux T n (t : ℂ) = 0 := by
      simpa only [add_sub_cancel_right, hc0, mul_zero, ofReal_zero] using he
    have hball : (t : ℂ) ∈ closedBall 0 (3 / 4 : ℝ) := by
      simp only [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos ht.2]
      linarith [ht.1]
    apply ((divisor (backlundAux T n) (closedBall 0 (3 / 4 : ℝ))).finiteSupport
      (isCompact_closedBall ..)).mem_toFinset.mpr
    exact (backlundAux_small_divisor_pos_of_zero hT hn hball hz).ne'
  have hv := argument_variation_le (by norm_num : (-3 / 4 : ℝ) ≤ 0) hc
    (backlundSmallSupport T n) hS
  have he : A 0 - A (-3 / 4) =
      (n : ℝ) * ((backlundLog T (5 / 4)).im - (backlundLog T (1 / 2)).im) := by
    dsimp [A]
    norm_num
    ring
  rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at hv
  exact hv.trans (mul_le_mul_of_nonneg_right
    (by linarith [backlundSmallSupport_card_le_divisor hT n]) Real.pi_pos.le)

theorem backlund_phase_variation_envelope {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |(backlundLog T (5 / 4)).im - (backlundLog T (1 / 2)).im| ≤
      ((Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) / Real.log (44 / 25 : ℝ)) *
        Real.pi := by
  obtain ⟨f, hf, hfn, hl⟩ := backlundAux_center_log_limit T
  have hq : 0 < Real.log (44 / 25 : ℝ) := Real.log_pos (by norm_num)
  have hinv : Tendsto (fun n => (1 : ℝ) / (f n : ℝ)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun n => (f n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hf
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hcast
  have ht := ((((tendsto_const_nhds
    (x := Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ))).sub hl).div_const
      (Real.log (44 / 25 : ℝ))).add hinv).mul_const Real.pi
  simp only [add_zero] at ht
  apply ge_of_tendsto ht
  filter_upwards [hf.eventually (eventually_ge_atTop 1)] with k hk
  have hp : (0 : ℝ) < f k := by exact_mod_cast (by omega : 0 < f k)
  have hv := backlundAux_phase_variation_divisor hT hr (hfn k)
  have hb := backlundAux_divisor_envelope_bound hT (hfn k)
  calc
    _ ≤ (((∑ᶠ z, (divisor (backlundAux T (f k)) (closedBall 0 (3 / 4 : ℝ)) z : ℝ)) + 1) *
        Real.pi) / (f k : ℝ) := by
      apply (le_div_iff₀ hp).mpr
      nlinarith only [hv]
    _ ≤ ((((f k : ℝ) * Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖backlundAux T (f k) 0‖) / Real.log (44 / 25 : ℝ) + 1) *
        Real.pi) / (f k : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hb]) Real.pi_pos.le) hp.le
    _ = _ := by
      field_simp

theorem positiveCount_centered_envelope_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |Real.pi * ((positiveCount T : ℝ) - rosserMain T) -
      rosserGammaRemainder T - (backlundLog T (5 / 4)).im| ≤
      ((Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) / Real.log (44 / 25 : ℝ)) *
        Real.pi := by
  have hpos : 0 < T := by linarith [rsA_ge_thousand]
  rw [positiveCount_error_backlundLog hpos hr]
  have he : rosserGammaRemainder T + (backlundLog T (1 / 2)).im -
      rosserGammaRemainder T - (backlundLog T (5 / 4)).im =
      (backlundLog T (1 / 2)).im - (backlundLog T (5 / 4)).im := by ring
  rw [he, abs_sub_comm]
  exact backlund_phase_variation_envelope hT hr

#print axioms backlundAux_small_divisor_pos_of_zero
#print axioms backlundSmallSupport_card_le_divisor
#print axioms backlundAux_phase_variation_divisor
#print axioms backlund_phase_variation_envelope
#print axioms positiveCount_centered_envelope_bound

end LiuWang.Proof.Campaign20260915.RosserCount
