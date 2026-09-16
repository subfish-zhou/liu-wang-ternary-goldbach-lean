import LiuWang.Proof.Campaign20260915.RosserCount.BacklundCircleBudget

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

def backlundCountBudget (T : ℝ) : ℝ :=
  (backlundCircleBudget T - Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
      (2 * Real.log (44 / 25 : ℝ)) +
    Real.log ‖riemannZeta (5 / 4 : ℂ)‖ / Real.pi +
    4 / (Real.pi * T) + 1 / (4 * Real.pi * T)

theorem backlundCountBudget_continuousAt {T : ℝ} (hT : rsA ≤ T) :
    ContinuousAt backlundCountBudget T := by
  have hT' : 1000 ≤ T := rsA_ge_thousand.trans hT
  have hT0 : T ≠ 0 := by linarith
  have hY : 0 < T + 33 / 25 := by linarith
  have hlogY : Real.log (T + 33 / 25) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hX : (T - 33 / 25) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  have hden : (T - 33 / 25) ^ 2 - 4 ≠ 0 := by nlinarith
  have hz : ContinuousAt (fun t : ℝ => Real.log ‖riemannZeta (backlundCenterPoint t)‖) T := by
    have hs : backlundCenterPoint T ≠ 1 := by
      intro he
      have hre := congrArg Complex.re he
      norm_num [backlundCenterPoint] at hre
    exact (((differentiableAt_riemannZeta hs).continuousAt.comp
      (by unfold backlundCenterPoint; fun_prop)).norm).log
        (norm_ne_zero_iff.mpr (backlundCenter_nonzero T))
  unfold backlundCountBudget backlundCircleBudget
  fun_prop (disch := positivity)

theorem positiveCount_regular_right_plateau {T e : ℝ} (he : 0 < e) :
    ∃ H : ℝ, T < H ∧ H < T + e ∧ positiveCount H = positiveCount T ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → riemannZeta s ≠ 0 := by
  obtain ⟨H, hTH, hHe, hc, _, hr⟩ :=
    LiuWang.Proof.DirichletZeroCount.Applications.exists_common_count_plateau 1
      (y := T) he
  refine ⟨H, hTH, hHe, ?_, ?_⟩
  · have h := hc (1 : LiuWang.Proof.Interfaces.Character 1) 0 H hTH.le le_rfl
    rw [← zetaClosedCount_eq_principal, ← zetaClosedCount_eq_principal,
      zetaClosedCount_eq_two_positiveCount, zetaClosedCount_eq_two_positiveCount] at h
    omega
  · intro s h0 h1 him
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      hr (1 : LiuWang.Proof.Interfaces.Character 1) s h0 h1 him

theorem positiveCount_backlund_closed_numerical_bound {T : ℝ} (hT : rsA ≤ T) :
    |(positiveCount T : ℝ) - rosserMain T| ≤ backlundCountBudget T := by
  let g : ℝ → ℝ := fun t => |(positiveCount T : ℝ) - rosserMain t| - backlundCountBudget t
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1000)
    (rsA_ge_thousand.trans hT)
  have hg : ContinuousAt g T :=
    ((continuousAt_const.sub (rosserMain_hasDerivAt hT0).continuousAt).abs).sub
      (backlundCountBudget_continuousAt hT)
  by_contra hn
  have hpos : 0 < g T := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨e, he, hnear⟩ := Metric.continuousAt_iff.mp hg (g T) hpos
  obtain ⟨H, hTH, hHe, hc, hr⟩ := positiveCount_regular_right_plateau (T := T) he
  have hd : dist H T < e := by rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hTH)]; linarith
  have hclose := hnear hd
  rw [Real.dist_eq] at hclose
  have hbound := positiveCount_backlund_numerical_circle_bound (hT.trans hTH.le) hr
  rw [hc] at hbound
  change |(positiveCount T : ℝ) - rosserMain H| < backlundCountBudget H at hbound
  have hneg : g H < 0 := sub_neg.mpr hbound
  have hlow := (abs_lt.mp hclose).1
  linarith

#print axioms backlundCountBudget_continuousAt
#print axioms positiveCount_regular_right_plateau
#print axioms positiveCount_backlund_closed_numerical_bound

end LiuWang.Proof.Campaign20260915.RosserCount
