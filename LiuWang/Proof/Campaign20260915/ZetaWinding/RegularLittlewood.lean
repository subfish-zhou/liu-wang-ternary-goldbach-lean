import LiuWang.Proof.Campaign20260915.ZetaWinding.RegularDerivative

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

theorem log_zeta_horizontal_hasDerivAt {T x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt (fun u => log (riemannZeta (horizontalAt T u)))
      (logDeriv riemannZeta (horizontalAt T x)) x := by
  simpa [horizontalAt, Function.comp_def, smul_eq_mul] using
    (log_zeta_hasDerivAt_right (s := horizontalAt T x) (by simpa [horizontalAt] using hx)).scomp x
      ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((T : ℂ) * I))

theorem integral_logDeriv_two_three (T : ℝ) :
    (∫ x in (2 : ℝ)..3, logDeriv riemannZeta (horizontalAt T x)) =
      log (riemannZeta (horizontalAt T 3)) - log (riemannZeta (horizontalAt T 2)) := by
  have hi : IntervalIntegrable (fun x => logDeriv riemannZeta (horizontalAt T x)) volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx' : 2 ≤ x := by
      rw [Set.uIcc_of_le (by norm_num)] at hx
      exact hx.1
    have hn : horizontalAt T x ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp [horizontalAt] at hr
      linarith
    have ha := LiuWang.Proof.PrincipalPsi.analytic_zeta_of_ne_one hn
    have hz := riemannZeta_ne_zero_of_one_le_re
      (s := horizontalAt T x) (by simp [horizontalAt]; linarith)
    exact ((ha.deriv.continuousAt.div ha.continuousAt hz).comp
      (f := horizontalAt T) (by unfold horizontalAt; fun_prop)).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => log_zeta_horizontal_hasDerivAt (by
      rw [Set.uIcc_of_le (by norm_num)] at hx; exact hx.1)) hi

theorem horizontalLogMass_hasDerivAt_turingS {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    HasDerivAt horizontalLogMass (Real.pi * turingS T) T := by
  have hd := (horizontalLogMass_hasDerivAt_integral hT hr).2
  have hz : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 3, riemannZeta (horizontalAt T x) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact zeta_horizontal_regular hT hr hx.1
  have hi := zeta_logDeriv_horizontal_integrable hT.ne' hz
  have ht := logDeriv_tail_integrable T (le_refl 3)
  have he := intervalIntegral.integral_interval_add_Ioi' hi ht
  have htwo : (2 : ℝ) ∈ Set.uIcc (1 / 2 : ℝ) 3 := by norm_num [Set.uIcc_of_le]
  have hi1 := hi.mono (Set.uIcc_subset_uIcc Set.left_mem_uIcc htwo) le_rfl
  have hi2 := hi.mono (Set.uIcc_subset_uIcc htwo Set.right_mem_uIcc) le_rfl
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [← hadd, integral_logDeriv_two_three, integral_logDeriv_right T (le_refl 3)] at he
  have hfull : IntegrableOn (fun x => logDeriv riemannZeta (horizontalAt T x))
      (Set.Ioi (1 / 2 : ℝ)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (show (1 / 2 : ℝ) ≤ 3 by norm_num)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hi).union ht
  have he' : (∫ x in Set.Ioi (1 / 2 : ℝ), logDeriv riemannZeta (horizontalAt T x)) =
      HIntegral (logDeriv riemannZeta) (1 / 2) 2 T - log (riemannZeta (horizontalAt T 2)) := by
    rw [← he]
    change _ = (∫ x in (1 / 2 : ℝ)..2, logDeriv riemannZeta (horizontalAt T x)) - _
    ring
  have him := integral_im hfull
  simp only [RCLike.im_to_complex] at him
  rw [integral_neg, him, he', sub_im] at hd
  have hp := turingS_eq_horizontal_logDeriv hT hr
  simp only [sub_im] at hp
  convert! hd using 1
  linarith

theorem littlewood_on_regular_interval {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hr : ∀ t ∈ Set.Icc u v, ∀ s : ℂ,
      0 < s.re → s.re < 1 → |s.im| = t → riemannZeta s ≠ 0) :
    Real.pi * (∫ t in u..v, turingS t) = horizontalLogMass v - horizontalLogMass u := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := horizontalLogMass) _ ((turingS_intervalIntegrable u v).const_mul _)
  intro t ht
  rw [Set.uIcc_of_le huv] at ht
  exact horizontalLogMass_hasDerivAt_turingS (hu.trans_le ht.1) (hr t ht)

#print axioms horizontalLogMass_hasDerivAt_turingS
#print axioms littlewood_on_regular_interval

end LiuWang.Proof.Campaign20260915.ZetaWinding
