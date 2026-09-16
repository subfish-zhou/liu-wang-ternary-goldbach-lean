import LiuWang.Proof.Campaign20260915.ZetaWinding.LehmanShift
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped ComplexOrder

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaWinding

def realLogZeta (x : ℝ) : ℝ := Real.log ‖riemannZeta (x : ℂ)‖

def realLogTail (a : ℝ) : ℝ := ∫ x in Set.Ioi a, realLogZeta x

theorem norm_zeta_real_eq_tsum_norm {x : ℝ} (hx : 1 < x) :
    ‖riemannZeta (x : ℂ)‖ =
      ∑' n : ℕ, ‖LSeries.term 1 (x : ℂ) n‖ := by
  have hs := LSeriesSummable_one_iff.mpr (show 1 < (x : ℂ).re by simpa using hx)
  have hp (n : ℕ) : 0 ≤ LSeries.term 1 (x : ℂ) n :=
    LSeries.term_nonneg (by norm_num) x
  have hn : 0 ≤ ∑' n : ℕ, LSeries.term 1 (x : ℂ) n := tsum_nonneg hp
  rw [← LSeries_one_eq_riemannZeta (by simpa using hx), LSeries,
    ← Complex.re_eq_norm.mpr hn, Complex.re_tsum hs]
  exact tsum_congr fun n => Complex.re_eq_norm.mpr (hp n)

theorem norm_zeta_le_real {s : ℂ} {x : ℝ} (hx : 1 < x) (hxs : x ≤ s.re) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta (x : ℂ)‖ := by
  have hs := LSeriesSummable_one_iff.mpr (hx.trans_le hxs)
  have hx' := LSeriesSummable_one_iff.mpr (show 1 < (x : ℂ).re by simpa using hx)
  rw [norm_zeta_real_eq_tsum_norm hx, ← LSeries_one_eq_riemannZeta (hx.trans_le hxs)]
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    (hs.norm.tsum_le_tsum
      (LSeries.norm_term_le_of_re_le_re _ (by simpa using hxs)) hx'.norm)

theorem one_le_norm_zeta_real {x : ℝ} (hx : 1 < x) :
    1 ≤ ‖riemannZeta (x : ℂ)‖ := by
  rw [norm_zeta_real_eq_tsum_norm hx]
  have hs := LSeriesSummable_one_iff.mpr (show 1 < (x : ℂ).re by simpa using hx)
  simpa using hs.norm.le_tsum 1 (fun _ _ => norm_nonneg _)

theorem realLogZeta_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ realLogZeta x :=
  Real.log_nonneg (one_le_norm_zeta_real hx)

theorem realLogZeta_antitone : AntitoneOn realLogZeta (Set.Ioi 1) := by
  intro x hx y hy hxy
  exact Real.log_le_log
    (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hy)))
    (norm_zeta_le_real hx (by simpa using hxy))

theorem horizontal_log_continuousOn (T : ℝ) :
    ContinuousOn (fun x => Real.log ‖riemannZeta (horizontalAt T x)‖) (Set.Ioi 1) := by
  intro x hx
  have hs : 1 < (horizontalAt T x).re := by simpa [horizontalAt] using hx
  have hn : horizontalAt T x ≠ 1 := by
    intro h
    simp [h] at hs
  exact (((differentiableAt_riemannZeta hn).continuousAt.comp
    (show ContinuousAt (horizontalAt T) x by unfold horizontalAt; fun_prop)).norm.log
      (norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs))).continuousWithinAt

theorem horizontal_log_intervalIntegrable (T : ℝ) {a b : ℝ}
    (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun x => Real.log ‖riemannZeta (horizontalAt T x)‖) volume a b :=
  ((horizontal_log_continuousOn T).mono (by
    intro x hx
    exact lt_of_lt_of_le (lt_min ha hb) hx.1)).intervalIntegrable

theorem realLogZeta_intervalIntegrable {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable realLogZeta volume a b := by
  change IntervalIntegrable (fun x => Real.log ‖riemannZeta (x : ℂ)‖) volume a b
  simpa [horizontalAt] using horizontal_log_intervalIntegrable 0 ha hb

theorem horizontal_log_integrable_right (T : ℝ) {a : ℝ} (ha : 1 < a) :
    IntegrableOn (fun x => Real.log ‖riemannZeta (horizontalAt T x)‖) (Set.Ioi a) := by
  have hr : IntegrableOn (fun x => Real.log ‖riemannZeta (horizontalAt T x)‖)
      (Set.Ioi (max a 2)) := by
    simpa only [RCLike.re_to_complex, log_re] using!
      (log_zeta_right_integrable T (le_max_right a 2)).re
  have hf := (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_max_left a 2)).mp
    (horizontal_log_intervalIntegrable T ha (ha.trans_le (le_max_left a 2)))
  rw [← Set.Ioc_union_Ioi_eq_Ioi (le_max_left a 2)]
  exact hf.union hr

theorem realLogZeta_integrable_right {a : ℝ} (ha : 1 < a) :
    IntegrableOn realLogZeta (Set.Ioi a) := by
  change IntegrableOn (fun x : ℝ => Real.log ‖riemannZeta (x : ℂ)‖) (Set.Ioi a)
  simpa [horizontalAt] using horizontal_log_integrable_right 0 ha

theorem realLogTail_nonneg {a : ℝ} (ha : 1 < a) : 0 ≤ realLogTail a :=
  setIntegral_nonneg measurableSet_Ioi (fun _ hx => realLogZeta_nonneg (ha.trans hx))

theorem realLogTail_split {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    realLogTail a = (∫ x in a..b, realLogZeta x) + realLogTail b :=
  (intervalIntegral.integral_interval_add_Ioi
    (realLogZeta_integrable_right ha) (realLogZeta_integrable_right hb)).symm

theorem horizontal_log_le_real (T : ℝ) {x : ℝ} (hx : 1 < x) :
    Real.log ‖riemannZeta (horizontalAt T x)‖ ≤ realLogZeta x :=
  Real.log_le_log
    (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa [horizontalAt] using hx)))
    (norm_zeta_le_real hx (by simp [horizontalAt]))

theorem real_log_ratio_le_horizontal (T : ℝ) {x : ℝ} (hx : 1 < x) :
    realLogZeta (2 * x) - realLogZeta x ≤
      Real.log ‖riemannZeta (horizontalAt T x)‖ := by
  have h2x : 1 < 2 * x := by linarith
  have hn : riemannZeta (x : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hx)
  have hn2 : riemannZeta (2 * (x : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using h2x)
  have h := Real.log_le_log (norm_pos_iff.mpr (div_ne_zero hn2 hn))
    (norm_riemannZeta_ratio_le_on_verticalLine x T hx)
  simpa [norm_div, Real.log_div (norm_ne_zero_iff.mpr hn2) (norm_ne_zero_iff.mpr hn),
    realLogZeta, horizontalAt, verticalLine] using h

theorem horizontal_log_tail_le_real (T : ℝ) {a : ℝ} (ha : 1 < a) :
    (∫ x in Set.Ioi a, Real.log ‖riemannZeta (horizontalAt T x)‖) ≤ realLogTail a :=
  setIntegral_mono_on (horizontal_log_integrable_right T ha)
    (realLogZeta_integrable_right ha) measurableSet_Ioi
    (fun _ hx => horizontal_log_le_real T (ha.trans hx))

theorem real_log_tail_ratio_le_horizontal (T : ℝ) {a : ℝ} (ha : 1 < a) :
    realLogTail (2 * a) / 2 - realLogTail a ≤
      ∫ x in Set.Ioi a, Real.log ‖riemannZeta (horizontalAt T x)‖ := by
  have hi : IntegrableOn (fun x => realLogZeta (2 * x)) (Set.Ioi a) :=
    (integrableOn_Ioi_comp_mul_left_iff realLogZeta a (by norm_num : (0 : ℝ) < 2)).mpr
      (realLogZeta_integrable_right (by linarith))
  have h := setIntegral_mono_on (hi.sub (realLogZeta_integrable_right ha))
    (horizontal_log_integrable_right T ha) measurableSet_Ioi
    (fun _ hx => real_log_ratio_le_horizontal T (ha.trans hx))
  simp only [Pi.sub_apply] at h
  rw [integral_sub hi (realLogZeta_integrable_right ha),
    integral_comp_mul_left_Ioi realLogZeta a (by norm_num : (0 : ℝ) < 2)] at h
  simpa [realLogTail, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem real_log_interval_ratio_le_horizontal (T : ℝ) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in (2 * a)..(2 * b), realLogZeta x) / 2 -
        (∫ x in a..b, realLogZeta x) ≤
      ∫ x in a..b, Real.log ‖riemannZeta (horizontalAt T x)‖ := by
  have hb := ha.trans_le hab
  have hi : IntervalIntegrable (fun x => realLogZeta (2 * x)) volume a b := by
    have h := (realLogZeta_intervalIntegrable
      (by linarith : 1 < 2 * a) (by linarith : 1 < 2 * b)).comp_mul_left (c := 2)
    simpa using h
  have h := intervalIntegral.integral_mono_on hab
    (hi.sub (realLogZeta_intervalIntegrable ha hb))
    (horizontal_log_intervalIntegrable T ha hb)
    (fun x hx => real_log_ratio_le_horizontal T (ha.trans_le hx.1))
  rw [intervalIntegral.integral_sub hi (realLogZeta_intervalIntegrable ha hb),
    intervalIntegral.integral_comp_mul_left realLogZeta (by norm_num : (2 : ℝ) ≠ 0)] at h
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem realLogZeta_integral_bounds {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) * realLogZeta b ≤ (∫ x in a..b, realLogZeta x) ∧
      (∫ x in a..b, realLogZeta x) ≤ (b - a) * realLogZeta a := by
  have hb := ha.trans_le hab
  have hi := realLogZeta_intervalIntegrable ha hb
  constructor
  · simpa using intervalIntegral.integral_mono_on hab intervalIntegrable_const hi
      (fun x hx => realLogZeta_antitone (ha.trans_le hx.1) hb hx.2)
  · simpa using intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
      (fun x hx => realLogZeta_antitone ha (ha.trans_le hx.1) hx.1)

#print axioms norm_zeta_le_real
#print axioms real_log_tail_ratio_le_horizontal
#print axioms real_log_interval_ratio_le_horizontal
#print axioms realLogZeta_integral_bounds

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
