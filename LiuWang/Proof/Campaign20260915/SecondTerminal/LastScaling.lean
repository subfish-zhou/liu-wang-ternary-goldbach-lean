import LiuWang.Proof.Campaign20260915.SecondTerminal.SignedCells
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

theorem shifted_phase_gain_forty {H H₀ t y k : ℝ} (hH₀ : 3093 ≤ H₀)
    (ht : 1 ≤ t) (hH : H₀ * t ≤ H) (hy : 20 ≤ y) (hy60 : y ≤ 60)
    (hk : 0 ≤ k) (hk7 : k ≤ 7) :
    H₀ / y + 40 * Real.log t ≤ H / (y + k * Real.log t) := by
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < y := by linarith
  have hh := shifted_height_bounds ht hy hk hk7
  have hl := Real.log_nonneg ht
  have hcoef : 7 * H₀ + 40 * y ^ (2 : ℕ) ≤ H₀ * y := by
    have h1 := mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hy60)
    have h2 := mul_nonneg (sub_nonneg.mpr hH₀) (show 0 ≤ y - 7 by linarith)
    nlinarith only [h1, h2, hy60]
  have hquad : 280 * y ≤ H₀ * y / 2 := by
    have hp := mul_nonneg (show 0 ≤ H₀ / 2 - 280 by linarith) hy0.le
    nlinarith only [hp]
  have he := Real.quadratic_le_exp_of_nonneg hl
  rw [Real.exp_log ht0] at he
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ H₀ * y by positivity)
  have hlin := mul_le_mul_of_nonneg_right hcoef hl
  have hquadratic := mul_le_mul_of_nonneg_right hquad (sq_nonneg (Real.log t))
  have hbase : (H₀ / y + 40 * Real.log t) * (y + 7 * Real.log t) ≤ H₀ * t := by
    apply (mul_le_mul_iff_right₀ hy0).mp
    field_simp
    nlinarith only [hm, hlin, hquadratic]
  apply (le_div_iff₀ hh.1).mpr
  apply le_trans _ (hbase.trans hH)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  gcongr

theorem exp_difference_integral (s a b : ℝ) :
    (∫ c in a..b, s * Real.exp (-c * s)) =
      Real.exp (-a * s) - Real.exp (-b * s) := by
  have hd (c : ℝ) : HasDerivAt (fun c : ℝ => -Real.exp (-c * s))
      (s * Real.exp (-c * s)) c := by
    convert! (((hasDerivAt_id c).neg.mul_const s).exp.neg) using 1
    simp [mul_comm]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun c _ => hd c)
    ((by fun_prop : Continuous (fun c : ℝ => s * Real.exp (-c * s))).intervalIntegrable a b)
  exact he.trans (by ring)

theorem lastKernel_as_integral (H z : ℝ) :
    lastKernel H z =
      ∫ c in ((1 : ℝ) / 9.645908801)..0.2067,
        Real.exp (-z / 2) * ((H / z) * Real.exp (-c * (H / z))) := by
  rw [intervalIntegral.integral_const_mul, exp_difference_integral]
  simp only [lastKernel, div_eq_mul_inv, mul_assoc]

theorem lastKernel_scaled {H H₀ t y k : ℝ} (hH₀ : 3093 ≤ H₀)
    (ht : 1 ≤ t) (hH : H₀ * t ≤ H) (hHup : H ≤ H₀ + 3100 * (t - 1))
    (hy : 20 ≤ y) (hy60 : y ≤ 60) (hk : 0 ≤ k) (hk7 : k ≤ 7) :
    lastKernel H (y + k * Real.log t) ≤
      (t ^ (1.1 : ℝ) * Real.exp (-(40 / 9.645908801) * Real.log t)) *
        lastKernel H₀ y := by
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < y := by linarith
  have hH₀0 : 0 < H₀ := by linarith
  have hH0 : 0 < H := (mul_pos hH₀0 ht0).trans_le hH
  have hz := shifted_height_bounds ht hy hk hk7
  have hl := Real.log_nonneg ht
  have hphase := shifted_phase_gain_forty hH₀ ht hH hy hy60 hk hk7
  have hratio : H / (y + k * Real.log t) ≤
      t ^ (1.1 : ℝ) * (H₀ / y) := by
    have hb := one_add_mul_self_le_rpow_one_add
      (s := t - 1) (show -1 ≤ t - 1 by linarith) (p := (1.1 : ℝ)) (by norm_num)
    rw [show 1 + (t - 1) = t by ring] at hb
    have hm := mul_le_mul_of_nonneg_left hb hH₀0.le
    have hd := mul_nonneg (show 0 ≤ 1.1 * H₀ - 3100 by linarith) (sub_nonneg.mpr ht)
    have hbase : H ≤ H₀ * t ^ (1.1 : ℝ) := by
      nlinarith only [hHup, hm, hd]
    calc
      _ ≤ H / y := div_le_div_of_nonneg_left hH0.le hy0 hz.2.1
      _ ≤ (H₀ * t ^ (1.1 : ℝ)) / y :=
        div_le_div_of_nonneg_right hbase hy0.le
      _ = _ := by ring
  have heheight : Real.exp (-(y + k * Real.log t) / 2) ≤ Real.exp (-y / 2) :=
    Real.exp_le_exp.mpr (by linarith [hz.2.1])
  rw [lastKernel_as_integral, lastKernel_as_integral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on
    (by norm_num : (1 : ℝ) / 9.645908801 ≤ 0.2067)
    ((by fun_prop : Continuous (fun c : ℝ =>
      Real.exp (-(y + k * Real.log t) / 2) *
        ((H / (y + k * Real.log t)) * Real.exp (-c * (H / (y + k * Real.log t)))))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun c : ℝ =>
      (t ^ (1.1 : ℝ) * Real.exp (-(40 / 9.645908801) * Real.log t)) *
        (Real.exp (-y / 2) * ((H₀ / y) * Real.exp (-c * (H₀ / y)))))).intervalIntegrable _ _)
  intro c hc
  have hc0 : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1 / 9.645908801).trans hc.1
  have he : Real.exp (-c * (H / (y + k * Real.log t))) ≤
      Real.exp (-(40 / 9.645908801) * Real.log t) * Real.exp (-c * (H₀ / y)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left hphase hc0
    have h2 := mul_le_mul_of_nonneg_right hc.1 (show 0 ≤ 40 * Real.log t by positivity)
    nlinarith only [h1, h2]
  have hm := mul_le_mul heheight
    (mul_le_mul hratio he (Real.exp_pos _).le (by positivity))
    (by positivity) (Real.exp_pos _).le
  exact hm.trans_eq (by ring)

def originalLastScalar (L : ℝ) : ℝ :=
  16 * sourceNu (L ^ (3 : ℕ)) * L *
    ∫ z in lowerLog L..upperLog L, lastKernel (L + Real.log 0.001) z

theorem affine_last_integrand_le {L y : ℝ} (hL : 3100 ≤ L)
    (hy : y ∈ Set.Icc (lowerLog 3100) (upperLog 3100)) :
    (sourceNu (L ^ (3 : ℕ)) * L * affineSlope L) *
      lastKernel (L + Real.log 0.001) (affineSlope L * y + affineOffset L) ≤
    (sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) *
      lastKernel ((3100 : ℝ) + Real.log 0.001) y := by
  let t := L / 3100
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 < t := by linarith
  have hLt : L = 3100 * t := by dsimp [t]; ring
  have hd := base_log_domain
  have hs := affine_source_domain hL
  have hnu := sourceNu_linear_scaling hL
  have hnu0 := hnu.1
  have hH := window_H_scaling hL
  obtain ⟨k, hk0, hk7, he⟩ := affine_source_shift hL hy
  have hy20 : 20 ≤ y := hd.1.trans hy.1
  have hy60 : y ≤ 60 := hy.2.trans hd.2.1
  have hy0 : 0 < y := by linarith
  have hHup : L + Real.log 0.001 ≤
      ((3100 : ℝ) + Real.log 0.001) + 3100 * (t - 1) := by
    linarith only [hLt]
  have hkbound := lastKernel_scaled hH.1 ht hH.2 hHup hy20 hy60 hk0 hk7
  rw [he]
  have hb := lastKernel_nonneg (show 0 ≤ (3100 : ℝ) + Real.log 0.001 by linarith [hH.1]) hy0
  have hcoef : sourceNu (L ^ (3 : ℕ)) * L * affineSlope L ≤
      (sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) * t ^ (3 : ℕ) := by
    calc
      _ ≤ (t * sourceNu ((3100 : ℝ) ^ (3 : ℕ))) * (3100 * t) * t := by
        rw [← hLt]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hnu.2 (by linarith))
          hs.2.1 (by linarith [hs.1]) (by positivity)
      _ = _ := by ring
  have habs : t ^ (3 : ℕ) * t ^ (1.1 : ℝ) *
      Real.exp (-(40 / 9.645908801) * Real.log t) ≤ 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0, Real.rpow_def_of_pos ht0, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have hl := Real.log_nonneg ht
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hl]
  have hHp : 0 ≤ L + Real.log 0.001 := by
    have h0 := mul_nonneg (show 0 ≤ (3100 : ℝ) + Real.log 0.001 by linarith [hH.1]) ht0.le
    exact h0.trans hH.2
  have hm := mul_le_mul hcoef hkbound
    (lastKernel_nonneg hHp (shifted_height_bounds ht hy20 hk0 hk7).1) (by positivity)
  have hp := mul_le_mul_of_nonneg_left habs
    (show 0 ≤ (sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) *
      lastKernel ((3100 : ℝ) + Real.log 0.001) y by positivity)
  nlinarith only [hm, hp]

theorem originalLastScalar_le_base {L : ℝ} (hL : 3100 ≤ L) :
    originalLastScalar L ≤ originalLastScalar 3100 := by
  have hd := base_log_domain
  have hs := affine_source_domain hL
  have hab : lowerLog 3100 ≤ upperLog 3100 := by linarith [hd.2.2]
  have hp : 0 < lowerLog L := (original_endpoints hL).1
  have hcomp : ContinuousOn
      (fun y => lastKernel (L + Real.log 0.001) (affineSlope L * y + affineOffset L))
      (Set.Icc (lowerLog 3100) (upperLog 3100)) := by
    apply (lastKernel_continuousOn hp (v := upperLog L)).comp
      ((continuousOn_const.mul continuousOn_id).add continuousOn_const)
    intro y hy
    change affineSlope L * y + affineOffset L ∈ Set.Icc (lowerLog L) (upperLog L)
    have hlo := mul_le_mul_of_nonneg_left hy.1 (show 0 ≤ affineSlope L by linarith [hs.1])
    have hup := mul_le_mul_of_nonneg_left hy.2 (show 0 ≤ affineSlope L by linarith [hs.1])
    exact ⟨by linarith [hs.2.2.1], by linarith [hs.2.2.2]⟩
  have hbase := lastKernel_continuousOn
    (show 0 < lowerLog 3100 by linarith [hd.1])
    (H := (3100 : ℝ) + Real.log 0.001) (v := upperLog 3100)
  have hi := intervalIntegral.integral_mono_on hab
    ((hcomp.const_mul (sourceNu (L ^ (3 : ℕ)) * L * affineSlope L)).intervalIntegrable_of_Icc
      (μ := volume) hab)
    ((hbase.const_mul (sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100)).intervalIntegrable_of_Icc hab)
    (fun y hy => affine_last_integrand_le hL hy)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have hchange := intervalIntegral.smul_integral_comp_mul_add
    (lastKernel (L + Real.log 0.001)) (a := lowerLog 3100) (b := upperLog 3100)
    (affineSlope L) (affineOffset L)
  simp only [smul_eq_mul] at hchange
  rw [hs.2.2.1, hs.2.2.2] at hchange
  rw [mul_assoc, hchange] at hi
  unfold originalLastScalar
  nlinarith only [hi]

theorem actual_last_strip_le_fixed_scalar {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (8 * (N : ℝ) * Real.sqrt q / q.totient) *
      (∫ y in omegaCutoff N q..middleUpper N q, heightKernel y *
        ∫ alpha in stripUpper q y..siegelCutoff q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      ((N : ℝ) / sourceL N) * originalLastScalar 3100 := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have he := original_endpoints hL
  have hH : 0 ≤ sourceL N + Real.log 0.001 := by
    rw [← log_window_eq (nat_pos_of_exp_le hN)]
    exact Real.log_nonneg (window_base_ge_one hN)
  have hi : 0 ≤ ∫ z in lowerLog (sourceL N)..upperLog (sourceL N),
      lastKernel (sourceL N + Real.log 0.001) z :=
    intervalIntegral.integral_nonneg he.2
      (fun z hz => lastKernel_nonneg hH (he.1.trans_le hz.1))
  have hcount := actual_last_strip_log_bound_T2 hN hq
  have hphi := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hnu (show 0 ≤ 16 * (N : ℝ) by positivity)) hi
  have hscalar : (16 * (N : ℝ)) * sourceNu (sourceP N) *
      (∫ z in lowerLog (sourceL N)..upperLog (sourceL N),
        lastKernel (sourceL N + Real.log 0.001) z) =
      ((N : ℝ) / sourceL N) * originalLastScalar (sourceL N) := by
    unfold originalLastScalar sourceP
    field_simp
  have hb := (hcount.trans hphi).trans_eq hscalar
  exact hb.trans (mul_le_mul_of_nonneg_left
    (originalLastScalar_le_base hL) (by positivity))

#print axioms originalLastScalar_le_base
#print axioms actual_last_strip_le_fixed_scalar

end LiuWang.Proof.Campaign20260915.SecondTerminal
