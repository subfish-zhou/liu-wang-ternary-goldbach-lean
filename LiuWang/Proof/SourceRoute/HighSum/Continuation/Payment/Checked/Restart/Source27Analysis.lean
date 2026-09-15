import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.CountScalar
import LiuWang.Proof.SourceRoute.HighSum.Continuation.EndpointScalar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Directed analytic integration of the literal scalar integrand in (2.27) -/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart

def source27Integrand (L s : ℝ) : ℝ :=
  L ^ (4 : ℕ) *
    (s / Real.pi - 0.874 + (6.8423 / 7) * (1 / 100000) * s * Real.exp (-s) +
      (15 / 7) * (1 / 100000) * Real.exp (-s)) * Real.exp (-0.478 * L / s)

def source27Primitive (k c s : ℝ) : ℝ :=
  ((s ^ (3 : ℕ) / Real.pi - c * s ^ (2 : ℕ)) / k -
    (3 * s ^ (4 : ℕ) / Real.pi - 2 * c * s ^ (3 : ℕ)) / k ^ (2 : ℕ) +
    (12 * s ^ (5 : ℕ) / Real.pi - 6 * c * s ^ (4 : ℕ)) / k ^ (3 : ℕ)) *
      Real.exp (-k / s)

theorem source27_correction {s : ℝ} (hs : 10 ≤ s) :
    (6.8423 / 7 : ℝ) * (1 / 100000) * s * Real.exp (-s) +
      (15 / 7) * (1 / 100000) * Real.exp (-s) ≤ 1 / 100000 := by
  have hs0 : 0 ≤ s := by linarith
  have he := Real.pow_div_factorial_le_exp s hs0 2
  norm_num at he
  have hs2 : 100 ≤ s ^ (2 : ℕ) := by nlinarith
  have hexp := Real.exp_pos s
  have h0 : Real.exp (-s) ≤ 1 / 50 := by
    rw [Real.exp_neg]
    exact (inv_le_iff_one_le_mul₀ hexp).mpr (by nlinarith)
  have h1 : s * Real.exp (-s) ≤ 1 / 5 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_iff₀ hexp).mpr (by nlinarith)
  nlinarith

theorem source27Integrand_le {L s : ℝ} (hs : 10 ≤ s) :
    source27Integrand L s ≤
      L ^ (4 : ℕ) * (s / Real.pi - 0.87399) * Real.exp (-0.478 * L / s) := by
  unfold source27Integrand
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith [source27_correction hs]

theorem source27Primitive_deriv {k c s : ℝ} (hk : k ≠ 0) (hs : s ≠ 0) :
    HasDerivAt (source27Primitive k c)
      ((s / Real.pi - c +
        (60 * s ^ (4 : ℕ) / Real.pi - 24 * c * s ^ (3 : ℕ)) / k ^ (3 : ℕ)) *
        Real.exp (-k / s)) s := by
  have h1 := ((((hasDerivAt_id s).pow 3).div_const Real.pi).sub
    (((hasDerivAt_id s).pow 2).const_mul c)).div_const k
  have h2 := (((((hasDerivAt_id s).pow 4).const_mul 3).div_const Real.pi).sub
    (((hasDerivAt_id s).pow 3).const_mul (2 * c))).div_const (k ^ (2 : ℕ))
  have h3 := (((((hasDerivAt_id s).pow 5).const_mul 12).div_const Real.pi).sub
    (((hasDerivAt_id s).pow 4).const_mul (6 * c))).div_const (k ^ (3 : ℕ))
  have hP := (h1.sub h2).add h3
  have he := (((hasDerivAt_const s (-k)).div (hasDerivAt_id s) hs).exp)
  convert! hP.mul he using 1
  dsimp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Pi.div_apply, id_eq]
  field_simp
  ring

theorem source27Primitive_majorizes {k s : ℝ} (hk : 0 < k) (hs : 10 ≤ s) :
    (s / Real.pi - 0.87399) * Real.exp (-k / s) ≤
      (s / Real.pi - 0.87399 +
        (60 * s ^ (4 : ℕ) / Real.pi - 24 * 0.87399 * s ^ (3 : ℕ)) / k ^ (3 : ℕ)) *
        Real.exp (-k / s) := by
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have hbase : 0 ≤ 60 * s / Real.pi - 24 * (0.87399 : ℝ) := by
    have h : 24 * (0.87399 : ℝ) ≤ 60 * s / Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_four])
    linarith
  have hnum : 0 ≤ 60 * s ^ (4 : ℕ) / Real.pi - 24 * 0.87399 * s ^ (3 : ℕ) := by
    have h := mul_nonneg (show 0 ≤ s ^ (3 : ℕ) by positivity) hbase
    convert! h using 1
    ring
  have hd := div_nonneg hnum (pow_pos hk 3).le
  linarith

theorem source27_integral_endpoint_bound {L a b : ℝ}
    (hL : 0 < L) (ha : 10 ≤ a) (hab : a ≤ b) :
    (∫ s in a..b, source27Integrand L s) ≤
      L ^ (4 : ℕ) *
        (source27Primitive (0.478 * L) 0.87399 b -
          source27Primitive (0.478 * L) 0.87399 a) := by
  have hs0 (s : ℝ) (hs : s ∈ Set.uIcc a b) : s ≠ 0 := by
    rw [Set.uIcc_of_le hab] at hs
    linarith [hs.1]
  have hk : 0 < 0.478 * L := by positivity
  let D := fun s : ℝ =>
    (s / Real.pi - 0.87399 +
      (60 * s ^ (4 : ℕ) / Real.pi - 24 * 0.87399 * s ^ (3 : ℕ)) / (0.478 * L) ^ (3 : ℕ)) *
      Real.exp (-(0.478 * L) / s)
  have hi : IntervalIntegrable D volume a b := by
    apply ContinuousOn.intervalIntegrable
    dsimp only [D]
    fun_prop
  have hf : IntervalIntegrable (source27Integrand L) volume a b := by
    apply ContinuousOn.intervalIntegrable
    unfold source27Integrand
    fun_prop
  have hd (s : ℝ) (hs : s ∈ Set.uIcc a b) :
      HasDerivAt (source27Primitive (0.478 * L) 0.87399) (D s) s :=
    source27Primitive_deriv hk.ne' (hs0 s hs)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  calc
    _ ≤ ∫ s in a..b, L ^ (4 : ℕ) * D s := by
      apply intervalIntegral.integral_mono_on hab hf (hi.const_mul _)
      intro s hs
      have h1 := source27Integrand_le (L := L) (ha.trans hs.1)
      have h2 := mul_le_mul_of_nonneg_left
        (source27Primitive_majorizes hk (ha.trans hs.1)) (show 0 ≤ L ^ (4 : ℕ) by positivity)
      dsimp only [D]
      convert! h1.trans (by simpa only [neg_mul, mul_assoc] using h2) using 1
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul, he]

theorem source27_original_endpoints {L : ℝ} (hL : 3100 ≤ L) :
    10 ≤ Real.log (3.36 * L ^ (3 : ℕ)) ∧
      Real.log (3.36 * L ^ (3 : ℕ)) ≤
        Real.log (10000 * L ^ (3 : ℕ) * Real.log (L ^ (3 : ℕ))) := by
  have h0 : 0 < L := by linarith
  have hl := original_log_linear hL
  have hA : 10 ≤ Real.log (3.36 * L ^ (3 : ℕ)) := by
    rw [Real.log_mul (by norm_num) (pow_pos h0 _).ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have hh : 0 ≤ Real.log (3.36 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  refine ⟨hA, Real.log_le_log (by positivity) ?_⟩
  have hb : 3.36 ≤ 10000 * Real.log (L ^ (3 : ℕ)) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hb (show 0 ≤ L ^ (3 : ℕ) by positivity)]

theorem original_source27_analytic {L : ℝ} (hL : 3100 ≤ L) :
    (∫ s in Real.log (3.36 * L ^ (3 : ℕ))..
      Real.log (10000 * L ^ (3 : ℕ) * Real.log (L ^ (3 : ℕ))),
        source27Integrand L s) ≤
      L ^ (4 : ℕ) *
        (source27Primitive (0.478 * L) 0.87399
          (Real.log (10000 * L ^ (3 : ℕ) * Real.log (L ^ (3 : ℕ)))) -
        source27Primitive (0.478 * L) 0.87399 (Real.log (3.36 * L ^ (3 : ℕ)))) :=
  source27_integral_endpoint_bound (by linarith)
    (source27_original_endpoints hL).1 (source27_original_endpoints hL).2

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
