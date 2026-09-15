import LiuWang.Proof.Campaign20260915.Totient.RSGammaRecursion
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory Set
open LiuWang.Proof.ChebyshevBound.IntegratedFormula

namespace LiuWang.Proof.Campaign20260915.Totient

def rsTrivialTerm (n : ℕ) (x : ℝ) : ℝ :=
  (x⁻¹) ^ (2 * (n + 1)) / (2 * (n + 1))

def rsTrivialPrimitive (n : ℕ) (x : ℝ) : ℝ :=
  (1 - (x⁻¹) ^ (2 * n + 1)) / ((2 * n + 2) * (2 * n + 1))

def rsTrivialKernel (x : ℝ) : ℝ := -(1 / 2) * Real.log (1 - x⁻¹ ^ 2)

theorem rsTrivialTerm_hasSum {x : ℝ} (hx : 1 < x) :
    HasSum (fun n => rsTrivialTerm n x) (rsTrivialKernel x) := by
  have hi : 0 < x⁻¹ := inv_pos.mpr (by linarith)
  have hi1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hp : |x⁻¹ ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_lt_one₀ hi.le hi1 (by omega)
  convert! (Real.hasSum_pow_div_log_of_abs_lt_one hp).div_const 2 using 1
  · funext n
    unfold rsTrivialTerm
    rw [pow_mul]
    field_simp
  · unfold rsTrivialKernel
    ring

theorem rsTrivialTerm_nonneg (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ rsTrivialTerm n x := by unfold rsTrivialTerm; positivity

theorem rsTrivialTerm_antitone (n : ℕ) :
    AntitoneOn (rsTrivialTerm n) (Ioi 0) := by
  intro a ha b hb hab
  unfold rsTrivialTerm
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (inv_nonneg.mpr hb.le) (inv_anti₀ ha hab) _) (by positivity)

theorem rsTrivialPrimitive_deriv (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (rsTrivialPrimitive n) (rsTrivialTerm n x) x := by
  have hd := ((hasDerivAt_inv hx.ne').pow (2 * n + 1)).const_sub 1
  convert! hd.div_const (((2 * n + 2) * (2 * n + 1) : ℕ) : ℝ) using 1
  · funext t
    simp only [rsTrivialPrimitive, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      Pi.pow_apply]
  · unfold rsTrivialTerm
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    have hn1 : (2 : ℝ) * n + 1 ≠ 0 := by positivity
    have hn2 : (2 : ℝ) * n + 2 ≠ 0 := by positivity
    field_simp

theorem rs_scaled_gamma_term (n : ℕ) {x : ℝ} (hx : 1 < x) :
    (x : ℂ) * gammaMellinTerm n x⁻¹ = (rsTrivialPrimitive n x : ℂ) := by
  have hmem : x⁻¹ ∈ Ioc (0 : ℝ) 1 :=
    ⟨inv_pos.mpr (by linarith), (inv_lt_one_of_one_lt₀ hx).le⟩
  have hexp : (2 : ℂ) * (n + 1) = ((2 * (n + 1) : ℕ) : ℂ) := by push_cast; ring
  simp only [gammaMellinTerm, powerCut, indicator_of_mem hmem, Complex.cpow_one,
    hexp, Complex.cpow_natCast]
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, pow_succ]
  unfold rsTrivialPrimitive
  push_cast
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  rw [show ((2 : ℂ) * n + 1 + 1) * (2 * n + 1 + 1 - 1) =
    (2 * n + 2) * (2 * n + 1) by ring, ← mul_div_assoc]
  congr 1
  field_simp

theorem rsTrivialPrimitive_summable {x : ℝ} (hx : 1 < x) :
    Summable (fun n => rsTrivialPrimitive n x) := by
  apply Complex.summable_ofReal.mp
  have hs := (gammaMellinTerm_summable (inv_pos.mpr (by linarith : 0 < x))).mul_left (x : ℂ)
  exact hs.congr (fun n => rs_scaled_gamma_term n hx)

theorem rsGammaCorrection_eq_trivial_sum {x : ℝ} (hx : 1 < x) :
    gammaCorrection x = ((∑' n, rsTrivialPrimitive n x : ℝ) : ℂ) := by
  rw [gammaCorrection, Complex.ofReal_tsum, ← tsum_mul_left]
  exact tsum_congr (fun n => rs_scaled_gamma_term n hx)

theorem rsGammaCorrection_deriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt gammaCorrection (rsTrivialKernel x : ℂ) x := by
  let a := (1 + x) / 2
  have ha : 1 < a := by dsimp [a]; linarith
  have hax : a < x := by dsimp [a]; linarith
  have hd := hasDerivAt_tsum_of_isPreconnected
    (rsTrivialTerm_hasSum ha).summable isOpen_Ioi (convex_Ioi a).isPreconnected
    (fun n y hy => rsTrivialPrimitive_deriv n ((by linarith : 0 < a).trans hy))
    (fun n y hy => by
      have hy0 : 0 < y := (by linarith : 0 < a).trans hy
      rw [Real.norm_eq_abs, abs_of_nonneg (rsTrivialTerm_nonneg n hy0)]
      exact rsTrivialTerm_antitone n (by linarith : 0 < a) hy0 hy.le)
    hax (rsTrivialPrimitive_summable hx) hax
  rw [(rsTrivialTerm_hasSum hx).tsum_eq] at hd
  apply hd.ofReal_comp.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact rsGammaCorrection_eq_trivial_sum hy

theorem rsTrivialKernel_nonneg {x : ℝ} (hx : 1 < x) :
    0 ≤ rsTrivialKernel x := by
  rw [← (rsTrivialTerm_hasSum hx).tsum_eq]
  exact tsum_nonneg (fun n => rsTrivialTerm_nonneg n (by linarith))

theorem rsTrivialKernel_antitone : AntitoneOn rsTrivialKernel (Ioi 1) := by
  intro a ha b hb hab
  have ha0 : a ∈ Ioi (0 : ℝ) := lt_trans zero_lt_one (show 1 < a from ha)
  have hb0 : b ∈ Ioi (0 : ℝ) := lt_trans zero_lt_one (show 1 < b from hb)
  rw [← (rsTrivialTerm_hasSum ha).tsum_eq, ← (rsTrivialTerm_hasSum hb).tsum_eq]
  exact (rsTrivialTerm_hasSum hb).summable.tsum_le_tsum
    (fun n => rsTrivialTerm_antitone n ha0 hb0 hab)
    (rsTrivialTerm_hasSum ha).summable

#print axioms rsTrivialTerm_hasSum
#print axioms rsTrivialPrimitive_deriv
#print axioms rsGammaCorrection_eq_trivial_sum
#print axioms rsGammaCorrection_deriv
#print axioms rsTrivialKernel_nonneg
#print axioms rsTrivialKernel_antitone

end LiuWang.Proof.Campaign20260915.Totient
