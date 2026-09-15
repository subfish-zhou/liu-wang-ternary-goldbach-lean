import LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.CorrectionReserve
import LiuWang.Proof.DirichletZeroCount.Applications.Coarse

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail

theorem selected_cutoff_ge_ten_thousand {L : ℝ} (hL : 5000 ≤ L) :
    10000 ≤ spectralCutoff L := by
  have hs := saddle_ge_sixteen hL
  have hr0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hr : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hv : 10 ≤ saddle L / Real.sqrt 2 :=
    (le_div_iff₀ hr0).mpr (by nlinarith)
  have he : (10000 : ℝ) ≤ Real.exp 10 := by
    have h := exp_lower_nat_add 10 (r := 0) (by norm_num)
    norm_num at h
    linarith
  exact he.trans (Real.exp_le_exp.mpr hv)

theorem selected_window_card_le {L : ℝ} (hL : 5000 ≤ L) :
    ((xiWindow 0 (spectralCutoff L)).card : ℝ) ≤
      10 * spectralCutoff L * Real.log (spectralCutoff L) := by
  let K := spectralCutoff L
  have hK : 10000 ≤ K := selected_cutoff_ge_ten_thousand hL
  have hlog : 8 ≤ Real.log K := log_height_ge_eight hK
  have hshift : Real.log (K + 4) ≤ Real.log K + 1 := by
    simpa only [one_mul] using log_shift_le (q := 1) (by norm_num) hK
      (c := 4) (by norm_num) le_rfl
  have hinv : 1 / (K + 3) ≤ 1 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hb : Real.log (K + 4) / 2 + 1 / (K + 3) + 1 / 3 ≤ 3 * Real.log K := by
    linarith
  have hb0 : 0 ≤ Real.log (K + 4) / 2 + 1 / (K + 3) + 1 / 3 := by
    have h := Real.log_nonneg (by linarith : 1 ≤ K + 4)
    positivity
  have hc := xi_count_real_parameter (y := K) (s := K + 4)
    (by linarith) (by linarith) (by linarith)
  calc
    _ ≤ (2 * K + 4) * (Real.log (K + 4) / 2 + 1 / (K + 3) + 1 / 3) := by
      convert hc using 1
      ring
    _ ≤ (3 * K) * (3 * Real.log K) :=
      mul_le_mul (by linarith) hb hb0 (by linarith)
    _ ≤ _ := by nlinarith

theorem selected_window_peak_budget {L : ℝ} (hL : 5000 ≤ L) :
    ((xiWindow 0 (spectralCutoff L)).card : ℝ) *
      Real.exp (-2 * Real.sqrt 2 * saddle L) ≤
        (1 / 2 : ℝ) * saddle L ^ 2 * Real.exp (-2 * saddle L) := by
  let s := saddle L
  let u := s / Real.sqrt 2
  have hs : 16 ≤ s := saddle_ge_sixteen hL
  have hs0 : 0 ≤ s := by linarith
  have hr0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hr : (7 / 5 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 3 / 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    constructor <;> nlinarith
  have hu0 : 0 ≤ u := div_nonneg hs0 hr0.le
  have hu : u ≤ (5 / 7 : ℝ) * s := by
    apply (div_le_iff₀ hr0).mpr
    nlinarith
  have hphase : u - 2 * Real.sqrt 2 * s ≤ -2 * s := by
    have hid : u - 2 * Real.sqrt 2 * s = -3 * s / Real.sqrt 2 := by
      dsimp [u]
      have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      field_simp
      nlinarith
    rw [hid]
    apply (div_le_iff₀ hr0).mpr
    nlinarith
  have hc := selected_window_card_le hL
  rw [log_spectralCutoff] at hc
  calc
    _ ≤ (10 * Real.exp u * u) * Real.exp (-2 * Real.sqrt 2 * s) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = (10 * u) * Real.exp (u - 2 * Real.sqrt 2 * s) := by
      rw [Real.exp_sub]
      rw [show -2 * Real.sqrt 2 * s = -(2 * Real.sqrt 2 * s) by ring, Real.exp_neg]
      ring
    _ ≤ (10 * u) * Real.exp (-2 * s) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase) (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith

theorem actual_middle_spectrum_budget {L : ℝ} (hL : 5000 ≤ L) :
    (∑ p ∈ xiWindow 0 (spectralCutoff L), rsHighTerm rsA 1 L p) ≤
      (1 / 2 : ℝ) * saddle L ^ 2 * Real.exp (-2 * saddle L) :=
  (actual_finite_spectrum_le_peak (by linarith : 0 ≤ L) _).trans
    (selected_window_peak_budget hL)

theorem actual_high_spectrum_after_middle {L : ℝ} (hL : 5000 ≤ L) :
    (∑' p, rsHighTerm rsA 1 L p) ≤
      (1 / 2 : ℝ) * saddle L ^ 2 * Real.exp (-2 * saddle L) +
        ∑' p, rsHighTerm (spectralCutoff L) 1 L p := by
  rw [actual_high_spectrum_split (by linarith : 0 ≤ L) (spectralCutoff_ge_rsA hL)]
  exact add_le_add (actual_middle_spectrum_budget hL) le_rfl

theorem weighted_first_moment_budget {L : ℝ} (hL : 5000 ≤ L) :
    Real.exp (-L / 2) * (∑' p, rsZeroMoment 1 0 p) ≤
      (1 / 10 : ℝ) * saddle L ^ 2 * Real.exp (-2 * saddle L) := by
  have hm : (∑' p, rsZeroMoment 1 0 p) ≤ (2 / 3 : ℝ) := by
    simpa only [rsZeroMoment, mul_zero, Real.exp_zero, show (1 + 1 : ℕ) = 2 by rfl,
      sq_abs] using xi_height_inverse_square_sum_le
  have hs := saddle_ge_sixteen hL
  have hsid : L = rsR * saddle L ^ 2 := by
    rw [saddle_sq (by linarith : 0 ≤ L)]
    field_simp [rsR_pos.ne']
  have hscale := mul_le_mul_of_nonneg_right
    (show (16 : ℝ) ≤ rsR by linarith [rsR_interval.1]) (sq_nonneg (saddle L))
  have hphase : -L / 2 ≤ -2 * saddle L := by nlinarith
  calc
    _ ≤ (2 / 3 : ℝ) * Real.exp (-L / 2) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ ≤ (2 / 3 : ℝ) * Real.exp (-2 * saddle L) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase) (by norm_num)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith

#print axioms actual_middle_spectrum_budget
#print axioms actual_high_spectrum_after_middle
#print axioms weighted_first_moment_budget

end LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail
