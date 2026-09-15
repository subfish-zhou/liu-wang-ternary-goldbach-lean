import LiuWang.Proof.Campaign20260915.Totient.RSParameters
import LiuWang.Proof.Campaign20260915.Totient.RSHighZeros

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.ChebyshevBound.HighHeight
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail

def saddle (L : ℝ) : ℝ := Real.sqrt (L / rsR)

-- Theorem 11, not the smoothing epsilon of Theorem 28.
def epsilon (x : ℝ) : ℝ :=
  Real.sqrt (Real.log x) * Real.exp (-saddle (Real.log x))

def spectralCutoff (L : ℝ) : ℝ :=
  Real.exp (saddle L / Real.sqrt 2)

theorem saddle_sq {L : ℝ} (hL : 0 ≤ L) :
    saddle L ^ 2 = L / rsR :=
  Real.sq_sqrt (div_nonneg hL rsR_pos.le)

theorem saddle_ge_sixteen {L : ℝ} (hL : 5000 ≤ L) : 16 ≤ saddle L := by
  have hs := saddle_sq (show 0 ≤ L by linarith)
  have hq : (256 : ℝ) ≤ L / rsR :=
    (le_div_iff₀ rsR_pos).mpr (by nlinarith [rsR_interval.2])
  have hn := Real.sqrt_nonneg (L / rsR)
  change 0 ≤ saddle L at hn
  nlinarith

theorem log_spectralCutoff (L : ℝ) :
    Real.log (spectralCutoff L) = saddle L / Real.sqrt 2 :=
  Real.log_exp _

theorem spectralCutoff_ge_rsA {L : ℝ} (hL : 5000 ≤ L) :
    rsA ≤ spectralCutoff L := by
  have hs := saddle_ge_sixteen hL
  have hr : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  apply Real.exp_le_exp.mpr
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
  nlinarith

theorem spectralCutoff_exact_domain {L : ℝ} (hL : 0 ≤ L) :
    L = 2 * rsR * Real.log (spectralCutoff L) ^ 2 := by
  rw [log_spectralCutoff, div_pow, Real.sq_sqrt (by norm_num), saddle_sq hL]
  field_simp [rsR_pos.ne']

theorem spectralCutoff_theorem27_domain {L : ℝ} (hL : 5000 ≤ L) :
    rsA ≤ spectralCutoff L ∧ 0 ≤ L ∧
      L ≤ (1 + 1 : ℝ) * rsR * Real.log (spectralCutoff L) ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  refine ⟨spectralCutoff_ge_rsA hL, hL0, ?_⟩
  norm_num only [show (1 + 1 : ℝ) = 2 by norm_num]
  exact (spectralCutoff_exact_domain hL0).le

theorem cubic_exp_tail {s : ℝ} (hs : 16 ≤ s) :
    s ^ 3 * Real.exp (-s) ≤ 1 / 2000 := by
  have hlin : s / 16 ≤ Real.exp ((s - 16) / 3) := by
    linarith [Real.add_one_le_exp ((s - 16) / 3)]
  have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ s / 16) hlin 3
  have he : Real.exp ((s - 16) / 3) ^ 3 = Real.exp (s - 16) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, div_pow] at hp
  have hp' : s ^ 3 ≤ 4096 * Real.exp (s - 16) := by
    nlinarith
  have h16 : (8192000 : ℝ) ≤ Real.exp 16 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 54)
      exp_four_ge_fifty_four 4
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  have hneg : Real.exp (-16 : ℝ) ≤ 1 / 8192000 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h16
  calc
    _ ≤ 4096 * Real.exp (s - 16) * Real.exp (-s) :=
      mul_le_mul_of_nonneg_right hp' (Real.exp_pos _).le
    _ = 4096 * Real.exp (-16) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 4096 * (1 / 8192000) := by gcongr
    _ = _ := by norm_num

theorem log_mul_epsilon_le {x : ℝ} (hx : 5000 ≤ Real.log x) :
    Real.log x * epsilon x ≤ 9 / 200 := by
  let L := Real.log x
  let s := saddle L
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hs : 16 ≤ s := saddle_ge_sixteen hx
  have hs0 : 0 ≤ s := by linarith
  have hsq : s ^ 2 = L / rsR := saddle_sq hL
  have hLid : L = rsR * s ^ 2 := by
    rw [hsq]
    field_simp [rsR_pos.ne']
  have hLup : L ≤ 18 * s ^ 2 := by
    rw [hLid]
    exact mul_le_mul_of_nonneg_right (by linarith [rsR_interval.2]) (sq_nonneg s)
  have hroot : Real.sqrt L ≤ 5 * s := by
    have hr := Real.sq_sqrt hL
    have hn := Real.sqrt_nonneg L
    nlinarith
  have hprod : L * Real.sqrt L ≤ 90 * s ^ 3 := by
    calc
      _ ≤ (18 * s ^ 2) * (5 * s) :=
        mul_le_mul hLup hroot (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ = (L * Real.sqrt L) * Real.exp (-s) := by
      change L * (Real.sqrt L * Real.exp (-s)) = _
      ring
    _ ≤ (90 * s ^ 3) * Real.exp (-s) :=
      mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
    _ = 90 * (s ^ 3 * Real.exp (-s)) := by ring
    _ ≤ 90 * (1 / 2000) :=
      mul_le_mul_of_nonneg_left (cubic_exp_tail hs) (by norm_num)
    _ = _ := by norm_num

theorem epsilon_lt_half_log_inv {x : ℝ} (hx : 5000 ≤ Real.log x) :
    epsilon x < 1 / (2 * Real.log x) := by
  apply (lt_div_iff₀ (by linarith : 0 < 2 * Real.log x)).mpr
  nlinarith [log_mul_epsilon_le hx]

theorem phi_one_exp (L u : ℝ) :
    rsPhi 1 L (Real.exp u) = Real.exp (-2 * u - (L / rsR) / u) := by
  unfold rsPhi
  rw [Real.log_exp, show (1 + 1 : ℕ) = 2 by rfl,
    ← Real.exp_nat_mul, ← Real.exp_sub, div_div]
  congr 1
  ring

theorem phi_one_peak {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    rsPhi 1 L (Real.exp u) ≤ Real.exp (-2 * Real.sqrt 2 * saddle L) := by
  rw [phi_one_exp]
  apply Real.exp_le_exp.mpr
  have hsq := sq_nonneg (Real.sqrt 2 * u - saddle L)
  have hr : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs := saddle_sq hL
  have hid : (Real.sqrt 2 * u) ^ 2 = 2 * u ^ 2 := by rw [mul_pow, hr]
  have hbound : 2 * Real.sqrt 2 * saddle L ≤ 2 * u + (L / rsR) / u := by
    apply (mul_le_mul_iff_right₀ hu).mp
    have he : u * (2 * u + (L / rsR) / u) = 2 * u ^ 2 + L / rsR := by
      field_simp
    rw [he]
    nlinarith [hsq]
  linarith

theorem actual_high_term_le_peak {L : ℝ} (hL : 0 ≤ L)
    (p : RiemannXiDivisorZeroIndex) :
    rsHighTerm rsA 1 L p ≤ Real.exp (-2 * Real.sqrt 2 * saddle L) := by
  have h := rsHighTerm_le_phi (le_refl rsA) hL 1 p
  split_ifs at h with hp
  · have ht : 1 < |(riemannXiDivisorZeroValue p).im| := by
      linarith [rsA_ge_thousand]
    have hpeak := phi_one_peak hL (Real.log_pos ht)
    rw [Real.exp_log (by linarith : 0 < |(riemannXiDivisorZeroValue p).im|)] at hpeak
    exact h.trans hpeak
  · exact h.trans (Real.exp_pos _).le

theorem actual_finite_spectrum_le_peak {L : ℝ} (hL : 0 ≤ L)
    (F : Finset RiemannXiDivisorZeroIndex) :
    (∑ p ∈ F, rsHighTerm rsA 1 L p) ≤
      F.card * Real.exp (-2 * Real.sqrt 2 * saddle L) := by
  simpa using Finset.sum_le_sum
    (fun p (_ : p ∈ F) => actual_high_term_le_peak hL p)

#print axioms spectralCutoff_theorem27_domain
#print axioms epsilon_lt_half_log_inv
#print axioms actual_finite_spectrum_le_peak

end LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail
