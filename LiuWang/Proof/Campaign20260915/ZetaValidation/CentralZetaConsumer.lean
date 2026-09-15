import LiuWang.Proof.Campaign20260915.ZetaValidation.CentralInfiniteContour

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem zeta_eq_source_local_truncation (sigma : ℝ) {eta : ℝ} {m : ℕ} (N : ℕ)
    (hm : 0 < m) (hs : sigma ≤ 1) (hlo : (m : ℝ) < eta) (hhi : eta < m + 1) :
    let s : ℂ := (sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      (2 * Real.pi : ℂ) ^ s / (2 * Gamma s * cos (Real.pi * s / 2)) *
        (∑ k ∈ Finset.range m, (k + 1 : ℂ) ^ (s - 1)) +
      rsHankelPrefactor s *
        (rsLocalPrefactor sigma eta m *
          ((∫ y : ℝ in (eta / 2)..(-eta / 2), rsLocalPolynomialIntegrand sigma eta m N y) +
            ∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta m N y) +
          (∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta m r) -
            ∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand s eta m y) := by
  dsimp only
  have he : 0 < eta := lt_of_le_of_lt (Nat.cast_nonneg m) hlo
  have hint : ∀ n : ℤ, eta ≠ n := by
    intro n hn
    have hh : (m : ℤ) < n ∧ n < (m : ℤ) + 1 := by exact_mod_cast (hn ▸ And.intro hlo hhi)
    omega
  have ht : 0 < (((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) : ℂ).im := by
    have hh : 0 < (rsSaddleScale * eta) ^ 2 := sq_pos_of_pos (mul_pos rsSaddleScale_pos he)
    simpa only [add_im, mul_im, ofReal_re, ofReal_im, pow_two, mul_re, I_re, I_im,
      mul_zero, mul_one, one_mul, zero_mul, add_zero, zero_add, sub_zero] using hh
  have hs' : (((sigma : ℂ) + I * ((rsSaddleScale * eta : ℝ) : ℂ) ^ 2) : ℂ).re ≤ 1 := by
    simpa only [add_re, mul_re, ofReal_re, ofReal_im, pow_two, mul_im, I_re, I_im,
      mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add] using hs
  rw [zeta_eq_source_sums_add_C2 hm ht hs' hlo hhi,
    rsSourceC2_local_truncation sigma N hm hs he hint]

theorem zeta_eq_C2_local_split {m : ℕ} (hm : 0 < m) {s : ℂ} (ht : 0 < s.im)
    (hs : s.re ≤ 1) {eta : ℝ} (hlo : (m : ℝ) < eta) (hhi : eta < m + 1) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      (2 * Real.pi : ℂ) ^ s / (2 * Gamma s * cos (Real.pi * s / 2)) *
        (∑ k ∈ Finset.range m, (k + 1 : ℂ) ^ (s - 1)) +
      rsHankelPrefactor s *
        ((∫ y : ℝ in (eta / 2)..(-eta / 2), rsC2RightIntegrand s eta m y) +
          (∫ r : ℝ in Ioi 0, rsC2LeftIntegrand s eta m r) -
            ∫ y : ℝ in Ioi (eta / 2), rsC2RightIntegrand s eta m y) := by
  have he : 0 < eta := lt_of_le_of_lt (Nat.cast_nonneg m) hlo
  have hint : ∀ n : ℤ, eta ≠ n := by
    intro n hn
    have hh : (m : ℤ) < n ∧ n < (m : ℤ) + 1 := by exact_mod_cast (hn ▸ And.intro hlo hhi)
    omega
  rw [zeta_eq_source_sums_add_C2 hm ht hs hlo hhi, rsSourceC2_local_split hm hs he hint]

end LiuWang.Proof.Campaign20260915.ZetaValidation
