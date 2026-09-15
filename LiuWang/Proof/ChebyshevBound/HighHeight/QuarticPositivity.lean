import LiuWang.Proof.ChebyshevBound.HighHeight.ZeroFree

/-! # 四次非负三角多项式：8(1+cos θ)^4 的实际 Λ 级数消费者。 -/

set_option autoImplicit false
noncomputable section

open Complex ArithmeticFunction
open scoped LSeries.notation

namespace LiuWang.Proof.ChebyshevBound.HighHeight

theorem quartic_unit_circle_nonneg {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ (35 + 56 * z + 28 * z ^ 2 + 8 * z ^ 3 + z ^ 4).re := by
  have hy : z.im ^ 2 = 1 - z.re ^ 2 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simp only [Complex.normSq_apply] at h
    nlinarith
  have heq : (35 + 56 * z + 28 * z ^ 2 + 8 * z ^ 3 + z ^ 4).re =
      8 * (1 + z.re) ^ 4 := by
    norm_num [pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re]
    ring_nf
    rw [show z.im ^ 4 = (z.im ^ 2) ^ 2 by ring, hy]
    ring
  rw [heq]
  positivity

theorem mangoldt_term_harmonic {n : ℕ} (hn : n ≠ 0) (σ t : ℝ) (k : ℕ) :
    LSeries.term (↗Λ) ((σ : ℂ) + I * ((k : ℝ) * t : ℝ)) n =
      ((Λ n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        ((n : ℂ) ^ (-(I * (t : ℂ)))) ^ k := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← cpow_neg,
    BombieriVinogradov.SiegelWalfisz.natCast_cpow_neg_add_I_mul hn]
  have he : -(I * (((k : ℝ) * t : ℝ) : ℂ)) = (k : ℂ) * (-(I * (t : ℂ))) := by
    push_cast
    ring
  rw [he, cpow_nat_mul]
  push_cast
  ring

theorem quartic_mangoldt_terms_nonneg (σ t : ℝ) (n : ℕ) :
    0 ≤
      35 * (LSeries.term (↗Λ) (σ : ℂ) n).re +
      56 * (LSeries.term (↗Λ) ((σ : ℂ) + I * (t : ℂ)) n).re +
      28 * (LSeries.term (↗Λ) ((σ : ℂ) + I * ((2 * t : ℝ) : ℂ)) n).re +
      8 * (LSeries.term (↗Λ) ((σ : ℂ) + I * ((3 * t : ℝ) : ℂ)) n).re +
      (LSeries.term (↗Λ) ((σ : ℂ) + I * ((4 * t : ℝ) : ℂ)) n).re := by
  by_cases hn : n = 0
  · subst n; simp
  let z := (n : ℂ) ^ (-(I * (t : ℂ)))
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    norm_num [Complex.mul_re]
  have hh := quartic_unit_circle_nonneg hz
  have h0 := mangoldt_term_harmonic hn σ t 0
  have h1 := mangoldt_term_harmonic hn σ t 1
  have h2 := mangoldt_term_harmonic hn σ t 2
  have h3 := mangoldt_term_harmonic hn σ t 3
  have h4 := mangoldt_term_harmonic hn σ t 4
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Complex.ofReal_zero, zero_mul, one_mul,
    mul_zero, add_zero, pow_zero, pow_one, mul_one] at h0 h1 h2 h3 h4
  rw [h0, h1, h2, h3, h4]
  have hweight : 0 ≤ Λ n * (n : ℝ) ^ (-σ) :=
    mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have h := mul_nonneg hweight hh
  dsimp [z] at h
  norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_mul] at h ⊢
  nlinarith only [h]

theorem zeta_quartic_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤
      35 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      56 * (-deriv riemannZeta ((σ : ℂ) + I * (t : ℂ)) /
        riemannZeta ((σ : ℂ) + I * (t : ℂ))).re +
      28 * (-deriv riemannZeta ((σ : ℂ) + I * ((2 * t : ℝ) : ℂ)) /
        riemannZeta ((σ : ℂ) + I * ((2 * t : ℝ) : ℂ))).re +
      8 * (-deriv riemannZeta ((σ : ℂ) + I * ((3 * t : ℝ) : ℂ)) /
        riemannZeta ((σ : ℂ) + I * ((3 * t : ℝ) : ℂ))).re +
      (-deriv riemannZeta ((σ : ℂ) + I * ((4 * t : ℝ) : ℂ)) /
        riemannZeta ((σ : ℂ) + I * ((4 * t : ℝ) : ℂ))).re := by
  have hs (u : ℝ) : HasSum
      (fun n => (LSeries.term (↗Λ) ((σ : ℂ) + I * (u : ℂ)) n).re)
      (-deriv riemannZeta ((σ : ℂ) + I * (u : ℂ)) /
        riemannZeta ((σ : ℂ) + I * (u : ℂ))).re := by
    have hre : 1 < ((σ : ℂ) + I * (u : ℂ)).re := by simpa using hσ
    have h := Complex.hasSum_re (LSeriesSummable_vonMangoldt hre).LSeriesHasSum
    rwa [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre] at h
  have h := ((((hs 0).mul_left 35).add ((hs t).mul_left 56)).add
    ((hs (2 * t)).mul_left 28)).add ((hs (3 * t)).mul_left 8)
  have hsum := h.add (hs (4 * t))
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at hsum
  rw [← hsum.tsum_eq]
  exact tsum_nonneg (quartic_mangoldt_terms_nonneg σ t)

end LiuWang.Proof.ChebyshevBound.HighHeight
