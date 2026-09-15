import LiuWang.Proof.Campaign20260915.ZetaValidation.BernoulliStep
import LiuWang.Proof.Campaign20260915.ZetaValidation.NormalizedEvaluation

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Finset

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def risingProduct (s : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ range k, (s + j)

def eulerMaclaurinApprox (s : ℂ) (N : ℕ) : ℕ → ℂ
  | 0 => abelApprox s N
  | m + 1 => eulerMaclaurinApprox s N m +
      risingProduct s (m + 1) * (normalizedBernoulli (m + 2) 0 : ℂ) *
        (N : ℂ) ^ (-s - (m + 1 : ℕ))

theorem risingProduct_succ (s : ℂ) (k : ℕ) :
    risingProduct s (k + 1) = risingProduct s k * (s + k) := by
  simp [risingProduct, Finset.prod_range_succ]

theorem eulerMaclaurinApprox_eq_sum (s : ℂ) (N m : ℕ) :
    eulerMaclaurinApprox s N m = abelApprox s N +
      ∑ j ∈ range m, risingProduct s (j + 1) *
        ((bernoulli (j + 2) : ℂ) / (j + 2).factorial) *
          (N : ℂ) ^ (-s - (j + 1 : ℕ)) := by
  induction m with
  | zero => simp [eulerMaclaurinApprox]
  | succ m ih =>
      rw [eulerMaclaurinApprox, ih, Finset.sum_range_succ, normalizedBernoulli_zero]
      push_cast
      ring

theorem zeta_sub_eulerMaclaurinApprox (m : ℕ) {s : ℂ} (hs : 1 / 10 < s.re)
    (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s - eulerMaclaurinApprox s N m =
      -risingProduct s (m + 1) * ∫ u in Ioi (N : ℝ), bernoulliKernel (m + 1) s u := by
  induction m with
  | zero =>
      simpa [eulerMaclaurinApprox, risingProduct, bernoulliKernel_first] using
        zeta_sub_abelApprox hs hs1 hN
  | succ m ih =>
      rw [eulerMaclaurinApprox, sub_add_eq_sub_sub, ih,
        bernoulli_tail_step (m + 1) (by omega) (by linarith : 0 < s.re) hN,
        risingProduct_succ s (m + 1)]
      ring

theorem norm_zeta_sub_eulerMaclaurinApprox_le (m : ℕ) {s : ℂ} (hs : 1 / 10 < s.re)
    (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - eulerMaclaurinApprox s N m‖ ≤
      ‖risingProduct s (m + 1)‖ * (bernoulliCoefficientBound (m + 1) : ℝ) *
        (N : ℝ) ^ (-s.re - m) / (s.re + m) := by
  rw [zeta_sub_eulerMaclaurinApprox m hs hs1 hN, norm_mul, norm_neg]
  have hb := norm_bernoulliTail_le (m + 1) (s := s)
    (by push_cast; linarith : 1 < s.re + (m + 1 : ℕ))
    (a := N) (by exact_mod_cast (show 0 < N by omega))
  have h := mul_le_mul_of_nonneg_left hb (norm_nonneg (risingProduct s (m + 1)))
  push_cast at h
  rw [show (1 : ℝ) - s.re - ((m : ℝ) + 1) = -s.re - m by ring,
    show s.re + ((m : ℝ) + 1) - 1 = s.re + m by ring] at h
  simpa only [mul_div_assoc, mul_assoc] using h

theorem norm_risingProduct_le (s : ℂ) (m : ℕ) :
    ‖risingProduct s (m + 1)‖ ≤ (‖s‖ + m) ^ (m + 1) := by
  rw [risingProduct, norm_prod]
  calc
    _ ≤ ∏ _j ∈ range (m + 1), (‖s‖ + m) := by
      apply Finset.prod_le_prod (fun (j : ℕ) _ => norm_nonneg (s + j))
      intro j hj
      have hjm : j ≤ m := by have h := Finset.mem_range.mp hj; omega
      have hjR : (j : ℝ) ≤ m := by exact_mod_cast hjm
      have h := norm_add_le s (j : ℂ)
      rw [Complex.norm_natCast] at h
      linarith
    _ = _ := by simp

theorem eulerMaclaurin_uniform_error (m : ℕ) {s : ℂ} (hs : 1 / 10 < s.re)
    (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - eulerMaclaurinApprox s N m‖ ≤
      (‖s‖ + m) ^ (m + 1) * (bernoulliCoefficientBound (m + 1) : ℝ) *
        (N : ℝ) ^ (-s.re - m) / (s.re + m) := by
  apply (norm_zeta_sub_eulerMaclaurinApprox_le m hs hs1 hN).trans
  have hb : (0 : ℝ) ≤ (bernoulliCoefficientBound (m + 1) : ℝ) := by
    exact_mod_cast bernoulliCoefficientBound_nonneg (m + 1)
  have hn : 0 ≤ (N : ℝ) ^ (-s.re - m) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hd : 0 ≤ s.re + m := by linarith [Nat.cast_nonneg m (α := ℝ)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (norm_risingProduct_le s m) hb) hn) hd

theorem normalized_eulerMaclaurin_error (t : ℝ) (m : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    |normalizedCriticalZeta t -
      (eulerMaclaurinApprox (criticalPoint t) N m * criticalGammaPhase t).re| ≤
      (‖criticalPoint t‖ + m) ^ (m + 1) * (bernoulliCoefficientBound (m + 1) : ℝ) *
        (N : ℝ) ^ (-(1 / 2 : ℝ) - m) / (1 / 2 + m) := by
  have he : normalizedCriticalZeta t -
      (eulerMaclaurinApprox (criticalPoint t) N m * criticalGammaPhase t).re =
      ((riemannZeta (criticalPoint t) - eulerMaclaurinApprox (criticalPoint t) N m) *
        criticalGammaPhase t).re := by
    rw [sub_mul, sub_re, ← normalizedCriticalZeta_ofReal, ofReal_re]
  rw [he]
  have h := eulerMaclaurin_uniform_error m (s := criticalPoint t)
    (by norm_num [criticalPoint]) (criticalPoint_ne_one t) hN
  calc
    _ ≤ ‖(riemannZeta (criticalPoint t) - eulerMaclaurinApprox (criticalPoint t) N m) *
        criticalGammaPhase t‖ := abs_re_le_norm _
    _ = ‖riemannZeta (criticalPoint t) - eulerMaclaurinApprox (criticalPoint t) N m‖ := by
      rw [norm_mul, norm_criticalGammaPhase, mul_one]
    _ ≤ _ := by simpa only [criticalPoint] using h

#print axioms zeta_sub_eulerMaclaurinApprox
#print axioms eulerMaclaurin_uniform_error
#print axioms normalized_eulerMaclaurin_error

end LiuWang.Proof.Campaign20260915.ZetaValidation
