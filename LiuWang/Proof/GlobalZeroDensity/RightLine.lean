import LiuWang.Proof.GlobalZeroDensity.Detector
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds

/-!
The full Mobius inverse gives an actual tail estimate stronger than the
divisor-majorized tail on Re(s)=2. No density or zero-count estimate is assumed.
-/

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory Set

namespace LiuWang.Proof.GlobalZeroDensity

theorem norm_mu_term_le {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ‖LSeries.term (fun k => (ArithmeticFunction.moebius k : ℂ)) s n‖ ≤
      (n : ℝ) ^ (-s.re) := by
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : -s.re ≠ 0)]
  · rw [LSeries.norm_term_eq, if_neg hn, Real.rpow_neg (Nat.cast_nonneg n)]
    rw [← one_div]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

theorem norm_zeta_le {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / (s.re - 1) := by
  rw [← LSeries_one_eq_riemannZeta hs]
  have hsum := LSeriesSummable_one_iff.mpr hs
  calc
    ‖LSeries 1 s‖ ≤ ∑' n, ‖LSeries.term 1 s n‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) := by
      apply hsum.norm.tsum_le_tsum _ (Real.summable_nat_rpow.mpr (by linarith))
      intro n
      by_cases hn : n = 0
      · subst n; simp [Real.zero_rpow (by linarith : -s.re ≠ 0)]
      · rw [LSeries.norm_term_eq, if_neg hn]
        simp only [Pi.one_apply, norm_one, Real.rpow_neg (Nat.cast_nonneg n), one_div,
          le_refl]
    _ ≤ _ := AnalyticNumberTheory.LargeSieve.tsum_nat_rpow_neg_le _ hs

theorem f_eq_moebius_tail {s : ℂ} (hs : 1 < s.re) (y : ℝ) :
    f y s = -riemannZeta s *
      ∑' n : ℕ, LSeries.term (fun k => (ArithmeticFunction.moebius k : ℂ)) s
        (n + ⌈y⌉₊) := by
  have hsum := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hsplit := hsum.sum_add_tsum_nat_add ⌈y⌉₊
  have hQ : (∑ n ∈ range ⌈y⌉₊,
      LSeries.term (fun k => (ArithmeticFunction.moebius k : ℂ)) s n) = Q y s := by
    apply sum_congr rfl
    intro n _
    by_cases hn : n = 0
    · subst n; simp
    · exact LSeries.term_of_ne_zero hn _ _
  rw [hQ] at hsplit
  have hinv := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hinv
  change riemannZeta s * (∑' n, LSeries.term
    (fun k => (ArithmeticFunction.moebius k : ℂ)) s n) = 1 at hinv
  rw [← hsplit] at hinv
  unfold f
  rw [← hinv]
  ring

theorem rpow_tail_le {σ : ℝ} (hσ : 1 < σ) {N : ℕ} (hN : 2 ≤ N) :
    (∑' n : ℕ, ((n + N : ℕ) : ℝ) ^ (-σ)) ≤
      ((N : ℝ) - 1) ^ (1 - σ) / (σ - 1) := by
  have hN1 : 1 ≤ N := by omega
  have hpos : (0 : ℝ) < (N - 1 : ℕ) := by exact_mod_cast (show 0 < N - 1 by omega)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Ici ((N - 1 : ℕ) : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -σ ≤ 0)).mono
      (Ici_subset_Ioi.mpr hpos)
  have ht := hanti.tsum_comp_add_le_integral (N - 1)
    (integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) hpos)
    (fun t ht => Real.rpow_nonneg (hpos.le.trans (mem_Ioi.mp ht).le) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) hpos] at ht
  simp only [Nat.add_assoc, Nat.sub_add_cancel hN1, Nat.cast_sub hN1, Nat.cast_one] at ht
  convert ht using 1
  rw [show -σ + 1 = 1 - σ by ring]
  rw [show 1 - σ = -(σ - 1) by ring, neg_div_neg_eq]

theorem norm_f_le_right {s : ℂ} (hs : 1 < s.re) {y : ℝ} (hy : 1 < y) :
    ‖f y s‖ ≤ (1 + 1 / (s.re - 1)) *
      (((⌈y⌉₊ : ℝ) - 1) ^ (1 - s.re) / (s.re - 1)) := by
  have hmu := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have htail : Summable (fun n : ℕ =>
      LSeries.term (fun k => (ArithmeticFunction.moebius k : ℂ)) s (n + ⌈y⌉₊)) :=
    (summable_nat_add_iff ⌈y⌉₊).mpr hmu
  have hp : Summable (fun n : ℕ => ((n + ⌈y⌉₊ : ℕ) : ℝ) ^ (-s.re)) :=
    (summable_nat_add_iff ⌈y⌉₊).mpr (Real.summable_nat_rpow.mpr (by linarith))
  have hN : 2 ≤ ⌈y⌉₊ := by
    have : 1 < ⌈y⌉₊ := Nat.lt_ceil.mpr (by simpa using hy)
    omega
  rw [f_eq_moebius_tail hs y, norm_mul, norm_neg]
  apply mul_le_mul (norm_zeta_le hs) _ (norm_nonneg _) (by positivity)
  exact (norm_tsum_le_tsum_norm htail.norm).trans
    ((htail.norm.tsum_le_tsum (fun n => norm_mu_term_le hs _) hp).trans
      (rpow_tail_le hs hN))

theorem norm_f_two_le {s : ℂ} (hs : s.re = 2) {y : ℝ} (hy : 1 < y) :
    ‖f y s‖ ≤ 2 / (y - 1) := by
  have ht := norm_f_le_right (s := s) (by rw [hs]; norm_num) hy
  have hceil : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have heq : (1 + 1 / (s.re - 1)) *
      (((⌈y⌉₊ : ℝ) - 1) ^ (1 - s.re) / (s.re - 1)) =
      2 / ((⌈y⌉₊ : ℝ) - 1) := by
    rw [hs]
    norm_num [Real.rpow_neg_one, div_eq_mul_inv]
  rw [heq] at ht
  exact ht.trans (div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith))

theorem H_ne_zero_on_two {s : ℂ} (hs : s.re = 2) {y : ℝ} (hy : 3 < y) :
    H y s ≠ 0 := by
  have hf : ‖f y s‖ < 1 :=
    (norm_f_two_le hs (by linarith)).trans_lt ((div_lt_one (by linarith)).mpr (by linarith))
  intro hz
  have hp : f y s ^ 2 = 1 := (sub_eq_zero.mp hz).symm
  have hn := congrArg norm hp
  rw [norm_pow, norm_one] at hn
  nlinarith [norm_nonneg (f y s)]

theorem M_two_le (y : ℝ) (hy : 1 < y) {u : ℝ} (hu : 0 ≤ u) :
    M y 2 u ≤ 8 * u / (y - 1) ^ 2 := by
  have hI := intervalIntegrable_F y u (σ := 2) (by norm_num)
  have hbound : ∀ t : ℝ, F y ((2 : ℂ) + t * Complex.I) ≤ (2 / (y - 1)) ^ 2 := by
    intro t
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_f_two_le (by simp) hy) 2
  have hi := intervalIntegral.integral_mono_on (by linarith : -u ≤ u)
    hI intervalIntegrable_const
    (fun t _ => hbound t)
  simp only [M, Complex.ofReal_ofNat] at hi ⊢
  rw [intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  convert hi using 1
  field_simp
  ring

end LiuWang.Proof.GlobalZeroDensity
