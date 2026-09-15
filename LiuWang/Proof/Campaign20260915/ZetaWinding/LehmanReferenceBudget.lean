import LiuWang.Proof.Campaign20260915.ZetaWinding.LehmanGammaBudget

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped ComplexOrder

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.PrincipalPsi.Quantitative

theorem zeta_logDeriv_norm_le_real {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv riemannZeta s‖ ≤ -(logDeriv riemannZeta (s.re : ℂ)).re := by
  have h := norm_neg_logDeriv_LFunction_le_zeta_re (1 : DirichletCharacter ℂ 1) hs
  simp only [DirichletCharacter.LFunction_modOne_eq, neg_div, norm_neg, ← logDeriv_apply] at h
  have hn : 0 ≤ -logDeriv riemannZeta (s.re : ℂ) := by
    rw [logDeriv_apply, ← neg_div,
      ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
        (by simpa using hs : 1 < (s.re : ℂ).re)]
    apply tsum_nonneg
    intro n
    apply LSeries.term_nonneg
    exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have he := Complex.re_eq_norm.mpr hn
  rw [neg_re, norm_neg] at he
  exact h.trans_eq he.symm

theorem lehman_reference_mass_identity (T : ℝ) :
    (∑' p : RiemannXiDivisorZeroIndex,
      (1 / (horizontalAt T (3 / 2) - riemannXiDivisorZeroValue p)).re) =
      (logDeriv riemannZeta (horizontalAt T (3 / 2))).re +
      (1 / (horizontalAt T (3 / 2) - 1)).re - Real.log Real.pi / 2 +
      (digamma (horizontalAt T (3 / 2) / 2 + 1)).re / 2 := by
  have hs : 1 < (horizontalAt T (3 / 2)).re := by norm_num [horizontalAt]
  have ha : ∀ p : RiemannXiDivisorZeroIndex,
      horizontalAt T (3 / 2) ≠ riemannXiDivisorZeroValue p := by
    intro p he
    have h := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
    rw [← he] at h
    linarith
  rw [← xi_uncompensated_logDeriv ha,
    logDeriv_xi_eq_zeta (by linarith)
      (by intro he; simp [he] at hs) (riemannZeta_ne_zero_of_one_lt_re hs)]
  simp [mul_re]
  ring

theorem lehman_reference_mass_error {T : ℝ} (hT : 0 < T) :
    |(∑' p : RiemannXiDivisorZeroIndex,
        (1 / (horizontalAt T (3 / 2) - riemannXiDivisorZeroValue p)).re) -
      ((logDeriv riemannZeta (horizontalAt T (3 / 2))).re +
        Real.log (T / (2 * Real.pi)) / 2)| ≤ 137 / (16 * T ^ 2) := by
  have hd := lehman_digamma_uniform_error hT (x := 3 / 2) (by constructor <;> norm_num)
  have hp :
      0 ≤ (1 / (horizontalAt T (3 / 2) - 1)).re ∧
        (1 / (horizontalAt T (3 / 2) - 1)).re ≤ 1 / (2 * T ^ 2) := by
    have he : (1 / (horizontalAt T (3 / 2) - 1)).re =
        (1 / 2) / (1 / 4 + T ^ 2) := by
      simp [one_div, inv_re, normSq_apply, horizontalAt]
      ring
    rw [he]
    constructor
    · positivity
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have hlog : Real.log (T / (2 * Real.pi)) = Real.log (T / 2) - Real.log Real.pi := by
    rw [← div_div, Real.log_div (div_ne_zero hT.ne' (by norm_num)) Real.pi_ne_zero]
  rw [lehman_reference_mass_identity, hlog]
  rw [abs_le] at hd ⊢
  have he : 137 / (16 * T ^ 2) = 1 / (2 * T ^ 2) + (129 / (8 * T ^ 2)) / 2 := by
    field_simp
    ring
  rw [he]
  constructor <;> linarith [hd.1, hd.2, hp.1, hp.2]

theorem lehman_reference_original_error {T : ℝ} (hT : 168 * Real.pi < T) :
    |(∑' p : RiemannXiDivisorZeroIndex,
        (1 / (horizontalAt T (3 / 2) - riemannXiDivisorZeroValue p)).re) -
      ((logDeriv riemannZeta (horizontalAt T (3 / 2))).re +
        Real.log (T / (2 * Real.pi)) / 2)| < 1 / 10000 := by
  have ht : 504 < T := by linarith [Real.pi_gt_three]
  refine (lehman_reference_mass_error (by linarith : 0 < T)).trans_lt ?_
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [sq_nonneg (T - 504)]

theorem lehman_reference_mass_upper {T : ℝ} (hT : 168 * Real.pi < T) :
    (∑' p : RiemannXiDivisorZeroIndex,
      (1 / (horizontalAt T (3 / 2) - riemannXiDivisorZeroValue p)).re) <
      -(logDeriv riemannZeta (3 / 2)).re + Real.log (T / (2 * Real.pi)) / 2 + 1 / 10000 := by
  have he := (abs_lt.mp (lehman_reference_original_error hT)).2
  have hz := (re_le_norm (logDeriv riemannZeta (horizontalAt T (3 / 2)))).trans
    (zeta_logDeriv_norm_le_real (by norm_num [horizontalAt]))
  have hs : ((horizontalAt T (3 / 2)).re : ℂ) = 3 / 2 := by norm_num [horizontalAt]
  rw [hs] at hz
  linarith

#print axioms zeta_logDeriv_norm_le_real
#print axioms lehman_reference_mass_identity
#print axioms lehman_reference_original_error
#print axioms lehman_reference_mass_upper

end LiuWang.Proof.Campaign20260915.ZetaWinding
