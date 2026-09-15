import LiuWang.Proof.PrincipalPsi.Quantitative.BadPrimeCorrection

/-! # 全部普通主字符的原闭高零点公式：更强系数 1.374954 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.PrincipalPsi.Quantitative

theorem principal_psi_formula_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP1 N)
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖ExplicitPerron.psi (1 : DirichletCharacter ℂ q) t - (t : ℂ) +
        highZeroSum q t (sourceT N)‖ ≤ 1.374954 * t / sourceT N * sourceL N ^ 2 := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hN2 : 2 ≤ N := by
    have h := sourceL_ge_2000 hN
    have he := Real.add_one_le_exp (2000 : ℝ)
    have hn : (2 : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast hn
  have hbad := (norm_principal_psi_sub_modulus_one_le hq0 hN2 hthi).trans
    (badMass_cost_source_le hN hq htlo)
  have hzeta := modulus_one_psi_formula_source hN htlo hthi
  rw [highZeroSum_eq_zeta]
  calc
    _ = ‖(ExplicitPerron.psi (1 : DirichletCharacter ℂ 1) t - (t : ℂ) +
        highZeroSum 1 t (sourceT N)) +
        (ExplicitPerron.psi (1 : DirichletCharacter ℂ q) t -
          ExplicitPerron.psi (1 : DirichletCharacter ℂ 1) t)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ 1.374953 * t / sourceT N * sourceL N ^ 2 +
        0.000001 * t / sourceT N * sourceL N ^ 2 := add_le_add hzeta hbad
    _ = _ := by ring

theorem principal_psi_formula_values {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP1 N)
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖ExplicitPerron.psi (1 : DirichletCharacter ℂ q) t - (t : ℂ) +
        ∑ rho ∈ highZeroValues q (sourceT N),
          (analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction rho : ℂ) *
            ((t : ℂ) ^ rho / rho)‖ ≤ 1.374954 * t / sourceT N * sourceL N ^ 2 := by
  rw [sum_highZeroValues_multiplicity]
  exact principal_psi_formula_source hN hq htlo hthi

theorem principal_character_psi_formula {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ))
    (chi : DirichletCharacter ℂ q) (hchi : chi = 1)
    {t : ℝ} (htlo : (N : ℝ) / 1000 ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖ExplicitPerron.psi chi t - (t : ℂ) +
        ∑ rho ∈ highZeroValues q ((Real.log (N : ℝ)) ^ (15 : ℕ)),
          (analyticOrderNatAt chi.LFunction rho : ℂ) * ((t : ℂ) ^ rho / rho)‖ ≤
      1.374954 * t / (Real.log (N : ℝ)) ^ (15 : ℕ) * (Real.log (N : ℝ)) ^ 2 := by
  subst chi
  exact principal_psi_formula_values hN hq htlo hthi

theorem principal_psi_formula_regression {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP1 N)
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖ExplicitPerron.psi (1 : DirichletCharacter ℂ q) t - (t : ℂ) +
        highZeroSum q t (sourceT N)‖ ≤ 1.3804 * t / sourceT N * sourceL N ^ 2 := by
  apply (principal_psi_formula_source hN hq htlo hthi).trans
  have hT0 := sourceT_pos hN
  have ht0 := hT0.trans (sourceT_lt_real_endpoint hN htlo)
  have hscale : 0 ≤ t / sourceT N * sourceL N ^ 2 := by positivity
  calc
    _ = 1.374954 * (t / sourceT N * sourceL N ^ 2) := by ring
    _ ≤ 1.3804 * (t / sourceT N * sourceL N ^ 2) :=
      mul_le_mul_of_nonneg_right (by norm_num) hscale
    _ = _ := by ring

end LiuWang.Proof.PrincipalPsi.Quantitative
