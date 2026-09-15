import LiuWang.Proof.MultiZeroRepulsion.FullWindow

/-! An actual two-point mother with full multiplicities in the nondegenerate primitive branch. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem primitive_multiplicity_bound {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {rho : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK rho.im +
      (analyticOrderNatAt chi.LFunction rho : ℝ) / (sigma - rho.re) ≤
      stechkinConductorCoeff *
        (Real.log q + Real.log (max 1 |rho.im|) - Real.log Real.pi) + 4 / 15 := by
  have hm := primitive_ordinary_mass_le hc hp hs rho.im {rho}
    (by intro z hz; simpa only [Finset.mem_singleton.mp hz] using hr)
  simp only [Finset.sum_singleton] at hm
  have hk := mul_le_mul_of_nonneg_left (selected_pair_dominates hs ⟨by linarith, hr1⟩)
    (Nat.cast_nonneg (analyticOrderNatAt chi.LFunction rho) : (0 : ℝ) ≤ _)
  change _ ≤ (analyticOrderNatAt chi.LFunction rho : ℝ) * reflectedKernel sigma rho.im rho at hk
  rw [mul_one_div] at hk
  linarith [primitive_full_zero_sum_bound hc hp hs hs1 rho.im]

theorem pair_primitive_function {q : ℕ} [NeZero q]
    {chi psi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (hd : psi ≠ 1) (hpr : psi.IsPrimitive) (hm : chi * psi ≠ 1) (hi : chi * psi⁻¹ ≠ 1)
    {rho tau : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    (ht : 1 / 2 < tau.re) (ht1 : tau.re < 1) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    (analyticOrderNatAt chi.LFunction rho : ℝ) / (sigma - rho.re) +
      (analyticOrderNatAt psi.LFunction tau : ℝ) / (sigma - tau.re) ≤
      1 / (sigma - 1) + stechkinConductorCoeff *
        (3 * Real.log q + Real.log (max 1 |rho.im|) + Real.log (max 1 |tau.im|) +
          (Real.log (max 1 |rho.im + tau.im|) + Real.log (max 1 |rho.im - tau.im|)) / 2 -
            3 * Real.log Real.pi) + 1 / 20 := by
  have he := pair_euler_nonneg chi psi hs rho.im tau.im
  simp only [Fin.sum_univ_succ, pairCoefficients, pairCharacters, pairHeights,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, one_mul] at he
  have h0 := principal_real_strong (q := q) hs hs1
  have hchi := primitive_multiplicity_bound hc hp hr hr1 hs hs1
  have hpsi := primitive_multiplicity_bound hd hpr ht ht1 hs hs1
  have hmul := imprimitive_level_bound (chi * psi) hm hs hs1 (rho.im + tau.im)
  have hinv := imprimitive_level_bound (chi * psi⁻¹) hi hs hs1 (rho.im - tau.im)
  linarith

theorem paired_height_logs {q : ℕ} [NeZero q] {x t u : ℝ}
    (hq : (q : ℝ) ≤ x) (ht : |t| ≤ x / q) (hu : |u| ≤ x / q) :
    Real.log q + Real.log (max 1 |t + u|) ≤ Real.log x + Real.log 2 ∧
      Real.log q + Real.log (max 1 |t - u|) ≤ Real.log x + Real.log 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hx : 0 < x := hq0.trans_le hq
  have hq2 : (q : ℝ) ≤ 2 * x := by linarith
  have hp : |t + u| ≤ (2 * x) / q := by
    have hh := abs_add_le t u
    rw [mul_div_assoc]
    linarith
  have hm : |t - u| ≤ (2 * x) / q := by
    have hh := abs_sub t u
    rw [mul_div_assoc]
    linarith
  have hlp := conductor_height_log_max_le hq2 hp
  have hlm := conductor_height_log_max_le hq2 hm
  rw [Real.log_mul (by norm_num) hx.ne'] at hlp hlm
  constructor <;> linarith

theorem pair_primitive_global {q : ℕ} [NeZero q] {x : ℝ}
    (hq : (q : ℝ) ≤ x) {chi psi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (hd : psi ≠ 1) (hpr : psi.IsPrimitive)
    (hm : chi * psi ≠ 1) (hi : chi * psi⁻¹ ≠ 1)
    {rho tau : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    (ht : 1 / 2 < tau.re) (ht1 : tau.re < 1)
    (hry : |rho.im| ≤ x / q) (hty : |tau.im| ≤ x / q)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    (analyticOrderNatAt chi.LFunction rho : ℝ) / (sigma - rho.re) +
      (analyticOrderNatAt psi.LFunction tau : ℝ) / (sigma - tau.re) ≤
      1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log x := by
  have hh := pair_primitive_function hc hp hd hpr hm hi hr hr1 ht ht1 hs hs1
  have hl1 := conductor_height_log_max_le hq hry
  have hl2 := conductor_height_log_max_le hq hty
  have hl3 := paired_height_logs hq hry hty
  have hlog : 3 * Real.log q + Real.log (max 1 |rho.im|) + Real.log (max 1 |tau.im|) +
      (Real.log (max 1 |rho.im + tau.im|) + Real.log (max 1 |rho.im - tau.im|)) / 2 -
        3 * Real.log Real.pi ≤ 3 * Real.log x + Real.log 2 - 3 * Real.log Real.pi := by
    linarith [hl3.1, hl3.2]
  have hmult := mul_le_mul_of_nonneg_left hlog conductorCoeff_bounds.1
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    dsimp [stechkinConductorCoeff]
    linarith [stechkinK_le]
  have hpi := LiuWang.Proof.ChebyshevBound.HighHeight.log_pi_ge_one
  have htwo := Real.log_two_lt_d9
  have hconst : stechkinConductorCoeff * (Real.log 2 - 3 * Real.log Real.pi) + 1 / 20 ≤ 0 := by
    nlinarith
  nlinarith

end LiuWang.Proof.MultiZeroRepulsion.Continuation
