import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1Euler

/-! Same-q height budgets for the actual three-point combination, before principal degeneracies. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.NearOneDensity.Continuation

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem t1_height_log {d q : ℕ} [NeZero d] [NeZero q] (hdq : d ∣ q)
    {x k t : ℝ} (hq : (q : ℝ) ≤ x) (hk : 1 ≤ k) (ht : |t| ≤ k * x / q) :
    Real.log d + Real.log (max 1 |t|) ≤ Real.log x + Real.log k := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hd0 : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hx0 : 0 < x := hq0.trans_le hq
  have hk0 : 0 < k := by linarith
  have hxk : x ≤ k * x := by nlinarith
  have hd : (d : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) hdq
  have hm0 : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hm : max 1 |t| ≤ k * x / q :=
    max_le ((le_div_iff₀ hq0).mpr (by simpa using hq.trans hxk)) ht
  have hm' := mul_le_mul hd hm hm0.le hq0.le
  have he : (q : ℝ) * (k * x / q) = k * x := by field_simp
  rw [he] at hm'
  have hl := Real.log_le_log (mul_pos hd0 hm0) hm'
  rw [Real.log_mul hd0.ne' hm0.ne', Real.log_mul hk0.ne' hx0.ne'] at hl
  linarith

theorem t1G_primitive_bound {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f)
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (hc' : psi ≠ 1) (hp' : psi.IsPrimitive)
    (hc'' : eta ≠ 1) (hp'' : eta.IsPrimitive)
    (hde : t1Product chi psi ≠ 1) (hdf : t1Product chi eta ≠ 1)
    (hef : t1Product psi eta ≠ 1) (hdef : t1Product (t1Product chi psi) eta ≠ 1)
    (hdq : d ∣ q) (heq : e ∣ q) (hfq : f ∣ q) {x sigma : ℝ}
    (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20)
    {rho tau ups : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    (ht : 1 / 2 < tau.re) (ht1 : tau.re < 1) (hu : 1 / 2 < ups.re) (hu1 : ups.re < 1)
    (hry : |rho.im| ≤ x / q) (hty : |tau.im| ≤ x / q) (huy : |ups.im| ≤ x / q) :
    t1G chi psi eta sigma rho.im tau.im ups.im +
      (analyticOrderNatAt chi.LFunction rho : ℝ) / (sigma - rho.re) +
      (analyticOrderNatAt psi.LFunction tau : ℝ) / (sigma - tau.re) +
      (analyticOrderNatAt eta.LFunction ups : ℝ) / (sigma - ups.re) ≤
      1 / (sigma - 1) + 7 * stechkinConductorCoeff * Real.log x + 9 / 4 := by
  have h0 := zeta_real_strong hs hs1
  have h1 := primitive_multiplicity_bound hc hp hr hr1 hs hs1
  have h2 := primitive_multiplicity_bound hc' hp' ht ht1 hs hs1
  have h3 := primitive_multiplicity_bound hc'' hp'' hu hu1 hs hs1
  have h4 := general_nonprincipal_cost (t1Product chi psi) hde hs hs1 (rho.im + tau.im)
  have h5 := general_nonprincipal_cost (t1Product chi eta) hdf hs hs1 (rho.im + ups.im)
  have h6 := general_nonprincipal_cost (t1Product psi eta) hef hs hs1 (tau.im + ups.im)
  have h7 := general_nonprincipal_cost (t1Product (t1Product chi psi) eta) hdef hs hs1
    (rho.im + tau.im + ups.im)
  have hs1log := t1_height_log hdq hq (le_refl (1 : ℝ)) (by simpa using hry)
  have hs2log := t1_height_log heq hq (le_refl (1 : ℝ)) (by simpa using hty)
  have hs3log := t1_height_log hfq hq (le_refl (1 : ℝ)) (by simpa using huy)
  simp only [Real.log_one, add_zero] at hs1log hs2log hs3log
  have hpair {t u : ℝ} (ht : |t| ≤ x / q) (hu : |u| ≤ x / q) : |t + u| ≤ 2 * x / q := by
    have h := abs_add_le t u
    rw [mul_div_assoc]
    linarith
  have htriple : |rho.im + tau.im + ups.im| ≤ 3 * x / q := by
    have h := abs_add_le (rho.im + tau.im) ups.im
    have h' := hpair hry hty
    rw [mul_div_assoc] at h' ⊢
    linarith
  have h4log := t1_height_log (Nat.lcm_dvd hdq heq) hq (by norm_num : (1 : ℝ) ≤ 2) (hpair hry hty)
  have h5log := t1_height_log (Nat.lcm_dvd hdq hfq) hq (by norm_num : (1 : ℝ) ≤ 2) (hpair hry huy)
  have h6log := t1_height_log (Nat.lcm_dvd heq hfq) hq (by norm_num : (1 : ℝ) ≤ 2) (hpair hty huy)
  have h7log := t1_height_log (Nat.lcm_dvd (Nat.lcm_dvd hdq heq) hfq) hq
    (by norm_num : (1 : ℝ) ≤ 3) htriple
  have hlogs := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hs1log hs2log)
      hs3log) h4log) h5log) h6log) h7log) conductorCoeff_bounds.1
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  have hconst : stechkinConductorCoeff * (3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi) +
      7 * (4 / 15 : ℝ) + 4 * (941 / 1600) - 3 / 4 ≤ 9 / 4 := by
    nlinarith only [hk, Real.log_two_lt_d9, Real.log_three_lt_d9,
      LiuWang.Proof.NearOneDensity.log_pi_ge_eleven_tenths]
  unfold t1G
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, hlogs, hconst]

def t1Orient {d : ℕ} (chi : DirichletCharacter ℂ d) (b : Bool) : DirichletCharacter ℂ d :=
  if b then chi⁻¹ else chi

def t1OrientValue (rho : ℂ) (b : Bool) : ℂ := if b then conj rho else rho

theorem t1Orient_ne_one {d : ℕ} {chi : DirichletCharacter ℂ d} (hc : chi ≠ 1) (b : Bool) :
    t1Orient chi b ≠ 1 := by cases b <;> simp [t1Orient, hc]

theorem t1Orient_primitive {d : ℕ} [NeZero d] {chi : DirichletCharacter ℂ d}
    (hp : chi.IsPrimitive) (b : Bool) : (t1Orient chi b).IsPrimitive := by
  cases b
  · exact hp
  · exact BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hp

theorem t1Orient_order {d : ℕ} [NeZero d] (chi : DirichletCharacter ℂ d)
    {rho : ℂ} (hr : 0 < rho.re) (hr1 : rho.re < 1) (b : Bool) :
    analyticOrderNatAt (t1Orient chi b).LFunction (t1OrientValue rho b) =
      analyticOrderNatAt chi.LFunction rho := by
  cases b
  · rfl
  · exact ordinary_order_conjugate chi hr hr1

theorem t1OrientValue_re (rho : ℂ) (b : Bool) : (t1OrientValue rho b).re = rho.re := by
  cases b <;> simp [t1OrientValue]

theorem t1OrientValue_abs_im (rho : ℂ) (b : Bool) : |(t1OrientValue rho b).im| = |rho.im| := by
  cases b <;> simp [t1OrientValue]

end LiuWang.Proof.MultiZeroRepulsion.Continuation
