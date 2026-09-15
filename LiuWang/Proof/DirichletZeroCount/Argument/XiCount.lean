import LiuWang.Proof.DirichletZeroCount.Argument.ThreeSides

/-! # The actual xi rectangle and three-side counts for every principal character -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators ComplexConjugate
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.PrincipalPsi LiuWang.Proof.PrincipalPsi.Quantitative
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount.Argument

theorem xi_zero_strip {s : ℂ} (hz : riemannXi s = 0) : 0 < s.re ∧ s.re < 1 := by
  have hs0 : s ≠ 0 := by intro h; simp [h, riemannXi_zero] at hz
  obtain ⟨p, hp⟩ := BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
    differentiable_riemannXi riemannXi_nontrivial hs0 hz
  exact hp ▸ riemannXiDivisorZeroValue_re_mem_Ioo p

theorem xi_zero_iff_principal (q : ℕ) [NeZero q] {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1) :
    riemannXi s = 0 ↔ (1 : Character q).LFunction s = 0 := by
  have hne : s ≠ 1 := by intro h; simp [h] at hs1
  rw [xi_zero_iff_zeta_zero (by linarith) hne, principal_zero_iff_zeta_zero hs hne]

theorem xi_border_nonzero (q : ℕ) [NeZero q] {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H →
      (1 : Character q).LFunction s ≠ 0) :
    ∀ s ∈ RectangleBorder (lowerCorner b H) (upperCorner b H), riemannXi s ≠ 0 := by
  intro s hs hz
  have hr := xi_zero_strip hz
  have ht : |s.im| = H := by
    rcases (mem_border hb hH s).mp hs with ((hs | hs) | hs | hs)
    · rw [hs.2, abs_neg, abs_of_nonneg hH]
    · linarith [hs.1]
    · rw [hs.2, abs_of_nonneg hH]
    · linarith [hs.1]
  exact hreg s hr.1 hr.2 ht ((xi_zero_iff_principal q hr.1 hr.2).mp hz)

theorem xi_rectangle_count (q : ℕ) [NeZero q] {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H →
      (1 : Character q).LFunction s ≠ 0) :
    RectangleIntegral' (logDeriv riemannXi) (lowerCorner b H) (upperCorner b H) =
      (count (1 : Character q) 0 H : ℂ) := by
  have hV (s : ℂ) : s ∈ zeroValues (1 : Character q) 0 H ↔
      s ∈ Rectangle (lowerCorner b H) (upperCorner b H) ∧ riemannXi s = 0 := by
    rw [mem_zeroValues, mem_rectangle hb hH]
    constructor
    · rintro ⟨hz, ⟨h0, h1, ht⟩, _⟩
      exact ⟨⟨by linarith, by linarith, (abs_le.mp ht).1, (abs_le.mp ht).2⟩,
        (xi_zero_iff_principal q h0 h1).mpr hz⟩
    · rintro ⟨⟨_, _, hm, hp⟩, hz⟩
      have hr := xi_zero_strip hz
      exact ⟨(xi_zero_iff_principal q hr.1 hr.2).mp hz,
        ⟨hr.1, hr.2, abs_le.mpr ⟨hm, hp⟩⟩, hr.1.le⟩
  rw [entire_rectangle_count differentiable_riemannXi riemannXi_nontrivial
    (by simp [lowerCorner, upperCorner]; linarith)
    (by simp [lowerCorner, upperCorner]; linarith) (zeroValues (1 : Character q) 0 H) hV
    (xi_border_nonzero q hb hH hreg)]
  simp only [count, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hr := (mem_zeroValues.mp hs).2.1
  rw [analyticOrderNatAt_xi_eq_principal (q := q) hr.1 (by intro h; simp [h] at hr)]

theorem xi_conjugate (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := by
  have hr (z : ℂ) (hz : 1 < z.re) : riemannXi (conj z) = conj (riemannXi z) := by
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    have hcz1 : conj z ≠ 1 := by
      intro h
      apply hz1
      simpa using congrArg conj h
    rw [xi_eq_factor_regularized (by simpa using (show -2 < z.re by linarith)),
      xi_eq_factor_regularized (by linarith : -2 < z.re),
      regularizedPrincipal_eq hcz1, regularizedPrincipal_eq hz1]
    simp only [xiFactor, DirichletCharacter.LFunction_modOne_eq, riemannZeta_conj,
      map_mul, map_sub, map_one]
    have hpi : ((Real.pi : ℂ)).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
      exact Real.pi_ne_zero.symm
    have hp := Complex.cpow_conj (Real.pi : ℂ) (-z / 2) hpi
    simp only [map_neg, map_div₀, map_ofNat, Complex.conj_ofReal] at hp
    rw [hp]
    have hg : Gamma (conj z / 2 + 1) = conj (Gamma (z / 2 + 1)) := by
      simpa only [map_add, map_div₀, map_ofNat, map_one] using Gamma_conj (z / 2 + 1)
    rw [hg]
  have hd : Differentiable ℂ (conj ∘ riemannXi ∘ conj) := by
    intro z
    simpa only [Complex.conj_conj] using
      (differentiable_riemannXi.differentiableAt (x := conj z)).conj_conj
  have ha := differentiable_riemannXi.differentiableOn.analyticOnNhd isOpen_univ
  have hb := hd.differentiableOn.analyticOnNhd isOpen_univ
  have he : riemannXi =ᶠ[nhds (2 : ℂ)] conj ∘ riemannXi ∘ conj := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : 1 < (2 : ℂ).re)] with z hz
    simpa [Function.comp_def] using (congrArg conj (hr z hz)).symm
  have hfun := AnalyticOnNhd.eq_of_eventuallyEq ha hb he
  simpa [Function.comp_def] using (congrArg conj (congrFun hfun s)).symm

theorem xi_logDeriv_conjugate (s : ℂ) :
    logDeriv riemannXi (conj s) = conj (logDeriv riemannXi s) := by
  have hfun : riemannXi = conj ∘ riemannXi ∘ conj := by
    funext z
    simp [Function.comp_def, xi_conjugate]
  have hd := congrArg (fun f : ℂ → ℂ => deriv f (conj s)) hfun
  rw [deriv_conj_conj] at hd
  simp only [logDeriv_apply, hd, xi_conjugate, map_div₀, Function.comp_def, Complex.conj_conj]

theorem xi_logDeriv_reflection (s : ℂ) :
    logDeriv riemannXi (1 - conj s) = -conj (logDeriv riemannXi s) := by
  have hfun : (fun z : ℂ => riemannXi (1 - z)) = riemannXi :=
    funext riemannXi_one_sub
  have h : logDeriv (fun z : ℂ => riemannXi (1 - z)) (conj s) =
      -logDeriv riemannXi (1 - conj s) := by
    simpa [Function.comp_def] using
      (logDeriv_comp (f := riemannXi) (g := fun z : ℂ => 1 - z)
        (x := conj s) differentiable_riemannXi.differentiableAt (by fun_prop))
  rw [hfun] at h
  rw [xi_logDeriv_conjugate] at h
  linear_combination h

theorem principal_count_eq_three_im (q : ℕ) [NeZero q] {b H : ℝ}
    (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H →
      (1 : Character q).LFunction s ≠ 0) :
    (count (1 : Character q) 0 H : ℝ) =
      (rightThreeIntegral (logDeriv riemannXi) b H).im / Real.pi := by
  have hi := logDeriv_border_integrable differentiable_riemannXi (xi_border_nonzero q hb hH hreg)
  have h := (xi_rectangle_count q hb hH hreg).symm.trans
    (normalized_rectangle_eq_three_im hb xi_logDeriv_reflection hi)
  exact_mod_cast h

theorem exists_principal_three_count (q : ℕ) [NeZero q] {b y r : ℝ}
    (hb : 1 < b) (hy : 0 ≤ y) (hr : 0 < r) :
    ∃ H : ℝ, y < H ∧ H < y + r ∧
      (count (1 : Character q) 0 y : ℝ) =
        (rightThreeIntegral (logDeriv riemannXi) b H).im / Real.pi ∧
      ∀ alpha : ℝ, 0 ≤ alpha → (count (1 : Character q) alpha y : ℝ) ≤
        (rightThreeIntegral (logDeriv riemannXi) b H).im / Real.pi := by
  obtain ⟨H, hyH, hHr, hc, _, hreg⟩ := Applications.exists_common_count_plateau q (y := y) hr
  have he : (count (1 : Character q) 0 y : ℝ) =
      (rightThreeIntegral (logDeriv riemannXi) b H).im / Real.pi := by
    rw [← hc 1 0 H hyH.le le_rfl]
    exact principal_count_eq_three_im q hb (hy.trans hyH.le) (hreg 1)
  exact ⟨H, hyH, hHr, he, fun alpha ha =>
    (Nat.cast_le.mpr (count_antitone_alpha (1 : Character q) y ha)).trans_eq he⟩

end LiuWang.Proof.DirichletZeroCount.Argument
