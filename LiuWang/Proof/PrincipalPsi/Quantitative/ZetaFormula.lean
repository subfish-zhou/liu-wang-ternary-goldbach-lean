import LiuWang.Proof.PrincipalPsi.Quantitative.SourceBudget

/-! # 无条件真实 ζ 原端点公式：保留更强系数 1.374953 -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.NonSymmetricContour
open LiuWang.Proof.LocalAnalyticBounds

namespace LiuWang.Proof.PrincipalPsi.Quantitative

theorem zeta_psi_formula_source {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖(Chebyshev.psi t : ℂ) - (t : ℂ) + highZeroSum 1 t (sourceT N)‖ ≤
      1.374953 * t / sourceT N * sourceL N ^ 2 := by
  obtain ⟨Hp, Hm, hp, hm, hsep⟩ := exists_xi_rectangle_heights (sourceT N)
  have hT0 := sourceT_pos hN
  have hT2 : 2 ≤ sourceT N :=
    (by norm_num : (2 : ℝ) ≤ 2000 ^ (15 : ℕ)).trans (sourceT_large hN)
  have hp0 : 0 < Hp := by linarith [(abs_le.mp hp).1]
  have hm0 : Hm < 0 := by linarith [(abs_le.mp hm).2]
  have hpa : |(|Hp|) - sourceT N| ≤ 1 := by rwa [abs_of_pos hp0]
  have hma : |(|Hm|) - sourceT N| ≤ 1 := by
    rw [abs_of_neg hm0, show -Hm - sourceT N = -(Hm + sourceT N) by ring, abs_neg]
    exact hm
  have htbig := HorizontalEstimate.source_endpoint_ge_billion hN htlo
  have ht0 : 0 < t := by linarith
  have hb : 1 < 1 + 1 / sourceL N := by
    have hh := one_div_pos.mpr (sourceL_pos hN)
    linarith
  have hborder := zeta_selected_border hb hp0 hm0 (heightSeparationBudget_pos _)
    (fun p => (hsep p).1) (fun p => (hsep p).2)
  have hrect := zeta_right_add_rectangle_zeros ht0 hb hp0 hm0 hborder
  have hleft := norm_left_source_le hN htlo hp hm
  have hupper := norm_horizontal_source_le hN htlo hthi hpa (fun p => (hsep p).1)
  have hlower := norm_horizontal_source_le hN htlo hthi hma (fun p => (hsep p).2)
  have hthree : ‖threeSides (zetaCenteredIntegrand t) (1 + 1 / sourceL N) Hp Hm‖ ≤
      0.000601 * t / sourceT N * sourceL N ^ 2 := by
    have hh := (norm_sub_le
      (verticalIntegral (zetaCenteredIntegrand t) (-1 / 2) Hp Hm +
        horizontalIntegral (zetaCenteredIntegrand t) (1 + 1 / sourceL N) Hp)
      (horizontalIntegral (zetaCenteredIntegrand t) (1 + 1 / sourceL N) Hm)).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    unfold threeSides
    calc
      _ ≤ _ := hh
      _ ≤ (0.000001 * t / sourceT N * sourceL N ^ 2 +
          0.0003 * t / sourceT N * sourceL N ^ 2) +
          0.0003 * t / sourceT N * sourceL N ^ 2 :=
        add_le_add (add_le_add hleft hupper) hlower
      _ = _ := by ring
  have htransport := (norm_transport_to_closed (by linarith : 1 ≤ t)
    (by linarith : 1 < sourceT N) hp hm).trans (transport_cost_source_le hN htlo)
  have hlow := (norm_closedCentered_sub_high_le (by linarith : 2.5 ≤ t) hT0.le).trans
    (low_center_cost_source_le hN htlo)
  have hperron := zeta_right_perron_strong hN htlo hthi hm hp
  have hcenter : ‖(2.5 : ℂ)‖ ≤ 0.000001 * t / sourceT N * sourceL N ^ 2 := by
    simpa only [show ‖(2.5 : ℂ)‖ = (2.5 : ℝ) by norm_num [Complex.norm_def]] using
      pole_center_cost_le_source hN htlo
  let R := zetaRightIntegral t (1 + 1 / sourceL N) Hm Hp
  let Z := xiRectangleCenteredSum t Hp Hm
  let C := closedCenteredZeroSum 1 t (sourceT N)
  let A := highZeroSum 1 t (sourceT N)
  calc
    _ = ‖(R - ((t : ℂ) - 2.5) + Z) - (R - (Chebyshev.psi t : ℂ)) -
        (Z - C) - (C - A) - (2.5 : ℂ)‖ := by
      congr 1
      dsimp [R, Z, C, A]
      ring
    _ ≤ ‖R - ((t : ℂ) - 2.5) + Z‖ + ‖R - (Chebyshev.psi t : ℂ)‖ +
        ‖Z - C‖ + ‖C - A‖ + ‖(2.5 : ℂ)‖ :=
      (norm_sub_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add
          ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ 0.000601 * t / sourceT N * sourceL N ^ 2 +
        1.374 * t / sourceT N * sourceL N ^ 2 +
        0.00035 * t / sourceT N * sourceL N ^ 2 +
        0.000001 * t / sourceT N * sourceL N ^ 2 +
        0.000001 * t / sourceT N * sourceL N ^ 2 := by
      apply add_le_add (add_le_add (add_le_add (add_le_add ?_ hperron) htransport) hlow) hcenter
      simpa only [R, Z, hrect] using hthree
    _ = _ := by ring

theorem modulus_one_psi_formula_source {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖ExplicitPerron.psi (1 : DirichletCharacter ℂ 1) t - (t : ℂ) +
        highZeroSum 1 t (sourceT N)‖ ≤ 1.374953 * t / sourceT N * sourceL N ^ 2 := by
  rw [psi_mod_one_eq_chebyshev]
  exact zeta_psi_formula_source hN htlo hthi

end LiuWang.Proof.PrincipalPsi.Quantitative
