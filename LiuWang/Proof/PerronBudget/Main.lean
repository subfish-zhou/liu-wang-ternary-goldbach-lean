import LiuWang.Proof.PerronBudget.Budget
import LiuWang.Proof.FixedHeightZeroSum.Main

/-!
# Paid actual Perron integral and primitive nonprincipal psi endpoint

The Perron estimate allows every character, including the modulus-one
principal character. Only the zero-sum endpoint uses primitivity and
nonprincipality. Heights are selected once before quantifying over `t`.
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ExplicitPerron LiuWang.Proof.FixedHeightZeroSum
open LiuWang.Proof.NonSymmetricContour

namespace LiuWang.Proof.PerronBudget

theorem sourceDomain_right_perron_paid {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hN : Real.exp 2000 ≤ (N : ℝ))
    {t Hminus Hplus : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ))
    (hminus : |Hminus + sourceT N| ≤ 1) (hplus : |Hplus - sourceT N| ≤ 1) :
    ‖vertical (centeredIntegrand chi t (5 / 2)) (1 + 1 / sourceL N) Hminus Hplus -
        psi chi t‖ ≤ 1.38022 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
  (ExplicitPerron.sourceDomain_right_perron chi hN htlo hminus hplus).trans
    (closedRealEndpointError_le_source hN htlo hthi hminus hplus)

theorem centered_vertical_eq_actual_right {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t b Hminus Hplus : ℝ) :
    vertical (centeredIntegrand chi t (5 / 2)) b Hminus Hplus =
      actualRightVerticalIntegral chi t 2.5 b Hminus Hplus := by
  unfold vertical centeredIntegrand actualRightVerticalIntegral
  norm_num

theorem source_budget_add : (1.38022 : ℝ) + 0.000171 = 1.380391 := by norm_num

theorem exists_paid_estimates_all_real_endpoints
    {N q : ℕ} [NeZero q] (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 3 ≤ q)
    (hqUpper : (q : ℝ) ≤ sourceP1 N) {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    ∃ Hplus Hminus, AdmissibleHeights N chi Hplus Hminus ∧
      ∀ t : ℝ, sourceWindowLower N ≤ t → t ≤ (N : ℝ) →
        ‖actualRightVerticalIntegral chi t 2.5 (1 + 1 / sourceL N) Hminus Hplus -
            psi chi t‖ ≤ 1.38022 * t / sourceT N * sourceL N ^ (2 : ℕ) ∧
        ‖actualRightVerticalIntegral chi t 2.5 (1 + 1 / sourceL N) Hminus Hplus +
            highZeroSum chi t (sourceT N)‖ ≤
          0.000171 * t / sourceT N * sourceL N ^ (2 : ℕ) ∧
        ‖psi chi t + highZeroSum chi t (sourceT N)‖ ≤
          1.380391 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  obtain ⟨Hp, Hm, hh, hzero⟩ :=
    exists_actual_high_zero_estimate_all_real_endpoints hN hq hqUpper hchi hPrimitive
  refine ⟨Hp, Hm, hh, ?_⟩
  intro t htlo hthi
  have hP := sourceDomain_right_perron_paid chi hN htlo hthi hh.2.1 hh.1
  rw [centered_vertical_eq_actual_right] at hP
  have hZ := hzero t htlo hthi
  refine ⟨hP, hZ, ?_⟩
  let R := actualRightVerticalIntegral chi t 2.5 (1 + 1 / sourceL N) Hm Hp
  calc
    _ = ‖(R + highZeroSum chi t (sourceT N)) - (R - psi chi t)‖ := by congr 1; abel
    _ ≤ ‖R + highZeroSum chi t (sourceT N)‖ + ‖R - psi chi t‖ := norm_sub_le _ _
    _ ≤ 0.000171 * t / sourceT N * sourceL N ^ (2 : ℕ) +
        1.38022 * t / sourceT N * sourceL N ^ (2 : ℕ) := add_le_add hZ hP
    _ = ((1.38022 : ℝ) + 0.000171) * t / sourceT N * sourceL N ^ (2 : ℕ) := by ring
    _ = _ := by rw [source_budget_add]

theorem psi_highZeroSum_source_all_real_endpoints
    {N q : ℕ} [NeZero q] (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 3 ≤ q)
    (hqUpper : (q : ℝ) ≤ sourceP1 N) {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    ∀ t : ℝ, sourceWindowLower N ≤ t → t ≤ (N : ℝ) →
      ‖psi chi t + highZeroSum chi t (sourceT N)‖ ≤
        1.380391 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  obtain ⟨_, _, _, hall⟩ := exists_paid_estimates_all_real_endpoints hN hq hqUpper hchi hPrimitive
  exact fun t htlo hthi => (hall t htlo hthi).2.2

theorem psi_highZeroSum_source_le
    {N q : ℕ} [NeZero q] (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 3 ≤ q)
    (hqUpper : (q : ℝ) ≤ sourceP1 N) {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖psi chi t + highZeroSum chi t (sourceT N)‖ ≤
      1.380391 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
  psi_highZeroSum_source_all_real_endpoints hN hq hqUpper hchi hPrimitive t htlo hthi

end LiuWang.Proof.PerronBudget
