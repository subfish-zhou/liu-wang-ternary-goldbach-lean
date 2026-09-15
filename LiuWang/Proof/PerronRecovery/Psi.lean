import LiuWang.Proof.PerronRecovery.Budget
import LiuWang.Proof.NonprincipalPsi.InductionBudget
import LiuWang.Proof.NonprincipalPsi.ZeroTransport

/-! The recovered Perron bound feeds the actual fixed-height contour formula.
The contour cost 0.000171 and the imprimitive Euler correction are each paid
once; the ambient-character high-zero sum is transported by exact equality. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace LiuWang.Proof.PerronRecovery

open Interfaces Parameters ExplicitPerron FixedHeightZeroSum NonSymmetricContour

def primitiveError (N : ℕ) (t : ℝ) : ℝ :=
  sourceError N t + 0.000171 * t / sourceT N * sourceL N ^ (2 : ℕ)

def nonprincipalError (N q : ℕ) (t : ℝ) : ℝ :=
  primitiveError N t + Real.log q * Real.log t / Real.log 2

theorem primitive_psi_function {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 3 ≤ q)
    (hqUpper : (q : ℝ) ≤ sourceP1 N) {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖psi chi t + highZeroSum chi t (sourceT N)‖ ≤ primitiveError N t := by
  obtain ⟨Hp, Hm, hh⟩ := exists_admissibleHeights hN hq hchi hPrimitive
  have hP := source_right_perron_function chi hN htlo hh.2.1 hh.1
  rw [PerronBudget.centered_vertical_eq_actual_right] at hP
  have hZ := actual_source_high_zero_estimate hN hq hqUpper hchi hPrimitive hh htlo hthi
  let R := actualRightVerticalIntegral chi t 2.5 (1 + 1 / sourceL N) Hm Hp
  calc
    _ = ‖(R + highZeroSum chi t (sourceT N)) - (R - psi chi t)‖ := by
      congr 1
      abel
    _ ≤ ‖R + highZeroSum chi t (sourceT N)‖ + ‖R - psi chi t‖ := norm_sub_le _ _
    _ ≤ 0.000171 * t / sourceT N * sourceL N ^ (2 : ℕ) + sourceError N t :=
      add_le_add hZ hP
    _ = _ := by unfold primitiveError; ring

theorem primitiveError_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    primitiveError N t ≤ 0.961615 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  calc
    _ ≤ 0.961444 * t / sourceT N * sourceL N ^ (2 : ℕ) +
        0.000171 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
      add_le_add (sourceError_le hN htlo hthi) le_rfl
    _ = _ := by ring

theorem primitive_psi_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 3 ≤ q)
    (hqUpper : (q : ℝ) ≤ sourceP1 N) {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖psi chi t + highZeroSum chi t (sourceT N)‖ ≤
      0.961615 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
  (primitive_psi_function hN hq hqUpper hchi hPrimitive htlo hthi).trans
    (primitiveError_le hN htlo hthi)

theorem nonprincipal_psi_function {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (hchi : chi ≠ 1)
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖psi chi t + highZeroSum chi t (sourceT N)‖ ≤ nonprincipalError N q t := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  obtain ⟨hc, hcUpper, hcNe, hcPrimitive⟩ :=
    NonprincipalPsi.conductor_source_domain chi hchi hqUpper
  have hp := primitive_psi_function hN hc hcUpper hcNe hcPrimitive htlo hthi
  have hd := NonprincipalPsi.norm_psi_sub_primitive_le chi
    (by linarith [(PerronBudget.source_cutoff_bounds hN htlo hthi).1] : 1 ≤ t)
  rw [NonprincipalPsi.highZeroSum_eq_primitive chi hchi]
  calc
    _ = ‖(psi chi.primitiveCharacter t + highZeroSum chi.primitiveCharacter t (sourceT N)) +
        (psi chi t - psi chi.primitiveCharacter t)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ primitiveError N t + Real.log q * Real.log t / Real.log 2 := add_le_add hp hd

theorem nonprincipalError_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hqUpper : (q : ℝ) ≤ sourceP1 N)
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    nonprincipalError N q t ≤ 0.961616 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  calc
    _ ≤ 0.961615 * t / sourceT N * sourceL N ^ (2 : ℕ) +
        0.000001 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
      add_le_add (primitiveError_le hN htlo hthi)
        (NonprincipalPsi.induction_cost_source_le hN hqUpper htlo hthi)
    _ = _ := by ring

theorem nonprincipal_psi_le {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (hchi : chi ≠ 1)
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖psi chi t + highZeroSum chi t (sourceT N)‖ ≤
      0.961616 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
  (nonprincipal_psi_function chi hN hqUpper hchi htlo hthi).trans
    (nonprincipalError_le hN hqUpper htlo hthi)

end LiuWang.Proof.PerronRecovery
