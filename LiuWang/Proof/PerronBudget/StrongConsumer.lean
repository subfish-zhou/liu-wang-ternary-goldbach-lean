import LiuWang.Proof.PerronBudget.Consumer

/-! 保留实际全部误差的1.374强界，并接到原本原非主psi。 -/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace LiuWang.Proof.PerronBudget

open Interfaces Parameters ExplicitPerron FixedHeightZeroSum NonSymmetricContour

theorem sourceDomain_right_perron_strong {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hN : Real.exp 2000 ≤ (N : ℝ))
    {t Hminus Hplus : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ))
    (hminus : |Hminus + sourceT N| ≤ 1) (hplus : |Hplus - sourceT N| ≤ 1) :
    ‖vertical (centeredIntegrand chi t (5 / 2)) (1 + 1 / sourceL N) Hminus Hplus -
        ExplicitPerron.psi chi t‖ ≤ 1.374 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
  (ExplicitPerron.sourceDomain_right_perron chi hN htlo hminus hplus).trans
    (closedRealEndpointError_le_stronger hN htlo hthi hminus hplus)

theorem psi_highZeroSum_source_le_strong {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 3 ≤ q)
    (hqUpper : (q : ℝ) ≤ sourceP1 N) {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖ExplicitPerron.psi chi t + highZeroSum chi t (sourceT N)‖ ≤
      1.374171 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  obtain ⟨Hp, Hm, hh⟩ := exists_admissibleHeights hN hq hchi hPrimitive
  have hP := sourceDomain_right_perron_strong chi hN htlo hthi hh.2.1 hh.1
  rw [centered_vertical_eq_actual_right] at hP
  have hZ := actual_source_high_zero_estimate hN hq hqUpper hchi hPrimitive hh htlo hthi
  let R := actualRightVerticalIntegral chi t 2.5 (1 + 1 / sourceL N) Hm Hp
  calc
    _ = ‖(R + highZeroSum chi t (sourceT N)) - (R - ExplicitPerron.psi chi t)‖ := by
      congr 1
      abel
    _ ≤ ‖R + highZeroSum chi t (sourceT N)‖ + ‖R - ExplicitPerron.psi chi t‖ :=
      norm_sub_le _ _
    _ ≤ 0.000171 * t / sourceT N * sourceL N ^ (2 : ℕ) +
        1.374 * t / sourceT N * sourceL N ^ (2 : ℕ) := add_le_add hZ hP
    _ = _ := by ring

theorem primitive_nonprincipal_psi_sum_strong {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 3 ≤ q)
    (hqUpper : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ))
    {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : ℝ} (htlo : (N : ℝ) / 1000 ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) +
        ∑ p ∈ highZeroIndices chi ((Real.log (N : ℝ)) ^ (15 : ℕ)),
          (t : ℂ) ^ completedZeroValue p / completedZeroValue p‖ ≤
      1.374171 * t / (Real.log (N : ℝ)) ^ (15 : ℕ) *
        (Real.log (N : ℝ)) ^ (2 : ℕ) := by
  simpa only [psi_eq_sum, highZeroSum, sourceL, sourceT] using
    psi_highZeroSum_source_le_strong hN hq hqUpper hchi hPrimitive htlo hthi

end LiuWang.Proof.PerronBudget
