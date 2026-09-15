import LiuWang.Proof.NonSymmetricContour.Heights
import LiuWang.Proof.NonSymmetricContour.Residues
import LiuWang.Proof.NonSymmetricContour.Budget

/-! # 同一非对称矩形上全实端点的实际恒等式及已付预算 -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.NonSymmetricContour

def centeredZeroSum {q : Nat} [NeZero q] (chi : Character q)
    (t Hplus Hminus : Real) : Complex :=
  ∑ p ∈ rectangleZeroIndices chi Hplus Hminus,
    ((t : Complex) ^ completedZeroValue p - (2.5 : Complex) ^ completedZeroValue p) /
      completedZeroValue p

theorem actual_source_rectangle_estimate {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {Hplus Hminus : Real} (h : AdmissibleHeights N chi Hplus Hminus)
    {t : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    let F := horizontalIntegrand chi t
    let b := 1 + 1 / sourceL N
    let Z := centeredZeroSum chi t Hplus Hminus
    let O := (lFunctionOriginMultiplicity chi : Complex) * (Real.log (t / 2.5) : Complex)
    RectangleBorderIntegrable F (lowerLeft Hminus) (upperRight b Hplus) ∧
    verticalIntegral F b Hplus Hminus + Z + O = threeSides F b Hplus Hminus ∧
    ‖verticalIntegral F b Hplus Hminus + Z + O‖ ≤
      0.0014 * t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2 +
        (1 / 100000 : Real) * t / sourceT N * sourceL N ^ (2 : Nat) ∧
    ‖verticalIntegral F b Hplus Hminus + Z‖ ≤
      0.00002 * t / sourceT N * sourceL N ^ (2 : Nat) := by
  intro F b Z O
  have ht0 : 0 < t := (sourceT_pos hN).trans (sourceT_lt_real_endpoint hN htlo)
  have hb : 1 ≤ b := by
    dsimp [b]
    have hL := sourceL_pos hN
    have hi : 0 ≤ 1 / sourceL N := by positivity
    linarith
  obtain ⟨hp0, hm0⟩ := admissibleHeights_signs hN h
  have hborder := admissibleHeights_border hN hq hchi hPrimitive h
  have hzero := zero_not_mem_border hb hp0 hm0
  have hcontG : ContinuousOn (analyticIntegrand chi t)
      (RectangleBorder (lowerLeft Hminus) (upperRight b Hplus)) := by
    intro s hs
    exact (analyticAt_analyticIntegrand hchi ht0 (hborder s hs)).continuousAt.continuousWithinAt
  have hcontF : ContinuousOn F
      (RectangleBorder (lowerLeft Hminus) (upperRight b Hplus)) := by
    apply hcontG.congr
    intro s hs
    exact (analyticIntegrand_eq chi t (fun hz => hzero (hz ▸ hs))).symm
  have hid : verticalIntegral F b Hplus Hminus + Z + O = threeSides F b Hplus Hminus :=
    right_integral_add_zeros_add_origin_eq_threeSides hchi hPrimitive ht0 hb hp0 hm0 hborder
  obtain ⟨_, hhorizontal⟩ :=
    admissibleHeights_horizontal_budget hN hq hchi hPrimitive h htlo hthi
  have hleft := LeftVertical.actual_left_vertical_estimate hN hq hqUpper hchi hPrimitive
    h.1 h.2.1 htlo hthi
  have hv : ‖verticalIntegral F (-1 / 2) Hplus Hminus‖ ≤
      (1 / 100000 : Real) * t / sourceT N * sourceL N ^ (2 : Nat) := by
    rw [norm_verticalIntegral]
    simpa [F] using hleft.2.2.2.2
  have hsides : ‖threeSides F b Hplus Hminus‖ ≤
      0.0014 * t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2 +
        (1 / 100000 : Real) * t / sourceT N * sourceL N ^ (2 : Nat) := by
    have hn := norm_sub_le
      (verticalIntegral F (-1 / 2) Hplus Hminus + horizontalIntegral F b Hplus)
      (horizontalIntegral F b Hminus)
    have ha := norm_add_le (verticalIntegral F (-1 / 2) Hplus Hminus)
      (horizontalIntegral F b Hplus)
    change ‖verticalIntegral F (-1 / 2) Hplus Hminus + horizontalIntegral F b Hplus -
      horizontalIntegral F b Hminus‖ ≤ _
    change ‖horizontalIntegral F b Hplus‖ + ‖horizontalIntegral F b Hminus‖ ≤ _ at hhorizontal
    linarith
  have hnorm : ‖verticalIntegral F b Hplus Hminus + Z + O‖ ≤
      0.0014 * t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2 +
        (1 / 100000 : Real) * t / sourceT N * sourceL N ^ (2 : Nat) := hid ▸ hsides
  refine ⟨hcontF.rectangleBorder_integrable, hid, hnorm, ?_⟩
  calc
    _ = ‖(verticalIntegral F b Hplus Hminus + Z + O) - O‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖verticalIntegral F b Hplus Hminus + Z + O‖ + ‖O‖ := norm_sub_le _ _
    _ ≤ (0.0014 * t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2 +
        (1 / 100000 : Real) * t / sourceT N * sourceL N ^ (2 : Nat)) + ‖O‖ :=
      add_le_add hnorm le_rfl
    _ ≤ _ := threeSides_and_origin_cost_le_budget hN hq hqUpper hchi hPrimitive htlo hthi

end LiuWang.Proof.NonSymmetricContour
