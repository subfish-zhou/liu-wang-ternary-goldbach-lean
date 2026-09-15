import LiuWang.Proof.Campaign20260915.Density.ExtendedCosine
import LiuWang.Proof.Campaign20260915.Density.L2ThreeLines
import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.FamilyHolder

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory Set
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open Complex.HadamardThreeLines

namespace LiuWang.Proof.Campaign20260915.Density

theorem source_product_shift_bounds (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    0 < sourceDelta ((q : ℝ) * y) ∧ sourceDelta ((q : ℝ) * y) ≤ 1 / 12 := by
  have hy' : 10000 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hX : 10000 ≤ (q : ℝ) * y := by nlinarith
  have hlog : 0 < Real.log ((q : ℝ) * y) := Real.log_pos (by linarith)
  exact ⟨by unfold sourceDelta; positivity, sourceDelta_le_twelfth hX⟩

theorem source_character_interpolation {q : ℕ} [NeZero q] {chi : Character q}
    (hc : chi ≠ 1) {y sigma : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    (∫ t : ℝ, ‖cosineDetector chi ((q : ℝ) * y) y ((sigma : ℂ) + t * I)‖ ^ 2) ≤
      (∫ t : ℝ, ‖cosineDetector chi ((q : ℝ) * y) y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ^
        (1 - (sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y))) *
      (∫ t : ℝ, ‖cosineDetector chi ((q : ℝ) * y) y
        (((1 + sourceDelta ((q : ℝ) * y) : ℝ) : ℂ) + t * I)‖ ^ 2) ^
        ((sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y))) := by
  have hy' : 2 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hd := source_product_shift_bounds q hy
  have hinside : verticalClosedStrip (1 / 2) (1 + sourceDelta ((q : ℝ) * y)) ⊆
      verticalStrip 0 2 := by
    intro z hz
    change 1 / 2 ≤ z.re ∧ z.re ≤ 1 + sourceDelta ((q : ℝ) * y) at hz
    change 0 < z.re ∧ z.re < 2
    constructor <;> linarith [hz.1, hz.2]
  have h := L2Strip.squareMean_interpolation (cosine_analytic_extended hc ((q : ℝ) * y) hy')
    (show (1 / 2 : ℝ) < 1 + sourceDelta ((q : ℝ) * y) by linarith) hinside
    (cosine_bounded_extended hc ((q : ℝ) * y) hy' (by linarith))
    (fun s hs' => cosine_integrable_extended hc ((q : ℝ) * y) hy' ⟨hs'.1, by linarith [hs'.2]⟩)
    hs
  simpa only [L2Strip.squareMean, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    show 1 + sourceDelta ((q : ℝ) * y) - 1 / 2 =
      1 / 2 + sourceDelta ((q : ℝ) * y) by ring] using h

theorem source_family_interpolation (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖cosineDetector chi ((q : ℝ) * y) y ((sigma : ℂ) + t * I)‖ ^ 2) ≤
      (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
        ‖cosineDetector chi ((q : ℝ) * y) y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ^
        (1 - (sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y))) *
      (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
        ‖cosineDetector chi ((q : ℝ) * y) y
          (((1 + sourceDelta ((q : ℝ) * y) : ℝ) : ℂ) + t * I)‖ ^ 2) ^
        ((sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y))) := by
  have hd := source_product_shift_bounds q hy
  have ht : (sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y)) ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hs.1) (by linarith)
    · apply (div_le_one (by linarith)).mpr
      linarith [hs.2]
  have hsum := sum_le_sum (s := nonprincipalCharacters q) (fun chi hc =>
    source_character_interpolation ((NonprincipalDensityAdvance.mem_nonprincipalCharacters chi).mp hc) hy hs)
  have hh := normalized_geometric_sum (nonprincipalCharacters q)
    (fun chi => ∫ t : ℝ, ‖cosineDetector chi ((q : ℝ) * y) y ((1 / 2 : ℂ) + t * I)‖ ^ 2)
    (fun chi => ∫ t : ℝ, ‖cosineDetector chi ((q : ℝ) * y) y
      (((1 + sourceDelta ((q : ℝ) * y) : ℝ) : ℂ) + t * I)‖ ^ 2)
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
    (D := 1) (by norm_num) ht
  simp only [div_one] at hh
  exact hsum.trans hh

theorem family_interpolation_log_four_budget (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖cosineDetector chi ((q : ℝ) * y) y ((sigma : ℂ) + t * I)‖ ^ 2) ≤
      (235.69 * ((q : ℝ) * y) ^ (3 / 2 : ℝ) * y ^ (1 / 2 : ℝ) *
        Real.log ((q : ℝ) * y) ^ 4) ^
        ((1 + sourceDelta ((q : ℝ) * y) - sigma) / (1 / 2 + sourceDelta ((q : ℝ) * y))) *
      (90.5727 * Real.log ((q : ℝ) * y) ^ 5) ^
        ((sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y))) := by
  have hd := source_product_shift_bounds q hy
  have hy0 : 0 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have ht0 : 0 ≤ (sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y)) :=
    div_nonneg (sub_nonneg.mpr hs.1) (by linarith)
  have ht1 : (sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y)) ≤ 1 := by
    apply (div_le_one (by linarith)).mpr
    linarith [hs.2]
  have hL := Real.rpow_le_rpow
    (sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))
    (source_family_critical_log_four q hy) (show 0 ≤ 1 - (sigma - 1 / 2) /
      (1 / 2 + sourceDelta ((q : ℝ) * y)) by linarith)
  have hR := Real.rpow_le_rpow
    (sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))
    (source_family_equation_31 q hy) ht0
  have h := (source_family_interpolation q hy hs).trans
    (mul_le_mul hL hR (Real.rpow_nonneg
      (sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))) _)
      (Real.rpow_nonneg (by positivity) _))
  have he : (1 + sourceDelta ((q : ℝ) * y) - sigma) / (1 / 2 + sourceDelta ((q : ℝ) * y)) =
      1 - (sigma - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y)) := by
    apply (div_eq_iff (show 1 / 2 + sourceDelta ((q : ℝ) * y) ≠ 0 by linarith)).mpr
    rw [sub_mul, div_mul_cancel₀ _ (show 1 / 2 + sourceDelta ((q : ℝ) * y) ≠ 0 by linarith)]
    ring
  rwa [he]

#print axioms source_character_interpolation
#print axioms source_family_interpolation
#print axioms family_interpolation_log_four_budget

end LiuWang.Proof.Campaign20260915.Density
