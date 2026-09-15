import LiuWang.Proof.Campaign20260915.Density.WindowWeight
import LiuWang.Proof.Campaign20260915.Density.FamilyRightConsumer
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets.Endpoints

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory Set Filter
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis (cosineDetector cosineMean)
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer

namespace LiuWang.Proof.Campaign20260915.Density

theorem source_family_weighted_window (q : ℕ) [NeZero q] {X y sigma : ℝ} {B : ℝ → ℝ}
    (hy : 10000 * Real.log 6 ≤ y)
    (hsig : sigma ∈ Icc (1 / 2) (1 + sourceDelta y))
    (hB0 : ∀ u, 0 ≤ u → 0 ≤ B u)
    (hKB : IntegrableOn (fun u => sourceKernel u * B u) (Ioi 0))
    (hwindow : ∀ u, 0 ≤ u →
      SourceRoute.Density.Restart.familyMean q X sigma (y * u) ≤ B u) :
    (∀ chi ∈ nonprincipalCharacters q, Integrable (fun t : ℝ =>
      ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2)) ∧
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2) ≤
      (4 + (10 : ℝ) ^ (-7 : ℤ)) * ∫ u in Ioi (0 : ℝ), sourceKernel u * B u := by
  let C : ℝ := 4 + (10 : ℝ) ^ (-7 : ℤ)
  let V : ℝ → ℝ := fun t =>
    SourceRoute.Density.Restart.familySquare q X ((sigma : ℂ) + t * I)
  let W : ℝ → ℝ := fun t => ∑ chi ∈ nonprincipalCharacters q,
    ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2
  have hy0 : 0 < y := by linarith [(source_height_log_bounds hy).1]
  have hcos (t : ℝ) :
      2 + Real.exp (|t| / y) ≤ C *
        ‖Complex.cos (((sigma : ℂ) + t * I) / (2 * (y : ℂ)))‖ ^ 2 :=
    source_cosine_lower hy hsig
  have hden (t : ℝ) :
      Complex.cos (((sigma : ℂ) + t * I) / (2 * (y : ℂ))) ≠ 0 := by
    intro hz
    have h := hcos t
    rw [hz, norm_zero, zero_pow (by decide), mul_zero] at h
    nlinarith [Real.exp_pos (|t| / y)]
  have hcont (chi : Character q) (hc : chi ∈ nonprincipalCharacters q) :
      Continuous (fun t : ℝ => ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2) := by
    have hc' := (NonprincipalDensityAdvance.mem_nonprincipalCharacters chi).mp hc
    have hf : Continuous (fun t : ℝ =>
        NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * I)) :=
      (NonprincipalDensityAdvance.differentiable_f hc' X).continuous.comp (by fun_prop)
    exact (hf.div (by fun_prop) hden).norm.pow 2
  have hV : Continuous V :=
    (SourceRoute.Density.Restart.familySquare_continuous q X).comp (by fun_prop)
  have hW : Continuous W := continuous_finsetSum _ hcont
  have hV0 (t : ℝ) : 0 ≤ V t := SourceRoute.Density.Restart.familySquare_nonneg q X _
  have hW0 (t : ℝ) : 0 ≤ W t := sum_nonneg (fun _ _ => sq_nonneg _)
  have henv (t : ℝ) : W t ≤ C * (V t / (2 + Real.exp (|t| / y))) := by
    have hpoint (chi : Character q) :
        ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2 ≤
          C * (‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * I)‖ ^ 2 /
            (2 + Real.exp (|t| / y))) := by
      have hc : 0 < ‖Complex.cos (((sigma : ℂ) + t * I) / (2 * (y : ℂ)))‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr (hden t)) 2
      have hi : 1 / ‖Complex.cos (((sigma : ℂ) + t * I) / (2 * (y : ℂ)))‖ ^ 2 ≤
          C / (2 + Real.exp (|t| / y)) := by
        apply (div_le_div_iff₀ hc (by positivity)).mpr
        simpa only [one_mul] using hcos t
      have h := mul_le_mul_of_nonneg_left hi
        (sq_nonneg ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * I)‖)
      unfold cosineDetector
      rw [norm_div, div_pow]
      simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using h
    have h := sum_le_sum (fun chi (_ : chi ∈ nonprincipalCharacters q) => hpoint chi)
    dsimp only [W, V, SourceRoute.Density.Restart.familySquare]
    simpa only [← mul_sum, ← sum_div] using h
  have hpaid := weighted_window_integral hy0 (show 0 ≤ C by dsimp [C]; positivity)
    hV hW hV0 hW0 hB0 hKB hwindow henv
  have hi (chi : Character q) (hc : chi ∈ nonprincipalCharacters q) :
      Integrable (fun t : ℝ => ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2) := by
    apply hpaid.1.mono' (hcont chi hc).aestronglyMeasurable
    exact Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      dsimp only [W]
      exact single_le_sum (fun chi _ =>
        sq_nonneg ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖) hc)
  refine ⟨hi, ?_⟩
  have h := hpaid.2
  rw [show (∫ t : ℝ, W t) =
      ∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
        ‖cosineDetector chi X y ((sigma : ℂ) + t * I)‖ ^ 2 from
      integral_finsetSum _ (fun chi hc => hi chi hc)] at h
  exact h

theorem source_family_weighted_right_data (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (∀ chi ∈ nonprincipalCharacters q, Integrable (fun t : ℝ =>
      ‖cosineDetector chi ((q : ℝ) * y) y
        (((1 + sourceDelta ((q : ℝ) * y) : ℝ) : ℂ) + t * I)‖ ^ 2)) ∧
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖cosineDetector chi ((q : ℝ) * y) y
        (((1 + sourceDelta ((q : ℝ) * y) : ℝ) : ℂ) + t * I)‖ ^ 2) ≤
      90.5727 * Real.log ((q : ℝ) * y) ^ 5 := by
  let X : ℝ := (q : ℝ) * y
  have hylog := source_height_ge_log_six hy
  obtain ⟨hy', hLy⟩ := source_height_log_bounds hylog
  have hy0 : 0 < y := by linarith
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hyX : y ≤ X := by dsimp [X]; nlinarith
  have hLX : 0 < Real.log X :=
    (show 0 < Real.log y by linarith).trans_le (Real.log_le_log hy0 hyX)
  have hd : 0 < sourceDelta X := by unfold sourceDelta; positivity
  have hdle : sourceDelta X ≤ sourceDelta y := by
    unfold sourceDelta
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hy0 hyX) (by norm_num)
  have hKB : IntegrableOn
      (fun u : ℝ => sourceKernel u * ((67.929 + 0.0003 * u) * Real.log X ^ 5)) (Ioi 0) := by
    simpa only [mul_assoc] using MeanBudgets.equation_3_45_integrable X
  have hpaid := source_family_weighted_window q hylog
    (X := X) (sigma := 1 + sourceDelta X) ⟨by linarith, by linarith⟩
    (B := fun u => (67.929 + 0.0003 * u) * Real.log X ^ 5)
    (fun u hu => by positivity) hKB (fun u hu => source_familyMean_right_paid q hy hu)
  have hbudget := MeanBudgets.equation_3_45_kernel (hylog.trans hyX)
  simp only [mul_assoc] at hbudget
  exact ⟨hpaid.1, hpaid.2.trans hbudget⟩

theorem source_family_equation_31 (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖cosineDetector chi ((q : ℝ) * y) y
        (((1 + sourceDelta ((q : ℝ) * y) : ℝ) : ℂ) + t * I)‖ ^ 2) ≤
      90.5727 * Real.log ((q : ℝ) * y) ^ 5 :=
  (source_family_weighted_right_data q hy).2

theorem source_cosineMean_right_paid (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    cosineMean q ((q : ℝ) * y) (1 + sourceDelta ((q : ℝ) * y)) y ≤
      90.5727 * Real.log ((q : ℝ) * y) ^ 5 / q.totient :=
  div_le_div_of_nonneg_right (source_family_equation_31 q hy) (Nat.cast_nonneg _)

#print axioms source_family_equation_31
#print axioms source_cosineMean_right_paid

end LiuWang.Proof.Campaign20260915.Density
