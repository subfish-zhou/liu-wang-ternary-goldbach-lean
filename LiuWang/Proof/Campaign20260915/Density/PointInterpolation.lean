import LiuWang.Proof.Campaign20260915.Density.RightPointSource
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section

open Finset Complex Set
open Complex.HadamardThreeLines
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.Campaign20260915.Density

theorem sqrt_rpow_square {A : ℝ} (hA : 0 ≤ A) (w : ℝ) :
    (Real.sqrt A ^ w) ^ 2 = A ^ w := by
  rw [← Real.rpow_mul_natCast (Real.sqrt_nonneg A), mul_comm w ((2 : ℕ) : ℝ),
    Real.rpow_natCast_mul (Real.sqrt_nonneg A), Real.sq_sqrt hA]

theorem source_family_point_interpolation (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {y : ℝ} {s : ℂ} (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : s.re ∈ Set.Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    let theta := (s.re - 1 / 2) / (1 / 2 + sourceDelta ((q : ℝ) * y))
    (∑ chi ∈ nonprincipalCharacters q,
      ‖cosineDetector chi ((q : ℝ) * y) y s‖ ^ 2) ≤
      (37.1 * Real.sqrt q * ((q : ℝ) * y) * y * Real.log q) ^ (1 - theta) *
        (2 * Real.log ((q : ℝ) * y) ^ 4) ^ theta := by
  let ι := ↥(nonprincipalCharacters q)
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm
  let G (z : ℂ) : EuclideanSpace ℂ ι :=
    e (fun chi => cosineDetector chi.val ((q : ℝ) * y) y z)
  let A : ℝ := 37.1 * Real.sqrt q * ((q : ℝ) * y) * y * Real.log q
  let B : ℝ := 2 * Real.log ((q : ℝ) * y) ^ 4
  let b : ℝ := 1 + sourceDelta ((q : ℝ) * y)
  have hy' : 10000 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hy2 : 2 ≤ y := by linarith
  have hd := source_product_shift_bounds q hy
  have hb : b ≤ 2 := by dsimp [b]; linarith [hd.2]
  have hab : (1 / 2 : ℝ) < b := by dsimp [b]; linarith [hd.1]
  have hl : 0 ≤ Real.log q :=
    Real.log_nonneg (Nat.one_le_cast.mpr (by omega : 1 ≤ q))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnorm (z : ℂ) : ‖G z‖ ^ 2 =
      ∑ chi ∈ nonprincipalCharacters q,
        ‖cosineDetector chi ((q : ℝ) * y) y z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ chi : ι, ‖cosineDetector chi.val ((q : ℝ) * y) y z‖ ^ 2) = _
    exact Finset.sum_attach (nonprincipalCharacters q)
      (fun chi => ‖cosineDetector chi ((q : ℝ) * y) y z‖ ^ 2)
  have hdiff (z : ℂ) (hz : z ∈ verticalClosedStrip (1 / 2) b) :
      DifferentiableAt ℂ G z := by
    have hsa : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith [hz.1], hz.2.trans hb⟩
    exact e.differentiableAt.comp z (differentiableAt_pi.mpr (fun chi =>
      cosine_diffAt_extended
        ((NonprincipalDensityAdvance.mem_nonprincipalCharacters chi.val).mp chi.property)
        ((q : ℝ) * y) hy2 hsa))
  have hdc : DiffContOnCl ℂ G (verticalStrip (1 / 2) b) := by
    apply DifferentiableOn.diffContOnCl
    rw [verticalStrip, Complex.closure_preimage_re, closure_Ioo hab.ne]
    exact fun z hz => (hdiff z hz).differentiableWithinAt
  choose C hC using fun (chi : ι) => cosine_bounded_extended
    ((NonprincipalDensityAdvance.mem_nonprincipalCharacters chi.val).mp chi.property)
    ((q : ℝ) * y) hy2 hb
  have hbounded : BddAbove ((norm ∘ G) '' verticalClosedStrip (1 / 2) b) := by
    refine ⟨Real.sqrt (∑ chi : ι, max (C chi) 0 ^ 2), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    apply (Real.le_sqrt (norm_nonneg _) (sum_nonneg (fun _ _ => sq_nonneg _))).mpr
    rw [EuclideanSpace.norm_sq_eq]
    apply sum_le_sum
    intro chi _
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (hC chi (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hleft : ∀ z ∈ Complex.re ⁻¹' {(1 / 2 : ℝ)}, ‖G z‖ ≤ Real.sqrt A := by
    intro z hz
    apply (Real.le_sqrt (norm_nonneg _) hA).mpr
    rw [hnorm]
    have he : (1 / 2 : ℂ) + z.im * I = z := by
      apply Complex.ext <;> simp [show z.re = 1 / 2 from hz]
    simpa only [he] using source_family_point_critical q hq hy z.im
  have hright : ∀ z ∈ Complex.re ⁻¹' {b}, ‖G z‖ ≤ Real.sqrt B := by
    intro z hz
    apply (Real.le_sqrt (norm_nonneg _) hB).mpr
    rw [hnorm]
    exact source_family_point_right q hy hz
  have h := norm_le_interp_of_mem_verticalClosedStrip' hab hs hdc hbounded hleft hright
  have hsq := pow_le_pow_left₀ (norm_nonneg (G s)) h 2
  rw [hnorm, mul_pow, sqrt_rpow_square hA, sqrt_rpow_square hB] at hsq
  have he : b - 1 / 2 = 1 / 2 + sourceDelta ((q : ℝ) * y) := by dsimp [b]; ring
  rw [he] at hsq
  exact hsq

end LiuWang.Proof.Campaign20260915.Density
