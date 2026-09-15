import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelPoleAnnulus

set_option autoImplicit false
noncomputable section
open Complex Set

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rsHankelLift_pole_iff (s : ℂ) (m : ℕ) {w : ℂ}
    (hlo : -(Real.pi / 2) < w.im) (hhi : w.im < 3 * Real.pi / 2) :
    meromorphicOrderAt (rsHankelLift s m) w < 0 ↔
      ∃ n : ℤ, n ≠ 0 ∧ w = rsHankelLog n := by
  constructor
  · intro hp
    by_contra hn
    have ha := rsHankelLift_analytic_off s m (mt (rsLiftDenominator_zero_iff hlo hhi).mp hn)
    exact not_lt_of_ge ha.meromorphicOrderAt_nonneg hp
  · rintro ⟨n, hn, rfl⟩
    rw [rsHankelLift_order_pole s m n hn]
    exact_mod_cast (by norm_num : (-1 : ℤ) < 0)

theorem rsHankelLift_annulus_residues (s : ℂ) (m : ℕ) {M : ℕ} {u R : ℝ}
    (hu : u < 0) (hR : (M : ℝ) < R) (hR' : R < M + 1) (hM : 0 < M) :
    RectangleIntegral' (rsHankelLift s m) (u - Real.pi / 4 * I)
      ((Real.log R : ℂ) + 5 * Real.pi / 4 * I) =
        ∑ n ∈ rsLiftPoleIndices M, residue (rsHankelKernel s m) n := by
  classical
  let a : ℂ := u - Real.pi / 4 * I
  let b : ℂ := (Real.log R : ℂ) + 5 * Real.pi / 4 * I
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlR : 0 < Real.log R := Real.log_pos (by linarith)
  have habR : a.re ≤ b.re := by simp [a, b]; linarith
  have habI : a.im ≤ b.im := by simp [a, b]; linarith [Real.pi_pos]
  have hmem (w : ℂ) : w ∈ Rectangle a b ↔
      u ≤ w.re ∧ w.re ≤ Real.log R ∧ -(Real.pi / 4) ≤ w.im ∧ w.im ≤ 5 * Real.pi / 4 := by
    simpa [a, b] using mem_Rect habR habI w
  have hangle {w : ℂ} (hw : w ∈ Rectangle a b) :
      -(Real.pi / 2) < w.im ∧ w.im < 3 * Real.pi / 2 := by
    have h := (hmem w).mp hw
    constructor <;> linarith [h.2.2.1, h.2.2.2, Real.pi_pos]
  have hset : Rectangle a b ∩ {w | meromorphicOrderAt (rsHankelLift s m) w < 0} =
      (rsLiftPoleSet M : Set ℂ) := by
    ext w
    constructor
    · rintro ⟨hw, hp⟩
      obtain ⟨n, hn, rfl⟩ := (rsHankelLift_pole_iff s m (hangle hw).1 (hangle hw).2).mp hp
      exact Finset.mem_image.mpr ⟨n, (rsLiftPole_mem_rectangle hu hR hR' hM n).mpr ⟨hn, hw⟩, rfl⟩
    · intro hw
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
      have h := (rsLiftPole_mem_rectangle hu hR hR' hM n).mp hn
      refine ⟨h.2, ?_⟩
      change meromorphicOrderAt (rsHankelLift s m) (rsHankelLog (n : ℂ)) < 0
      rw [rsHankelLift_order_pole s m n h.1]
      exact_mod_cast (by norm_num : (-1 : ℤ) < 0)
  have hborder : Disjoint (RectangleBorder a b)
      {w | meromorphicOrderAt (rsHankelLift s m) w < 0} := by
    rw [Set.disjoint_left]
    intro w hw hp
    have hrect := rectangleBorder_subset_rectangle a b hw
    have hpol : w ∈ rsLiftPoleSet M := by
      change w ∈ (rsLiftPoleSet M : Set ℂ)
      rw [← hset]
      exact ⟨hrect, hp⟩
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hpol
    obtain ⟨h1, h2, h3, h4⟩ := rsLiftPole_strict_interior hu hR hn
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
      a, b, sub_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im,
      mul_zero, sub_zero, add_zero, sub_im, add_im, mul_im, mul_one, zero_sub,
      div_ofNat, re_ofNat, im_ofNat] at hw
    rcases hw with ((hw | hw) | hw) | hw
    · linarith [hw.2]
    · linarith [hw.1]
    · linarith [hw.2]
    · linarith [hw.1]
  have hsimple : ∀ w ∈ Rectangle a b, (-1 : ℤ) ≤ meromorphicOrderAt (rsHankelLift s m) w := by
    intro w hw
    by_cases hp : meromorphicOrderAt (rsHankelLift s m) w < 0
    · obtain ⟨n, hn, rfl⟩ := (rsHankelLift_pole_iff s m (hangle hw).1 (hangle hw).2).mp hp
      rw [rsHankelLift_order_pole s m n hn]
    · exact le_trans (by exact_mod_cast (by norm_num : (-1 : ℤ) ≤ 0)) (le_of_not_gt hp)
  rw [RectangleIntegral'_eq_sumResiduesIn habR habI
    (fun w _ => rsHankelLift_meromorphic s m w) hborder
    (by rw [hset]; exact (rsLiftPoleSet M).finite_toSet) hsimple,
    hset, BombieriVinogradov.ComplexAnalysis.sumResiduesIn_finset, rsLiftPoleSet,
    Finset.sum_image (fun n _ k _ h => rsHankelLog_int_injective h)]
  apply Finset.sum_congr rfl
  intro n hn
  exact rsHankelLift_residue s m n (Finset.mem_erase.mp hn).1

end LiuWang.Proof.Campaign20260915.ZetaValidation
