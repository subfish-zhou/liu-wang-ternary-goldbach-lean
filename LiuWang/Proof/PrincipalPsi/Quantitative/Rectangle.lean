import LiuWang.Proof.PrincipalPsi.Quantitative.IndexTransport
import LiuWang.Proof.PrincipalPsi.Quantitative.LeftBound
import LiuWang.Proof.PrincipalPsi.Consumer
import LiuWang.Proof.NonSymmetricContour.Residues

/-! # 实际 ζ 非对称矩形：极点主项与全部真实零点留数 -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.NonSymmetricContour

namespace LiuWang.Proof.PrincipalPsi.Quantitative

def xiRectangleIndices (Hp Hm : ℝ) : Finset RiemannXiDivisorZeroIndex := by
  classical
  exact (xiWindow 0 (|Hp| + |Hm| + 1)).filter
    (fun p => Hm < (riemannXiDivisorZeroValue p).im ∧ (riemannXiDivisorZeroValue p).im < Hp)

@[simp] theorem mem_xiRectangleIndices {Hp Hm : ℝ} {p : RiemannXiDivisorZeroIndex} :
    p ∈ xiRectangleIndices Hp Hm ↔
      Hm < (riemannXiDivisorZeroValue p).im ∧ (riemannXiDivisorZeroValue p).im < Hp := by
  classical
  rw [xiRectangleIndices, Finset.mem_filter, mem_xiWindow]
  refine and_iff_right_of_imp ?_
  rintro ⟨hm, hp⟩
  simp only [sub_zero]
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self Hp, neg_le_abs Hm, abs_nonneg Hp, abs_nonneg Hm]

def xiRectangleValues (Hp Hm : ℝ) : Finset ℂ := by
  classical
  exact (xiRectangleIndices Hp Hm).image riemannXiDivisorZeroValue

theorem xiRectangle_fiber_card {Hp Hm : ℝ} {rho : ℂ}
    (hrho : rho ∈ xiRectangleValues Hp Hm) :
    ((xiRectangleIndices Hp Hm).filter (fun p => riemannXiDivisorZeroValue p = rho)).card =
      analyticOrderNatAt riemannZeta rho := by
  classical
  obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hrho
  have hr := riemannXiDivisorZeroValue_re_mem_Ioo p
  have hr0 : rho ≠ 0 := hpv ▸ riemannXiDivisorZeroValue_ne_zero p
  have hre : 0 < rho.re := hpv ▸ hr.1
  have hr1 : rho ≠ 1 := by
    intro h
    have hh : rho.re < 1 := hpv ▸ hr.2
    norm_num [h] at hh
  have hf : (xiRectangleIndices Hp Hm).filter (fun p => riemannXiDivisorZeroValue p = rho) =
      Hadamard.divisorZeroIndex₀_fiberFinset riemannXi rho := by
    ext a
    rw [Finset.mem_filter, mem_xiRectangleIndices, Hadamard.mem_divisorZeroIndex₀_fiberFinset]
    change (_ ∧ riemannXiDivisorZeroValue a = rho) ↔ riemannXiDivisorZeroValue a = rho
    refine and_iff_right_of_imp ?_
    intro ha
    simpa only [ha, hpv] using mem_xiRectangleIndices.mp hp
  rw [hf, Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    differentiable_riemannXi hr0, analyticOrderNatAt_xi_eq_principal (q := 1) hre hr1,
    DirichletCharacter.LFunction_modOne_eq]

theorem sum_xiRectangle_values (Hp Hm : ℝ) (f : ℂ → ℂ) :
    ∑ rho ∈ xiRectangleValues Hp Hm, (analyticOrderNatAt riemannZeta rho : ℂ) * f rho =
      ∑ p ∈ xiRectangleIndices Hp Hm, f (riemannXiDivisorZeroValue p) := by
  classical
  calc
    _ = ∑ rho ∈ xiRectangleValues Hp Hm,
        ∑ p ∈ (xiRectangleIndices Hp Hm).filter (fun p => riemannXiDivisorZeroValue p = rho),
          f (riemannXiDivisorZeroValue p) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      simp only [Finset.sum_congr rfl (fun p hp =>
        congrArg f (Finset.mem_filter.mp hp).2), Finset.sum_const, nsmul_eq_mul,
        xiRectangle_fiber_card hrho]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) _

def xiRectangleCenteredSum (t Hp Hm : ℝ) : ℂ :=
  ∑ p ∈ xiRectangleIndices Hp Hm, centeredKernel t (riemannXiDivisorZeroValue p)

theorem zeta_rectangle_residue {t b Hp Hm : ℝ}
    (ht : 0 < t) (hb : 1 < b) (hp : 0 < Hp) (hm : Hm < 0)
    (hborder : ∀ s ∈ RectangleBorder (lowerLeft Hm) (upperRight b Hp),
      s ≠ 1 ∧ riemannZeta s ≠ 0) :
    RectangleIntegral' (zetaCenteredIntegrand t) (lowerLeft Hm) (upperRight b Hp) =
      (t : ℂ) - 2.5 - xiRectangleCenteredSum t Hp Hm := by
  classical
  let G := zetaCenteredIntegrand t
  let R := Complex.Rectangle (lowerLeft Hm) (upperRight b Hp)
  let V := insert (1 : ℂ) (xiRectangleValues Hp Hm)
  let P := {s : ℂ | meromorphicOrderAt G s < 0}
  have hH : Hm ≤ Hp := by linarith
  have hmero := meromorphic_zetaCenteredIntegrand ht
  have hdisj : Disjoint (RectangleBorder (lowerLeft Hm) (upperRight b Hp)) P := by
    rw [Set.disjoint_left]
    intro s hs hsp
    exact not_lt_of_ge
      (analytic_zetaCenteredIntegrand ht (hborder s hs).1 (hborder s hs).2).meromorphicOrderAt_nonneg hsp
  have hVinR : (V : Set ℂ) ⊆ R := by
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact (mem_rectangle hb.le hH 1).mpr ⟨⟨by norm_num, by simpa using hb.le⟩,
        by simpa using hm.le, by simpa using hp.le⟩
    · obtain ⟨p, hpi, rfl⟩ := Finset.mem_image.mp hs
      have hr := riemannXiDivisorZeroValue_re_mem_Ioo p
      have hi := mem_xiRectangleIndices.mp hpi
      exact (mem_rectangle hb.le hH _).mpr ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩,
        hi.1.le, hi.2.le⟩
  have hset : R ∩ P = (V : Set ℂ) ∩ P := by
    ext s
    constructor
    · rintro ⟨hsR, hsP⟩
      refine ⟨?_, hsP⟩
      rcases zetaCenteredIntegrand_poles_subset ht hsP with hs1 | hz
      · exact Finset.mem_insert.mpr (Or.inl hs1)
      have hs := (mem_rectangle hb.le hH s).mp hsR
      have hr := zeta_zero_strip (by linarith [hs.1.1]) hz
      obtain ⟨p, hpv⟩ := exists_xi_index_of_zeta_zero hr.1 hz
      have hbottom : Hm < s.im := by
        apply lt_of_le_of_ne hs.2.1
        intro heq
        exact (hborder s ((mem_border hb.le hH s).mpr
          (Or.inl (Or.inl ⟨hs.1, heq.symm⟩)))).2 hz
      have htop : s.im < Hp := by
        apply lt_of_le_of_ne hs.2.2
        intro heq
        exact (hborder s ((mem_border hb.le hH s).mpr
          (Or.inr (Or.inl ⟨hs.1, heq⟩)))).2 hz
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
        ⟨p, mem_xiRectangleIndices.mpr (by simpa only [hpv] using ⟨hbottom, htop⟩), hpv⟩))
    · exact fun hs => ⟨hVinR hs.1, hs.2⟩
  have hrect : RectangleIntegral' G (lowerLeft Hm) (upperRight b Hp) =
      sumResiduesIn G (V : Set ℂ) := by
    rw [RectangleIntegral'_eq_sumResiduesIn (by simp; linarith) (by simpa using hH)
      hmero.meromorphicOn hdisj
      (BombieriVinogradov.ComplexAnalysis.finite_polesIn_rectangle G _ _ hmero.meromorphicOn)
      (simple_zetaCenteredIntegrand ht _)]
    exact sumResiduesIn_inter_eq_of_set_eq hset (fun s _ hs =>
      residue_eq_zero_of_not_pole_of_meromorphicAt (hmero s) (le_of_not_gt hs))
  have hnot : (1 : ℂ) ∉ xiRectangleValues Hp Hm := by
    intro h
    obtain ⟨p, _, hpv⟩ := Finset.mem_image.mp h
    have hr := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
    norm_num [hpv] at hr
  have hsum : ∑ rho ∈ xiRectangleValues Hp Hm, residue G rho =
      -xiRectangleCenteredSum t Hp Hm := by
    calc
      _ = -(∑ rho ∈ xiRectangleValues Hp Hm,
          (analyticOrderNatAt riemannZeta rho : ℂ) * centeredKernel t rho) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro rho hrho
        have hr1 : rho ≠ 1 := by intro h; exact hnot (h ▸ hrho)
        simpa only [G, neg_mul] using residue_zetaCenteredIntegrand_of_ne_one ht hr1
      _ = _ := by rw [sum_xiRectangle_values]; rfl
  rw [hrect, BombieriVinogradov.ComplexAnalysis.sumResiduesIn_finset,
    Finset.sum_insert hnot, hsum]
  change residue (zetaCenteredIntegrand t) 1 - _ = _
  rw [residue_zetaCenteredIntegrand_one ht]

theorem zeta_selected_border {b Hp Hm B : ℝ} (hb : 1 < b) (hp : 0 < Hp) (hm : Hm < 0)
    (hB : 0 < B)
    (hsp : ∀ p : RiemannXiDivisorZeroIndex, B⁻¹ ≤ |(riemannXiDivisorZeroValue p).im - Hp|)
    (hsm : ∀ p : RiemannXiDivisorZeroIndex, B⁻¹ ≤ |(riemannXiDivisorZeroValue p).im - Hm|) :
    ∀ s ∈ RectangleBorder (lowerLeft Hm) (upperRight b Hp),
      s ≠ 1 ∧ riemannZeta s ≠ 0 := by
  intro s hs
  rcases (mem_border hb.le (by linarith) s).mp hs with ((hs | hs) | hs | hs)
  · refine ⟨?_, zeta_ne_zero_separated hB hsm hs.2 hs.1.1⟩
    intro h
    norm_num [h] at hs
    linarith [hs.2]
  · refine ⟨?_, zeta_ne_zero_left hs.1⟩
    intro h
    norm_num [h] at hs
  · refine ⟨?_, zeta_ne_zero_separated hB hsp hs.2 hs.1.1⟩
    intro h
    norm_num [h] at hs
    linarith [hs.2]
  · refine ⟨?_, riemannZeta_ne_zero_of_one_lt_re (by linarith [hs.1])⟩
    intro h
    norm_num [h] at hs
    linarith [hs.1]

theorem zetaRightIntegral_eq_vertical {b : ℝ} (hb : 0 < b) (t Hp Hm : ℝ) :
    zetaRightIntegral t b Hm Hp = verticalIntegral (zetaCenteredIntegrand t) b Hp Hm := by
  unfold zetaRightIntegral ExplicitPerron.vertical verticalIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  have hs0 : (b : ℂ) + (u : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  dsimp only
  rw [zetaCenteredIntegrand_eq hs0]
  ring

theorem zeta_right_add_rectangle_zeros {t b Hp Hm : ℝ}
    (ht : 0 < t) (hb : 1 < b) (hp : 0 < Hp) (hm : Hm < 0)
    (hborder : ∀ s ∈ RectangleBorder (lowerLeft Hm) (upperRight b Hp),
      s ≠ 1 ∧ riemannZeta s ≠ 0) :
    zetaRightIntegral t b Hm Hp - ((t : ℂ) - 2.5) + xiRectangleCenteredSum t Hp Hm =
      threeSides (zetaCenteredIntegrand t) b Hp Hm := by
  rw [zetaRightIntegral_eq_vertical (by linarith), rectangle_orientation,
    zeta_rectangle_residue ht hb hp hm hborder]
  ring

end LiuWang.Proof.PrincipalPsi.Quantitative
