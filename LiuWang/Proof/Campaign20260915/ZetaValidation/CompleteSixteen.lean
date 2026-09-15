import LiuWang.Proof.Campaign20260915.ZetaValidation.CountingPrimitive
import LiuWang.Proof.Campaign20260915.ZetaValidation.ActualMultiplicity

set_option autoImplicit false
noncomputable section
open Complex
open scoped ComplexConjugate
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem xiCountingPrimitive_two_im : (xiCountingPrimitive 2).im = 0 := by
  have hz : (riemannZeta 2).im = 0 := by
    have h := riemannZeta_conj (2 : ℂ)
    have hi := congrArg Complex.im h
    simp only [map_ofNat, conj_im] at hi
    linarith
  have hp : 0 < (riemannZeta 2).re := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      LiuWang.Proof.DirichletZeroCount.Remainder.LFunction_re_pos
        (1 : LiuWang.Proof.Interfaces.Character 1) (s := 2) (by norm_num)
  have hg : (gammaLogBranch 1).im = 0 := by
    exact LiuWang.Proof.DirichletZeroCount.Remainder.logGamma_real_im_zero
      (x := 1) (by norm_num)
  have hl : (log (riemannZeta 2)).im = 0 := by
    rw [log_im_of_re_pos hp, hz, zero_div, Real.arctan_zero]
  norm_num [xiCountingPrimitive, hl, hg, log_im]

theorem critical_polynomial_argument :
    (log (criticalPoint 16)).im + (log (criticalPoint 16 - 1)).im = Real.pi := by
  have he : criticalPoint 16 - 1 = -conj (criticalPoint 16) := by
    apply Complex.ext <;> norm_num [criticalPoint]
  have hp : (criticalPoint 16).arg ≠ Real.pi := by
    have h := (arg_lt_pi_div_two_iff).mpr (Or.inl (by norm_num [criticalPoint] :
      0 < (criticalPoint 16).re))
    linarith [Real.pi_pos]
  rw [he, log_im, log_im, arg_neg_eq_arg_add_pi_of_im_neg
    (by norm_num [criticalPoint] : (conj (criticalPoint 16)).im < 0), arg_conj, if_neg hp]
  ring

theorem xiCountingPrimitive_sixteen_im :
    (xiCountingPrimitive (criticalPoint 16)).im =
      (riemannZeta (criticalPoint 16)).arg + Real.pi + criticalGammaArgument 16 := by
  have hp := critical_polynomial_argument
  simp only [xiCountingPrimitive, criticalGammaArgument, sub_im, add_im, log_im] at hp ⊢
  linarith

theorem xi_upper_integral_sixteen_lt :
    (Argument.upperRightIntegral (logDeriv riemannXi) 2 16).im < 3 * Real.pi / 2 := by
  rw [xi_upper_integral_primitive, sub_im, xiCountingPrimitive_two_im, sub_zero,
    xiCountingPrimitive_sixteen_im]
  have hp : 0 < (riemannZeta (criticalPoint 16)).re := by
    simpa only [horizontalPoint, criticalPoint] using horizontal_zeta_re_pos (sigma := 1 / 2) le_rfl
  have ha := arg_lt_pi_div_two_iff.mpr (Or.inl hp)
  have ht := gamma16_argument_rational_enclosure.2
  linarith

theorem zetaClosedCount_sixteen : zetaClosedCount 16 = 2 := by
  have hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = 16 →
      (1 : LiuWang.Proof.Interfaces.Character 1).LFunction s ≠ 0 := by
    intro s h0 h1 ht
    simpa only [DirichletCharacter.LFunction_modOne_eq] using zeta_ne_zero_height_sixteen h0 h1 ht
  have hc := Argument.principal_count_eq_upper_im 1 (b := 2) (H := 16)
    (by norm_num) (by norm_num) hreg
  rw [← zetaClosedCount_eq_principal] at hc
  have hlt : (zetaClosedCount 16 : ℝ) < 3 := by
    rw [hc, div_lt_iff₀ Real.pi_pos]
    linarith [xi_upper_integral_sixteen_lt]
  have hn : zetaClosedCount 16 < 3 := by exact_mod_cast hlt
  have hl := zetaClosedCount_sixteen_lower
  omega

theorem zetaClosedValues_sixteen_pair :
    ∃ t ∈ Set.Ioo (1 : ℝ) 16,
      zetaClosedValues 16 = {criticalPoint t, conj (criticalPoint t)} := by
  classical
  obtain ⟨t, ht, hz⟩ := exists_nontrivial_zero_below_sixteen
  have ht0 : 0 < t := by linarith [ht.1]
  have ht1 : 1 < t := by
    by_contra hn
    exact zeta_ne_zero_closed_height_one (by norm_num [criticalPoint])
      (by norm_num [criticalPoint])
      (by simpa only [criticalPoint, abs_of_pos ht0] using not_lt.mp hn) hz
  have hp : criticalPoint t ∈ zetaClosedValues 16 :=
    mem_zetaClosedValues.mpr ⟨hz, by norm_num [criticalPoint],
      by norm_num [criticalPoint], by simpa [criticalPoint, abs_of_pos ht0] using ht.2.le⟩
  have hc : conj (criticalPoint t) ∈ zetaClosedValues 16 := by
    apply mem_zetaClosedValues.mpr
    refine ⟨?_, by norm_num [criticalPoint], by norm_num [criticalPoint], ?_⟩
    · rw [riemannZeta_conj, hz, map_zero]
    · simpa [criticalPoint, abs_of_pos ht0] using ht.2.le
  have hne : criticalPoint t ≠ conj (criticalPoint t) := by
    intro he
    have hi := congrArg Complex.im he
    simp only [criticalPoint, conj_im] at hi
    linarith
  have hsub : {criticalPoint t, conj (criticalPoint t)} ⊆ zetaClosedValues 16 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hcard := zetaClosedValues_card_le_count 16
  rw [zetaClosedCount_sixteen] at hcard
  refine ⟨t, ⟨ht1, ht.2⟩, ?_⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by simpa only [Finset.card_pair hne] using hcard)).symm

theorem zeta_sixteen_all_simple_on_line {s : ℂ}
    (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) (ht : |s.im| ≤ 16) :
    s.re = 1 / 2 ∧ analyticOrderNatAt riemannZeta s = 1 := by
  classical
  obtain ⟨t, ht', he⟩ := zetaClosedValues_sixteen_pair
  have hp : criticalPoint t ∈ zetaClosedValues 16 := by rw [he]; simp
  have hc : conj (criticalPoint t) ∈ zetaClosedValues 16 := by rw [he]; simp
  have hne : criticalPoint t ≠ conj (criticalPoint t) := by
    intro hh
    have hi := congrArg Complex.im hh
    simp only [criticalPoint, conj_im] at hi
    linarith [ht'.1]
  have hsum := zetaClosedCount_sixteen
  rw [zetaClosedCount, he, Finset.sum_pair hne] at hsum
  have hpos1 := zeta_order_positive_of_mem hp
  have hpos2 := zeta_order_positive_of_mem hc
  have ho1 : analyticOrderNatAt riemannZeta (criticalPoint t) = 1 := by omega
  have ho2 : analyticOrderNatAt riemannZeta (conj (criticalPoint t)) = 1 := by omega
  have hm := mem_zetaClosedValues.mpr ⟨hz, h0, h1, ht⟩
  rw [he, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact ⟨rfl, ho1⟩
  · exact ⟨by norm_num [criticalPoint], ho2⟩

#print axioms xi_upper_integral_sixteen_lt
#print axioms zetaClosedCount_sixteen
#print axioms zetaClosedValues_sixteen_pair
#print axioms zeta_sixteen_all_simple_on_line

end LiuWang.Proof.Campaign20260915.ZetaValidation
