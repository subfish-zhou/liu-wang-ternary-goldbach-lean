import LiuWang.Proof.Campaign20260915.LowZeroMoment.FourteenEndpoint
import LiuWang.Proof.Campaign20260915.ZetaValidation.CompleteSixteen

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexConjugate
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.PrincipalPsi.Quantitative

namespace LiuWang.Proof.Campaign20260915.LowZeroMoment
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem zetaClosedValues_sixteen_pair_above_fourteen :
    ∃ t ∈ Set.Ioo (14 : ℝ) 16,
      zetaClosedValues 16 = {criticalPoint t, conj (criticalPoint t)} := by
  classical
  obtain ⟨t, ht, hz⟩ := exists_nontrivial_zero_fourteen_sixteen
  obtain ⟨u, hu, he⟩ := zetaClosedValues_sixteen_pair
  have ht0 : 0 < t := by linarith [ht.1]
  have hm : criticalPoint t ∈ zetaClosedValues 16 :=
    mem_zetaClosedValues.mpr ⟨hz, by norm_num [criticalPoint],
      by norm_num [criticalPoint], by simpa [criticalPoint, abs_of_pos ht0] using ht.2.le⟩
  rw [he, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · have htu := congrArg Complex.im hm
    change t = u at htu
    subst u
    exact ⟨t, ht, he⟩
  · have htu := congrArg Complex.im hm
    simp only [criticalPoint, conj_im] at htu
    linarith [hu.1]

theorem zeta_zero_height_gt_fourteen {s : ℂ}
    (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    14 < |s.im| := by
  classical
  by_cases ht : |s.im| ≤ 16
  · obtain ⟨t, ht', he⟩ := zetaClosedValues_sixteen_pair_above_fourteen
    have hm := mem_zetaClosedValues.mpr ⟨hz, h0, h1, ht⟩
    rw [he, Finset.mem_insert, Finset.mem_singleton] at hm
    have ht0 : 0 < t := by linarith [ht'.1]
    rcases hm with rfl | rfl <;>
      simpa [criticalPoint, abs_of_pos ht0] using ht'.1
  · linarith [lt_of_not_ge ht]

theorem xi_zero_height_gt_fourteen (p : RiemannXiDivisorZeroIndex) :
    14 < |(riemannXiDivisorZeroValue p).im| := by
  have hr := riemannXiDivisorZeroValue_re_mem_Ioo p
  have hz := (xi_zero_iff_zeta_zero (by linarith [hr.1]) (by
    intro he
    have := hr.2
    simp [he] at this)).mp (riemannXiDivisorZeroValue_eq_zero p)
  exact zeta_zero_height_gt_fourteen hz hr.1 hr.2

#print axioms zetaClosedValues_sixteen_pair_above_fourteen
#print axioms zeta_zero_height_gt_fourteen
#print axioms xi_zero_height_gt_fourteen

end LiuWang.Proof.Campaign20260915.LowZeroMoment
