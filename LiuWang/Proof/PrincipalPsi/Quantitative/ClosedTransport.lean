import LiuWang.Proof.PrincipalPsi.Quantitative.Rectangle

/-! # 所选上下高度到原闭高度的局部计数运输 -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped BigOperators
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.NonSymmetricContour

namespace LiuWang.Proof.PrincipalPsi.Quantitative

def changedXiIndices (T Hp Hm : ℝ) : Finset RiemannXiDivisorZeroIndex := by
  classical
  exact (xiRectangleIndices Hp Hm \ xiWindow 0 T) ∪ (xiWindow 0 T \ xiRectangleIndices Hp Hm)

theorem changedXiIndices_edge {T Hp Hm : ℝ}
    (hp : |Hp - T| ≤ 1) (hm : |Hm + T| ≤ 1)
    {p : RiemannXiDivisorZeroIndex} (h : p ∈ changedXiIndices T Hp Hm) :
    p ∈ xiWindow T 1 ∨ p ∈ xiWindow (-T) 1 := by
  classical
  have hp' := abs_le.mp hp
  have hm' := abs_le.mp hm
  simp only [changedXiIndices, Finset.mem_union, Finset.mem_sdiff,
    mem_xiRectangleIndices, mem_xiWindow, sub_zero] at h
  rw [mem_xiWindow, mem_xiWindow]
  rcases h with ⟨hr, hz⟩ | ⟨hz, hr⟩
  · rcases lt_abs.mp (lt_of_not_ge hz) with hy | hy
    · left
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · right
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hz' := abs_le.mp hz
    by_cases hy : (riemannXiDivisorZeroValue p).im ≤ Hm
    · right
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have hy' : Hp ≤ (riemannXiDivisorZeroValue p).im := by
        by_contra hh
        exact hr ⟨lt_of_not_ge hy, lt_of_not_ge hh⟩
      left
      exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem changedXiIndices_card_le {T Hp Hm : ℝ}
    (hp : |Hp - T| ≤ 1) (hm : |Hm + T| ≤ 1) :
    ((changedXiIndices T Hp Hm).card : ℝ) ≤ 10 * referenceMass T := by
  classical
  have hsub : changedXiIndices T Hp Hm ⊆ xiWindow T 1 ∪ xiWindow (-T) 1 := by
    intro p hp'
    exact Finset.mem_union.mpr (changedXiIndices_edge hp hm hp')
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hc : ((changedXiIndices T Hp Hm).card : ℝ) ≤
      ((xiWindow T 1).card : ℝ) + ((xiWindow (-T) 1).card : ℝ) := by exact_mod_cast h
  have hn := xiWindow_local_card_le (-T)
  rw [referenceMass, abs_neg] at hn
  have hp' := xiWindow_local_card_le T
  unfold referenceMass at hp' ⊢
  linarith

theorem norm_transport_to_closed {t T Hp Hm : ℝ}
    (ht : 1 ≤ t) (hT : 1 < T) (hp : |Hp - T| ≤ 1) (hm : |Hm + T| ≤ 1) :
    ‖xiRectangleCenteredSum t Hp Hm - closedCenteredZeroSum 1 t T‖ ≤
      10 * referenceMass T * ((t + 2.5) / (T - 1)) := by
  classical
  have hzero (p : RiemannXiDivisorZeroIndex) := riemannXiDivisorZeroValue_ne_zero p
  have hsum : closedCenteredZeroSum 1 t T =
      ∑ p ∈ xiWindow 0 T, centeredKernel t (riemannXiDivisorZeroValue p) := by
    unfold closedCenteredZeroSum
    rw [sum_principal_closed_eq_xi T (fun rho => ((t : ℂ) ^ rho - (2.5 : ℂ) ^ rho) / rho)]
    exact Finset.sum_congr rfl (fun p _ => (centeredKernel_eq (hzero p)).symm)
  rw [hsum, xiRectangleCenteredSum]
  apply (FixedHeightZeroSum.norm_sum_sub_sum_le_changed
    (xiRectangleIndices Hp Hm) (xiWindow 0 T) _ ?_).trans
  · exact mul_le_mul_of_nonneg_right (changedXiIndices_card_le hp hm) (by positivity)
  · intro p hpi
    have he := changedXiIndices_edge hp hm hpi
    have hn : T - 1 ≤ ‖riemannXiDivisorZeroValue p‖ := by
      apply le_trans _ (Complex.abs_im_le_norm _)
      rcases he with he | he
      · have hh := (abs_le.mp (mem_xiWindow.mp he)).1
        linarith [le_abs_self (riemannXiDivisorZeroValue p).im]
      · have hh := (abs_le.mp (mem_xiWindow.mp he)).2
        linarith [neg_le_abs (riemannXiDivisorZeroValue p).im]
    rw [centeredKernel_eq (hzero p)]
    exact FixedHeightZeroSum.norm_centered_kernel_edge_le ht hT
      (riemannXiDivisorZeroValue_re_mem_Ioo p).2.le hn

end LiuWang.Proof.PrincipalPsi.Quantitative
