import LiuWang.Proof.DirichletZeroCount.RealKernel

/-! # Zeta/principal count producers without a low-zero numerical table -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.PrincipalPsi.Quantitative
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount

theorem xi_count_real_parameter {y s : ℝ} (hy : 0 ≤ y) (hs : 4 ≤ s)
    (hys : y + 1 ≤ s) :
    ((xiWindow 0 y).card : ℝ) ≤
      (s + y) * (Real.log s / 2 + 1 / (s - 1) + 1 / 3) := by
  have hs1 : 1 ≤ (s : ℂ).re := by simp; linarith
  have hsum := Complex.reCLM.summable (xiTerm_summable hs1)
  have hsy : 0 < s + y := by linarith
  have hc : ((xiWindow 0 y).card : ℝ) / (s + y) ≤
      (∑' p, xiTerm (s : ℂ) p).re := by
    rw [Complex.re_tsum (xiTerm_summable hs1)]
    calc
      _ = ∑ _p ∈ xiWindow 0 y, 1 / (s + y) := by simp [div_eq_mul_inv]
      _ ≤ ∑ p ∈ xiWindow 0 y, (xiTerm (s : ℂ) p).re := by
        apply Finset.sum_le_sum
        intro p hp
        have hr := riemannXiDivisorZeroValue_re_mem_Ioo p
        have ht : |(riemannXiDivisorZeroValue p).im| ≤ y := by
          simpa using mem_xiWindow.mp hp
        have hk := real_kernel_lower hy hys hr ht
        have hp0 : 0 ≤ (1 / riemannXiDivisorZeroValue p).re := by
          rw [one_div, Complex.inv_re]
          exact div_nonneg hr.1.le (Complex.normSq_nonneg _)
        simpa only [xiTerm, Complex.add_re] using hk.trans (le_add_of_nonneg_right hp0)
      _ ≤ _ := hsum.sum_le_tsum _ (fun p _ => xiTerm_re_nonneg hs1 p)
  have hm := xiTerm_sum_real_le hs
  have hbound : (∑' p, xiTerm (s : ℂ) p).re ≤
      Real.log s / 2 + 1 / (s - 1) + 1 / 3 := by linarith
  exact (div_le_iff₀ hsy).mp (hc.trans hbound) |>.trans_eq (mul_comm _ _)

theorem count_principal_real_parameter (q : ℕ) [NeZero q] (alpha : ℝ)
    {y s : ℝ} (hy : 0 ≤ y) (hs : 4 ≤ s) (hys : y + 1 ≤ s) :
    (count (1 : Character q) alpha y : ℝ) ≤
      (s + y) * (Real.log s / 2 + 1 / (s - 1) + 1 / 3) := by
  rw [count_principal_eq_zeta, count_principal]
  have hc : ((principalIndices 1 alpha y).card : ℝ) ≤
      ((PrincipalPsi.closedZeroIndices 1 y).card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  rw [card_principal_closed_eq_xi] at hc
  exact hc.trans (xi_count_real_parameter hy hs hys)

theorem count_principal_linear (q : ℕ) [NeZero q] (alpha : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    (count (1 : Character q) alpha y : ℝ) ≤
      (2 * y + 4) * (Real.log (y + 4) / 2 + 1 / (y + 3) + 1 / 3) := by
  convert count_principal_real_parameter q alpha hy
    (s := y + 4) (by linarith) (by linarith) using 1
  ring

theorem count_principal_low (q : ℕ) [NeZero q] (alpha : ℝ)
    {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    count (1 : Character q) alpha y = 0 := by
  have hc := count_principal_quadratic q alpha hy
  have hlt : (count (1 : Character q) alpha y : ℝ) < 1 := by nlinarith
  have hnat : count (1 : Character q) alpha y < 1 := by exact_mod_cast hlt
  omega

def principalBound (y : ℝ) : ℝ :=
  if y ≤ 1 then 0 else
    min ((2 / 3) * y ^ 2)
      ((2 * y + 4) * (Real.log (y + 4) / 2 + 1 / (y + 3) + 1 / 3))

theorem count_principal_le (q : ℕ) [NeZero q] (alpha : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    (count (1 : Character q) alpha y : ℝ) ≤ principalBound y := by
  unfold principalBound
  split_ifs with h
  · rw [count_principal_low q alpha hy h]
    simp
  · exact le_min (count_principal_quadratic q alpha hy) (count_principal_linear q alpha hy)

theorem principalBound_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ principalBound y :=
  (Nat.cast_nonneg (count (1 : Character 1) 0 y)).trans (count_principal_le 1 0 hy)

end LiuWang.Proof.DirichletZeroCount
