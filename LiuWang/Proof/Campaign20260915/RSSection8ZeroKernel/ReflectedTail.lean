import LiuWang.Proof.Campaign20260915.Totient.RSZeroDifferenceSum
import LiuWang.Proof.ZeroRegionFamily.Sharp.ZetaKernel

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.ZeroRegionFamily.Sharp
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel

private theorem exp_pair_le {β L B : ℝ} (hL : 0 ≤ L)
    (hleft : Real.exp ((β - 1) * L) ≤ B)
    (hright : Real.exp (-β * L) ≤ B) :
    Real.exp ((β - 1) * L) + Real.exp (-β * L) ≤ Real.exp (-L / 2) + B := by
  by_cases hβ : β ≤ 1 / 2
  · have h := Real.exp_le_exp.mpr
      (show (β - 1) * L ≤ -L / 2 by nlinarith)
    exact add_le_add h hright
  · have h := Real.exp_le_exp.mpr (show -β * L ≤ -L / 2 by nlinarith)
    linarith

private theorem regional_exp_le {K L : ℝ} (hL : 0 ≤ L)
    (p : RiemannXiDivisorZeroIndex)
    (hp : rsA < |(riemannXiDivisorZeroValue p).im|)
    (hpK : |(riemannXiDivisorZeroValue p).im| ≤ K) :
    Real.exp (((riemannXiDivisorZeroValue p).re - 1) * L) ≤
      Real.exp (-(L / (rsR * Real.log K))) := by
  have hγ : 1 < |(riemannXiDivisorZeroValue p).im| := by
    linarith [rsA_ge_thousand]
  have hi := one_div_le_one_div_of_le
    (mul_pos rsR_pos (Real.log_pos hγ))
    (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) hpK) rsR_pos.le)
  have hg := hi.trans (rs_zero_gap p hp.le).le
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hg hL
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm]

theorem reflected_tail_pointwise {K L : ℝ} (hK : rsA ≤ K) (hL : 0 ≤ L)
    (p : RiemannXiDivisorZeroIndex) :
    rsHighTerm rsA 1 L p + rsHighTerm rsA 1 L (xiReflection p) ≤
      Real.exp (-L / 2) * rsHighTerm rsA 1 0 p +
        Real.exp (-(L / (rsR * Real.log K))) * rsHighTerm rsA 1 0 p +
          rsHighTerm K 1 0 p := by
  have href : riemannXiDivisorZeroValue (xiReflection p) =
      1 - conj (riemannXiDivisorZeroValue p) := rfl
  have him : (riemannXiDivisorZeroValue (xiReflection p)).im =
      (riemannXiDivisorZeroValue p).im := by simp [href]
  have hre : (riemannXiDivisorZeroValue (xiReflection p)).re =
      1 - (riemannXiDivisorZeroValue p).re := by simp [href]
  by_cases hp : rsA < |(riemannXiDivisorZeroValue p).im|
  · have hrp : rsA < |(riemannXiDivisorZeroValue (xiReflection p)).im| := by
      rwa [him]
    by_cases hpK : K < |(riemannXiDivisorZeroValue p).im|
    · have hleft : Real.exp (((riemannXiDivisorZeroValue p).re - 1) * L) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (by linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).2]) hL)
      have hright : Real.exp (-(riemannXiDivisorZeroValue p).re * L) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (riemannXiDivisorZeroValue_re_mem_Ioo p).1.le) hL)
      have he := exp_pair_le hL hleft hright
      have hd := div_le_div_of_nonneg_right he
        (sq_nonneg |(riemannXiDivisorZeroValue p).im|)
      have hn : 0 ≤ Real.exp (-(L / (rsR * Real.log K))) /
          |(riemannXiDivisorZeroValue p).im| ^ 2 := by positivity
      simp only [rsHighTerm, him, hre, if_pos hp, if_pos hpK, mul_zero,
        Real.exp_zero, show 1 + 1 = 2 from rfl,
        show 1 - (riemannXiDivisorZeroValue p).re - 1 =
          -(riemannXiDivisorZeroValue p).re by ring]
      simp only [add_div] at hd
      simp only [mul_one_div]
      linarith
    · have hleft := regional_exp_le hL p hp (le_of_not_gt hpK)
      have hright := regional_exp_le hL (xiReflection p) hrp
        (by simpa [him] using le_of_not_gt hpK)
      rw [hre, show 1 - (riemannXiDivisorZeroValue p).re - 1 =
        -(riemannXiDivisorZeroValue p).re by ring] at hright
      have he := exp_pair_le hL hleft hright
      have hd := div_le_div_of_nonneg_right he
        (sq_nonneg |(riemannXiDivisorZeroValue p).im|)
      simp only [rsHighTerm, him, hre, if_pos hp, if_neg hpK, mul_zero,
        Real.exp_zero, add_zero, show 1 + 1 = 2 from rfl,
        show 1 - (riemannXiDivisorZeroValue p).re - 1 =
          -(riemannXiDivisorZeroValue p).re by ring]
      simpa only [add_div, mul_one_div] using hd
  · have hpK : ¬ K < |(riemannXiDivisorZeroValue p).im| := by
      exact not_lt.mpr ((le_of_not_gt hp).trans hK)
    simp only [rsHighTerm, him, if_neg hp, if_neg hpK, mul_zero, add_zero, le_refl]

/-- Reflection preserves the divisor index, including its multiplicity coordinate.
The factor 1/2 is not an unproved replacement of a two-sided sum by a positive sum. -/
theorem reflected_tail_sum {K L : ℝ} (hK : rsA ≤ K) (hL : 0 ≤ L) :
    (∑' p, rsHighTerm rsA 1 L p) ≤
      Real.exp (-L / 2) / 2 * (∑' p, rsHighTerm rsA 1 0 p) +
        Real.exp (-(L / (rsR * Real.log K))) / 2 *
          (∑' p, rsHighTerm rsA 1 0 p) +
            (∑' p, rsHighTerm K 1 0 p) / 2 := by
  have hs := rsHighTerm_summable (le_refl rsA) hL (by norm_num : 1 ≤ (1 : ℕ))
  have hr : Summable (fun p => rsHighTerm rsA 1 L (xiReflection p)) :=
    xiReflection.summable_iff.mpr hs
  have hA := rsHighTerm_summable (le_refl rsA) (le_refl (0 : ℝ))
    (by norm_num : 1 ≤ (1 : ℕ))
  have hK0 := rsHighTerm_summable hK (le_refl (0 : ℝ)) (by norm_num : 1 ≤ (1 : ℕ))
  have hE := hA.mul_left (Real.exp (-L / 2))
  have hF := hA.mul_left (Real.exp (-(L / (rsR * Real.log K))))
  have ht := (hs.add hr).tsum_le_tsum (reflected_tail_pointwise hK hL)
    ((hE.add hF).add hK0)
  rw [hs.tsum_add hr, xiReflection.tsum_eq, (hE.add hF).tsum_add hK0,
    hE.tsum_add hF, tsum_mul_left, tsum_mul_left] at ht
  linarith

def closedMomentTerm (H L : ℝ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
  if |(riemannXiDivisorZeroValue p).im| ≤ H then rsZeroMoment 1 L p else 0

theorem closedMomentTerm_summable (H : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    Summable (closedMomentTerm H L) := by
  apply Summable.of_nonneg_of_le
    (fun p => by unfold closedMomentTerm rsZeroMoment; split_ifs <;> positivity)
    (f := rsZeroMoment 1 L) _ (rsZeroMoment_summable (by norm_num) hL)
  intro p
  unfold closedMomentTerm
  split_ifs
  · exact le_rfl
  · unfold rsZeroMoment
    positivity

theorem actual_moment_split {L : ℝ} (hL : 0 ≤ L) :
    (∑' p, rsZeroMoment 1 L p) =
      (∑' p, closedMomentTerm rsA L p) + ∑' p, rsHighTerm rsA 1 L p := by
  rw [← (closedMomentTerm_summable rsA hL).tsum_add
    (rsHighTerm_summable (le_refl rsA) hL (by norm_num))]
  apply tsum_congr
  intro p
  by_cases hp : rsA < |(riemannXiDivisorZeroValue p).im|
  · simp [closedMomentTerm, rsHighTerm, rsZeroMoment, hp, not_le.mpr hp]
  · simp [closedMomentTerm, rsHighTerm, rsZeroMoment, hp, le_of_not_gt hp]

theorem actual_moment_variable_cutoff {K L : ℝ} (hK : rsA ≤ K) (hL : 0 ≤ L) :
    (∑' p, rsZeroMoment 1 L p) ≤
      (∑' p, closedMomentTerm rsA L p) +
        Real.exp (-L / 2) / 2 * (∑' p, rsHighTerm rsA 1 0 p) +
          Real.exp (-(L / (rsR * Real.log K))) / 2 *
            (∑' p, rsHighTerm rsA 1 0 p) +
              (∑' p, rsHighTerm K 1 0 p) / 2 := by
  rw [actual_moment_split hL]
  have h := reflected_tail_sum hK hL
  linarith

#print axioms reflected_tail_sum
#print axioms actual_moment_variable_cutoff

end LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel
