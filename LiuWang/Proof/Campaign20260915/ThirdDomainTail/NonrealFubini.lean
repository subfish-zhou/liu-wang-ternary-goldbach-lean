import LiuWang.Proof.Campaign20260915.ThirdDomainTail.NonrealAbel
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.CountFubini
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.HeightPayments

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation

namespace LiuWang.Proof.Campaign20260915.ThirdDomainTail

theorem densityBand_integral_real_credit (q : ℕ) [NeZero q] {X a b u v p : ℝ}
    (hX : 1 ≤ X) (ha : 1 / 2 ≤ a) (hab : a ≤ b)
    (hu : 0 < u) (huv : u ≤ v) (hp : 0 ≤ p) :
    (∫ alpha in a..b, betaKernel X alpha * densityBand q alpha u v p) +
        u ^ (-p) * countIntegral q X 0 a b ≤
      v ^ (-p) * countIntegral q X v a b +
        ∫ y in u..v, heightKernel p y * countIntegral q X y a b := by
  have hx : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hb : IntervalIntegrable (betaKernel X) volume a b :=
    (betaKernel_continuous hx).intervalIntegrable a b
  have hg := heightKernel_integrable hu huv p
  have hband := densityBand_beta_integrable q u v p hx ha hab
  have hreal := (family_beta_integrable q 0 hx ha hab).const_mul (u ^ (-p))
  have hfirst := (family_beta_integrable q v hx ha hab).const_mul (v ^ (-p))
  have hsecond := familyCount_inner_integrable q hab huv hb hg
  have h :
      (∫ alpha in a..b,
        betaKernel X alpha * densityBand q alpha u v p +
          u ^ (-p) * (betaKernel X alpha * (familyCount q alpha 0 : ℝ))) ≤
      ∫ alpha in a..b,
        v ^ (-p) * (betaKernel X alpha * (familyCount q alpha v : ℝ)) +
          betaKernel X alpha *
            ∫ y in u..v, heightKernel p y * (familyCount q alpha y : ℝ) := by
    apply intervalIntegral.integral_mono_on hab (hband.add hreal) (hfirst.add hsecond)
    intro alpha _
    have h := mul_le_mul_of_nonneg_left
      (family_height_partialSummation_real_credit q alpha hu huv hp)
      (show 0 ≤ betaKernel X alpha from
        mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg hX))
    nlinarith only [h]
  rw [intervalIntegral.integral_add hband hreal,
    intervalIntegral.integral_add hfirst hsecond,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    countIntegral_height_swap q hx hab hu huv] at h
  exact h

theorem countIntegral_sub_real_eq_integral (q : ℕ) [NeZero q]
    {X a b : ℝ} (y : ℝ) (hX : 0 < X) (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    countIntegral q X y a b - countIntegral q X 0 a b =
      ∫ alpha in a..b, betaKernel X alpha *
        ((familyCount q alpha y : ℝ) - (familyCount q alpha 0 : ℝ)) := by
  simp only [countIntegral, mul_sub]
  exact (intervalIntegral.integral_sub
    (family_beta_integrable q y hX ha hab) (family_beta_integrable q 0 hX ha hab)).symm

theorem countIntegral_sub_real_nonneg (q : ℕ) [NeZero q]
    {X a b y : ℝ} (hX : 1 ≤ X) (ha : 1 / 2 ≤ a) (hab : a ≤ b) (hy : 0 ≤ y) :
    0 ≤ countIntegral q X y a b - countIntegral q X 0 a b := by
  rw [countIntegral_sub_real_eq_integral q y (lt_of_lt_of_le zero_lt_one hX) ha hab]
  apply intervalIntegral.integral_nonneg hab
  intro alpha _
  apply mul_nonneg
  · exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg hX)
  · apply sub_nonneg.mpr
    exact Nat.cast_le.mpr (Finset.sum_le_sum (fun chi _ => count_mono_height chi alpha hy))

theorem countIntegral_sub_real_height_integrable (q : ℕ) [NeZero q]
    {X a b u v p : ℝ} (hX : 1 ≤ X) (ha : 1 / 2 ≤ a) (hab : a ≤ b)
    (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun y => heightKernel p y *
      (countIntegral q X y a b - countIntegral q X 0 a b)) volume u v := by
  have hi := heightKernel_mul_integrable hu huv p
    (countIntegral_mono_height q hX ha hab).intervalIntegrable
  simpa only [mul_sub] using
    hi.sub ((heightKernel_integrable hu huv p).mul_const (countIntegral q X 0 a b))

theorem densityBand_integral_le_counts_sub_real (q : ℕ) [NeZero q]
    {X a b u v p : ℝ} (hX : 1 ≤ X) (ha : 1 / 2 ≤ a) (hab : a ≤ b)
    (hu : 0 < u) (huv : u ≤ v) (hp : 0 ≤ p) :
    (∫ alpha in a..b, betaKernel X alpha * densityBand q alpha u v p) ≤
      v ^ (-p) * (countIntegral q X v a b - countIntegral q X 0 a b) +
        ∫ y in u..v, heightKernel p y *
          (countIntegral q X y a b - countIntegral q X 0 a b) := by
  have h := densityBand_integral_real_credit q hX ha hab hu huv hp
  have hi := heightKernel_mul_integrable hu huv p
    (countIntegral_mono_height q hX ha hab).intervalIntegrable
  simp only [mul_sub]
  rw [intervalIntegral.integral_sub hi
    ((heightKernel_integrable hu huv p).mul_const (countIntegral q X 0 a b)),
    intervalIntegral.integral_mul_const, integral_heightKernel hu huv p]
  nlinarith only [h]

#print axioms densityBand_integral_real_credit
#print axioms countIntegral_sub_real_eq_integral
#print axioms countIntegral_sub_real_nonneg
#print axioms densityBand_integral_le_counts_sub_real

end LiuWang.Proof.Campaign20260915.ThirdDomainTail
