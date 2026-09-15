import LiuWang.Proof.SourceRoute.ThirdArc.BetaIntegrals
import LiuWang.Proof.WeightedLowZeros.Weight

/-! The genuine weight in (5.22), not a constant envelope for its beta integral. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc

def lowCoefficient (beta : ℝ) : ℝ := (1 - (0.001 : ℝ) ^ beta) / beta

theorem lowCoefficient_integral {beta : ℝ} (hb : 0 < beta) :
    lowCoefficient beta = ∫ t in (0.001 : ℝ)..1, t ^ (beta - 1) := by
  have h := WeightedLowZeros.weight_eq_integral (N := 1) (by norm_num) hb
  simpa only [WeightedLowZeros.weight, Nat.cast_one, Real.one_rpow, mul_one, div_one,
    show (1 : ℝ) / 1000 = 0.001 by norm_num, lowCoefficient] using h

theorem lowCoefficient_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    lowCoefficient b ≤ lowCoefficient a := by
  rw [lowCoefficient_integral (ha.trans_le hab), lowCoefficient_integral ha]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (WeightedLowZeros.intervalIntegrable_weight_kernel (by norm_num) (by norm_num) b)
    (WeightedLowZeros.intervalIntegrable_weight_kernel (by norm_num) (by norm_num) a)
  intro t ht
  exact Real.rpow_le_rpow_of_exponent_ge (by linarith [ht.1]) ht.2 (by linarith)

theorem lowCoefficient_nonneg {beta : ℝ} (hb : 0 < beta) :
    0 ≤ lowCoefficient beta := by
  exact div_nonneg (sub_nonneg.mpr
    (Real.rpow_le_one (by norm_num) (by norm_num) hb.le)) hb.le

theorem lowCoefficient_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn lowCoefficient (Set.Icc a b) := by
  intro beta hb
  apply ContinuousAt.continuousWithinAt
  unfold lowCoefficient
  have hbeta : beta ≠ 0 := (ha.trans_le hb.1).ne'
  exact (continuousAt_const.sub (Real.continuousAt_const_rpow (by norm_num))).div
    continuousAt_id hbeta

theorem low_integrand_integrable {X a b : ℝ}
    (hX : 0 < X) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun alpha => betaKernel X alpha * lowCoefficient alpha) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact (betaKernel_continuous hX).continuousOn.mul (lowCoefficient_continuousOn ha)

theorem low_single_partialSummation {X a b c : ℝ}
    (hX : 1 ≤ X) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    lowCoefficient b * X ^ (b - 1) ≤
      lowCoefficient a * X ^ (a - 1) +
        ∫ alpha in a..c, (Set.Iic b).indicator
          (fun alpha => betaKernel X alpha * lowCoefficient alpha) alpha := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hmono := lowCoefficient_antitone ha hab
  have hbase : lowCoefficient b * X ^ (a - 1) ≤ lowCoefficient a * X ^ (a - 1) :=
    mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hX0.le _)
  have hint :
      (∫ alpha in a..b, lowCoefficient b * betaKernel X alpha) ≤
        ∫ alpha in a..b, betaKernel X alpha * lowCoefficient alpha := by
    apply intervalIntegral.integral_mono_on hab
      (((betaKernel_continuous hX0).intervalIntegrable a b).const_mul _)
      (low_integrand_integrable hX0 ha hab)
    intro alpha halpha
    have hc := lowCoefficient_antitone (ha.trans_le halpha.1) halpha.2
    have hk : 0 ≤ betaKernel X alpha :=
      mul_nonneg (Real.rpow_nonneg hX0.le _) (Real.log_nonneg hX)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hc hk
  have hind :
      (∫ alpha in a..c, (Set.Iic b).indicator
        (fun alpha => betaKernel X alpha * lowCoefficient alpha) alpha) =
      ∫ alpha in a..b, betaKernel X alpha * lowCoefficient alpha :=
    intervalIntegral.integral_indicator ⟨hab, hbc⟩
  rw [hind]
  rw [intervalIntegral.integral_const_mul, integral_betaKernel hX0] at hint
  nlinarith

theorem finite_low_partialSummation {ι : Type*} (s : Finset ι) (b w : ι → ℝ)
    {X a c : ℝ} (hX : 1 ≤ X) (ha : 0 < a) (hac : a ≤ c)
    (hb : ∀ i ∈ s, a ≤ b i ∧ b i ≤ c) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (lowCoefficient (b i) * X ^ (b i - 1))) ≤
      lowCoefficient a * X ^ (a - 1) * (∑ i ∈ s, w i) +
        ∫ alpha in a..c,
          (betaKernel X alpha * lowCoefficient alpha) * upperMass s b w alpha := by
  simp_rw [upperMass_integrand s b w (fun alpha => betaKernel X alpha * lowCoefficient alpha)]
  have hf := low_integrand_integrable (lt_of_lt_of_le zero_lt_one hX) ha hac
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left
      (low_single_partialSummation hX ha (hb i hi).1 (hb i hi).2) (hw i hi)
    simpa only [mul_add, mul_comm, mul_left_comm, mul_assoc] using h
  · intro i _
    exact (indicator_integrable hf measurableSet_Iic).const_mul _

theorem low_character_partialSummation {q : ℕ} [NeZero q]
    (chi : Character q) {N : ℕ} (hN : 0 < N) (v : ℝ) :
    (∑ rho ∈ DirichletZeroCount.zeroValues chi (1 / 2) v,
      (analyticOrderNatAt chi.LFunction rho : ℝ) *
        (lowCoefficient rho.re * (N : ℝ) ^ (rho.re - 1))) ≤
      lowCoefficient (1 / 2) * (N : ℝ) ^ (-1 / 2 : ℝ) *
        DirichletZeroCount.count chi (1 / 2) v +
        ∫ alpha in (1 / 2 : ℝ)..1,
          (betaKernel N alpha * lowCoefficient alpha) *
            DirichletZeroCount.count chi alpha v := by
  have h := finite_low_partialSummation (DirichletZeroCount.zeroValues chi (1 / 2) v)
    Complex.re (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ))
    (X := N) (a := 1 / 2) (c := 1) (by exact_mod_cast hN) (by norm_num) (by norm_num)
    (by
      intro rho hrho
      have hr := DirichletZeroCount.mem_zeroValues.mp hrho
      exact ⟨hr.2.2, hr.2.1.2.1.le⟩)
    (fun _ _ => Nat.cast_nonneg _)
  have hcount {alpha : ℝ} (ha : 1 / 2 ≤ alpha) :
      upperMass (DirichletZeroCount.zeroValues chi (1 / 2) v) Complex.re
        (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ)) alpha =
          DirichletZeroCount.count chi alpha v := by
    have hsets :
        (DirichletZeroCount.zeroValues chi (1 / 2) v).filter
          (fun rho => alpha ≤ rho.re) = DirichletZeroCount.zeroValues chi alpha v := by
      ext rho
      simp only [Finset.mem_filter, DirichletZeroCount.mem_zeroValues]
      constructor
      · tauto
      · rintro ⟨hz, hs, hb⟩
        exact ⟨⟨hz, hs, ha.trans hb⟩, hb⟩
    simp only [upperMass, hsets, DirichletZeroCount.count, Nat.cast_sum]
  apply h.trans_eq
  simp only [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num,
    DirichletZeroCount.count, Nat.cast_sum]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro alpha ha
  rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ha
  dsimp only
  rw [hcount ha.1.le, DirichletZeroCount.count, Nat.cast_sum]

end LiuWang.Proof.SourceRoute.ThirdArc
