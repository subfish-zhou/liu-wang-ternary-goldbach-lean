import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.MovingDomains

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdDomainTail

theorem countIntegral_le_legal_height (q : ℕ) [NeZero q]
    {X a b y : ℝ} (hX : 1 ≤ X) (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    countIntegral q X y a b ≤
      countIntegral q X (max y (max (100000 / (q : ℝ)) (10000 * Real.log q))) a b :=
  countIntegral_mono_height q hX ha hab (le_max_left _ _)

theorem countIntegral_height_gate_split (q : ℕ) [NeZero q]
    {X a b u v g p : ℝ} (hX : 1 ≤ X) (ha : 1 / 2 ≤ a) (hab : a ≤ b)
    (hu : 0 < u) (huv : u ≤ v) (hug : u ≤ g) (hp : 0 ≤ p) :
    (∫ y in u..v, heightKernel p y * countIntegral q X y a b) ≤
      (u ^ (-p) - (min v g) ^ (-p)) * countIntegral q X g a b +
        ∫ y in min v g..v, heightKernel p y * countIntegral q X y a b := by
  have hus : u ≤ min v g := le_min huv hug
  have hsv : min v g ≤ v := min_le_left _ _
  have hsg : min v g ≤ g := min_le_right _ _
  have hmono := countIntegral_mono_height q hX ha hab
  have hi (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s) :
      IntervalIntegrable (fun y => heightKernel p y * countIntegral q X y a b)
        volume r s :=
    heightKernel_mul_integrable hr hrs p hmono.intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hi u (min v g) hu hus) (hi (min v g) v (hu.trans_le hus) hsv)
  have hlow :
      (∫ y in u..min v g, heightKernel p y * countIntegral q X y a b) ≤
        (u ^ (-p) - (min v g) ^ (-p)) * countIntegral q X g a b := by
    calc
      _ ≤ ∫ y in u..min v g, heightKernel p y * countIntegral q X g a b := by
        apply intervalIntegral.integral_mono_on hus (hi u (min v g) hu hus)
          ((heightKernel_integrable hu hus p).mul_const _)
        intro y hy
        exact mul_le_mul_of_nonneg_left (hmono (hy.2.trans hsg))
          (mul_nonneg hp (Real.rpow_nonneg (hu.le.trans hy.1) _))
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, integral_heightKernel hu hus p]
  linarith only [hsplit, hlow]

theorem clipped_gate_intervals {u v g : ℝ} (huv : u ≤ v) (hug : u ≤ g) :
    u ≤ min v g ∧ min v g ≤ v ∧
      (v ≤ g → min v g = v) ∧ (g ≤ v → min v g = g) := by
  exact ⟨le_min huv hug, min_le_left _ _, min_eq_left, min_eq_right⟩

theorem moving_countIntegral_height_gate_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X u v g d p : ℝ} (hX : 1 ≤ X) (hu : lowHeight ≤ u)
    (huv : u ≤ v) (hug : u ≤ g) (hd : 0 ≤ d) (hd1 : d ≤ 0.478) (hp : 0 ≤ p) :
    (∫ y in u..v, heightKernel p y *
      countIntegral q X y (59 / 60) (sourceCutoff q d y)) ≤
      (u ^ (-p) - (min v g) ^ (-p)) *
        countIntegral q X g (59 / 60) (sourceCutoff q d g) +
        ∫ y in min v g..v, heightKernel p y *
          countIntegral q X y (59 / 60) (sourceCutoff q d y) := by
  have hu0 := lowHeight_pos.trans_le hu
  have hus : u ≤ min v g := le_min huv hug
  have hsv : min v g ≤ v := min_le_left _ _
  have hsg : min v g ≤ g := min_le_right _ _
  have hi (r s : ℝ) (hr : lowHeight ≤ r) (hrs : r ≤ s) :
      IntervalIntegrable (fun y => heightKernel p y *
        countIntegral q X y (59 / 60) (sourceCutoff q d y)) volume r s :=
    heightKernel_mul_integrable (lowHeight_pos.trans_le hr) hrs p
      (moving_countIntegral_monotone hN hq hX hr hrs hd hd1).intervalIntegrable
  have hmono := moving_countIntegral_monotone hN hq hX hu hug hd hd1
  rw [Set.uIcc_of_le hug] at hmono
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hi u (min v g) hu hus) (hi (min v g) v (hu.trans hus) hsv)
  have hlow :
      (∫ y in u..min v g, heightKernel p y *
        countIntegral q X y (59 / 60) (sourceCutoff q d y)) ≤
        (u ^ (-p) - (min v g) ^ (-p)) *
          countIntegral q X g (59 / 60) (sourceCutoff q d g) := by
    calc
      _ ≤ ∫ y in u..min v g, heightKernel p y *
          countIntegral q X g (59 / 60) (sourceCutoff q d g) := by
        apply intervalIntegral.integral_mono_on hus (hi u (min v g) hu hus)
          ((heightKernel_integrable hu0 hus p).mul_const _)
        intro y hy
        have hyg := hy.2.trans hsg
        exact mul_le_mul_of_nonneg_left (hmono ⟨hy.1, hyg⟩ ⟨hug, le_rfl⟩ hyg)
          (mul_nonneg hp (Real.rpow_nonneg (hu0.le.trans hy.1) _))
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, integral_heightKernel hu0 hus p]
  linarith only [hsplit, hlow]

#print axioms countIntegral_le_legal_height
#print axioms countIntegral_height_gate_split
#print axioms moving_countIntegral_height_gate_split

end LiuWang.Proof.Campaign20260915.ThirdDomainTail
