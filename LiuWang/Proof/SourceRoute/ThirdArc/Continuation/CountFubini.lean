import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.TableIntegrals
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Rectangular interchange for the actual full-family count in (5.31) and (5.40). -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation

theorem finite_separated_integral {ι : Type*} (s : Finset ι) (f g : ι → ℝ → ℝ)
    {a b u v : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b)
    (hg : ∀ i ∈ s, IntervalIntegrable (g i) volume u v) :
    (∫ x in a..b, ∫ y in u..v, ∑ i ∈ s, f i x * g i y) =
      ∑ i ∈ s, (∫ x in a..b, f i x) * ∫ y in u..v, g i y := by
  have hi (x : ℝ) :
      (∫ y in u..v, ∑ i ∈ s, f i x * g i y) =
        ∑ i ∈ s, f i x * ∫ y in u..v, g i y := by
    rw [intervalIntegral.integral_finsetSum (fun i hi => (hg i hi).const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  simp_rw [hi]
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).mul_const _)]
  simp only [intervalIntegral.integral_mul_const]

theorem finite_separated_swap {ι : Type*} (s : Finset ι) (f g : ι → ℝ → ℝ)
    {a b u v : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b)
    (hg : ∀ i ∈ s, IntervalIntegrable (g i) volume u v) :
    (∫ x in a..b, ∫ y in u..v, ∑ i ∈ s, f i x * g i y) =
      ∫ y in u..v, ∫ x in a..b, ∑ i ∈ s, f i x * g i y := by
  rw [finite_separated_integral s f g hf hg]
  have h := finite_separated_integral s g f hg hf
  simpa only [mul_comm] using h.symm

def rectangleZeros (q : ℕ) [NeZero q] (a v : ℝ) :
    Finset ((_chi : Character q) × ℂ) :=
  Finset.univ.sigma (fun chi => zeroValues chi a v)

theorem zeroValues_rectangle_filter {q : ℕ} [NeZero q] (chi : Character q)
    {a alpha y v : ℝ} (ha : a ≤ alpha) (hy : y ≤ v) :
    zeroValues chi alpha y =
      (zeroValues chi a v).filter (fun rho => alpha ≤ rho.re ∧ |rho.im| ≤ y) := by
  ext rho
  simp only [Finset.mem_filter, mem_zeroValues]
  constructor
  · rintro ⟨hz, ⟨h0, h1, hh⟩, halpha⟩
    exact ⟨⟨hz, ⟨h0, h1, hh.trans hy⟩, ha.trans halpha⟩, halpha, hh⟩
  · tauto

theorem familyCount_rectangle {q : ℕ} [NeZero q] {a alpha y v : ℝ}
    (ha : a ≤ alpha) (hy : y ≤ v) :
    (familyCount q alpha y : ℝ) =
      ∑ z ∈ rectangleZeros q a v,
        if alpha ≤ z.2.re ∧ |z.2.im| ≤ y then
          (analyticOrderNatAt z.1.LFunction z.2 : ℝ) else 0 := by
  simp only [familyCount, count, zeroValues_rectangle_filter _ ha hy, Nat.cast_sum,
    Finset.sum_filter, rectangleZeros, Finset.sum_sigma]
  simp only [Nat.cast_ite, Nat.cast_zero]

theorem familyCount_separated {q : ℕ} [NeZero q] {a alpha y v : ℝ}
    (ha : a ≤ alpha) (hy : y ≤ v) (f g : ℝ → ℝ) :
    f alpha * (g y * (familyCount q alpha y : ℝ)) =
      ∑ z ∈ rectangleZeros q a v,
        (Set.Iic z.2.re).indicator
          (fun x => (analyticOrderNatAt z.1.LFunction z.2 : ℝ) * f x) alpha *
        (Set.Ici |z.2.im|).indicator g y := by
  rw [familyCount_rectangle ha hy]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hα : alpha ≤ z.2.re <;> by_cases hγ : |z.2.im| ≤ y <;>
    simp [Set.indicator, hα, hγ]
  ring

theorem familyCount_integral_swap (q : ℕ) [NeZero q] {a b u v : ℝ}
    (hab : a ≤ b) (huv : u ≤ v) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume u v) :
    (∫ alpha in a..b, f alpha * ∫ y in u..v, g y * familyCount q alpha y) =
      ∫ y in u..v, g y * ∫ alpha in a..b, f alpha * familyCount q alpha y := by
  let F (z : (_chi : Character q) × ℂ) :=
    (Set.Iic z.2.re).indicator
      (fun x => (analyticOrderNatAt z.1.LFunction z.2 : ℝ) * f x)
  let G (z : (_chi : Character q) × ℂ) := (Set.Ici |z.2.im|).indicator g
  have hF (z : (_chi : Character q) × ℂ) (_hz : z ∈ rectangleZeros q a v) :
      IntervalIntegrable (F z) volume a b :=
    indicator_integrable (hf.const_mul _) measurableSet_Iic
  have hG (z : (_chi : Character q) × ℂ) (_hz : z ∈ rectangleZeros q a v) :
      IntervalIntegrable (G z) volume u v :=
    indicator_integrable hg measurableSet_Ici
  calc
    _ = ∫ alpha in a..b, ∫ y in u..v,
        ∑ z ∈ rectangleZeros q a v, F z alpha * G z y := by
      apply intervalIntegral.integral_congr
      intro alpha halpha
      rw [Set.uIcc_of_le hab] at halpha
      dsimp only
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le huv] at hy
      dsimp only
      exact familyCount_separated halpha.1 hy.2 f g
    _ = ∫ y in u..v, ∫ alpha in a..b,
        ∑ z ∈ rectangleZeros q a v, F z alpha * G z y :=
      finite_separated_swap _ F G hF hG
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le huv] at hy
      dsimp only
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro alpha halpha
      rw [Set.uIcc_of_le hab] at halpha
      dsimp only
      have h := familyCount_separated (q := q) halpha.1 hy.2 f g
      dsimp only [F, G]
      rw [← h]
      ring

theorem countIntegral_height_swap (q : ℕ) [NeZero q] {X a b u v p : ℝ}
    (hX : 0 < X) (hab : a ≤ b) (hu : 0 < u) (huv : u ≤ v) :
    (∫ alpha in a..b, betaKernel X alpha *
        ∫ y in u..v, heightKernel p y * familyCount q alpha y) =
      ∫ y in u..v, heightKernel p y * countIntegral q X y a b :=
  familyCount_integral_swap q hab huv
    ((betaKernel_continuous hX).intervalIntegrable a b) (heightKernel_integrable hu huv p)

theorem familyCount_inner_integrable (q : ℕ) [NeZero q] {a b u v : ℝ}
    (hab : a ≤ b) (huv : u ≤ v) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume u v) :
    IntervalIntegrable
      (fun alpha => f alpha * ∫ y in u..v, g y * familyCount q alpha y) volume a b := by
  let F (z : (_chi : Character q) × ℂ) :=
    (Set.Iic z.2.re).indicator
      (fun x => (analyticOrderNatAt z.1.LFunction z.2 : ℝ) * f x)
  let G (z : (_chi : Character q) × ℂ) := (Set.Ici |z.2.im|).indicator g
  have hF (z : (_chi : Character q) × ℂ) :
      IntervalIntegrable (F z) volume a b :=
    indicator_integrable (hf.const_mul _) measurableSet_Iic
  have hG (z : (_chi : Character q) × ℂ) :
      IntervalIntegrable (G z) volume u v :=
    indicator_integrable hg measurableSet_Ici
  have hi : IntervalIntegrable (fun alpha =>
      ∑ z ∈ rectangleZeros q a v, F z alpha * ∫ y in u..v, G z y) volume a b := by
    convert! IntervalIntegrable.sum (rectangleZeros q a v)
      (fun z _ => (hF z).mul_const (∫ y in u..v, G z y)) using 1
    ext alpha
    simp only [Finset.sum_apply]
  apply hi.congr_ae
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro alpha halpha
  rw [Set.uIoc_of_le hab] at halpha
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  calc
    _ = ∫ y in u..v, ∑ z ∈ rectangleZeros q a v, F z alpha * G z y := by
      rw [intervalIntegral.integral_finsetSum (fun z _ => (hG z).const_mul _)]
      simp only [intervalIntegral.integral_const_mul]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le huv] at hy
      exact (familyCount_separated halpha.1.le hy.2 f g).symm

theorem densityBand_integral_le_counts (q : ℕ) [NeZero q] {X a b u v p : ℝ}
    (hX : 1 ≤ X) (ha : 1 / 2 ≤ a) (hab : a ≤ b)
    (hu : 0 < u) (huv : u ≤ v) (hp : 0 ≤ p) :
    (∫ alpha in a..b, betaKernel X alpha * densityBand q alpha u v p) ≤
      v ^ (-p) * countIntegral q X v a b +
        ∫ y in u..v, heightKernel p y * countIntegral q X y a b := by
  have hx : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hb : IntervalIntegrable (betaKernel X) volume a b :=
    (betaKernel_continuous hx).intervalIntegrable a b
  have hg := heightKernel_integrable hu huv p
  have hfirst := (family_beta_integrable q v hx ha hab).const_mul (v ^ (-p))
  have hsecond := familyCount_inner_integrable q hab huv hb hg
  calc
    _ ≤ ∫ alpha in a..b,
        v ^ (-p) * (betaKernel X alpha * familyCount q alpha v) +
          betaKernel X alpha * ∫ y in u..v, heightKernel p y * familyCount q alpha y := by
      apply intervalIntegral.integral_mono_on hab
        (densityBand_beta_integrable q u v p hx ha hab) (hfirst.add hsecond)
      intro alpha _
      have h := mul_le_mul_of_nonneg_left (family_height_partialSummation q alpha hu huv hp)
        (mul_nonneg (Real.rpow_nonneg hx.le (alpha - 1)) (Real.log_nonneg hX))
      exact h.trans_eq (by unfold betaKernel; ring)
    _ = _ := by
      rw [intervalIntegral.integral_add hfirst hsecond, intervalIntegral.integral_const_mul,
        countIntegral_height_swap q hx hab hu huv]
      rfl

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation
