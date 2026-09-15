import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Finite partial summation, including all integrability obligations. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.SourceRoute.ThirdArc

def heightKernel (p y : ℝ) : ℝ := p * y ^ (-p - 1)

theorem heightKernel_integrable {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (p : ℝ) :
    IntervalIntegrable (heightKernel p) volume u v := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le huv]
  intro y hy
  exact (continuousAt_const.mul
    (Real.continuousAt_rpow_const y (-p - 1)
      (Or.inl (hu.trans_le hy.1).ne'))).continuousWithinAt

theorem integral_heightKernel {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (p : ℝ) :
    (∫ y in u..v, heightKernel p y) = u ^ (-p) - v ^ (-p) := by
  have h : (∫ y in u..v, heightKernel p y) = -v ^ (-p) - -u ^ (-p) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => -(x ^ (-p)))
    · intro y hy
      rw [Set.uIcc_of_le huv] at hy
      convert (Real.hasDerivAt_rpow_const
        (p := -p) (Or.inl (hu.trans_le hy.1).ne')).neg using 1
      · rfl
      · change p * y ^ (-p - 1) = -(-p * y ^ (-p - 1))
        ring
    · exact heightKernel_integrable hu huv p
  linarith

theorem indicator_integrable {u v : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume u v) {s : Set ℝ} (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) volume u v := by
  rw [intervalIntegrable_iff]
  exact hf.def'.indicator hs

theorem integral_height_tail {u r v : ℝ} (hu : 0 < u)
    (hur : u ≤ r) (hrv : r ≤ v) (p : ℝ) :
    (∫ y in u..v, (Set.Ioi r).indicator (heightKernel p) y) =
      r ^ (-p) - v ^ (-p) := by
  have hf := heightKernel_integrable hu (hur.trans hrv) p
  have hid : (Set.Ioi r).indicator (heightKernel p) =
      fun y => heightKernel p y - (Set.Iic r).indicator (heightKernel p) y := by
    funext y
    by_cases hy : y ≤ r
    · simp [Set.indicator, hy, not_lt.mpr hy]
    · simp [Set.indicator, hy, lt_of_not_ge hy]
  have hic : (∫ y in u..v, (Set.Iic r).indicator (heightKernel p) y) =
      ∫ y in u..r, heightKernel p y :=
    intervalIntegral.integral_indicator ⟨hur, hrv⟩
  rw [hid, intervalIntegral.integral_sub hf (indicator_integrable hf measurableSet_Iic),
    hic,
    integral_heightKernel hu (hur.trans hrv), integral_heightKernel hu hur]
  ring

def cumulative {ι : Type*} (s : Finset ι) (r w : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s.filter (fun i => r i ≤ y), w i

theorem cumulative_integrand {ι : Type*} (s : Finset ι) (r w : ι → ℝ)
    (f : ℝ → ℝ) (y : ℝ) :
    f y * cumulative s r w y =
      ∑ i ∈ s, w i * (Set.Ici (r i)).indicator f y := by
  simp only [cumulative, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hy : r i ≤ y <;> simp [Set.indicator, hy, mul_comm]

theorem cumulative_integrable {ι : Type*} (s : Finset ι) (r w : ι → ℝ)
    {f : ℝ → ℝ} {u v : ℝ} (hf : IntervalIntegrable f volume u v) :
    IntervalIntegrable (fun y => f y * cumulative s r w y) volume u v := by
  simp_rw [cumulative_integrand]
  convert! IntervalIntegrable.sum s (fun i _ =>
    (indicator_integrable hf (s := Set.Ici (r i)) measurableSet_Ici).const_mul (w i)) using 1
  ext y
  simp only [Finset.sum_apply]

theorem finite_height_partialSummation {ι : Type*} (s : Finset ι) (r w : ι → ℝ)
    {u v p : ℝ} (hu : 0 < u) (huv : u ≤ v) (hp : 0 ≤ p)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hr : ∀ i ∈ s, u ≤ r i ∧ r i ≤ v) :
    (∑ i ∈ s, w i * r i ^ (-p)) ≤
      v ^ (-p) * (∑ i ∈ s, w i) +
        ∫ y in u..v, heightKernel p y * cumulative s r w y := by
  have hf := heightKernel_integrable hu huv p
  have hi (i : ι) :
      IntervalIntegrable (fun y => w i *
        (Set.Ioi (r i)).indicator (heightKernel p) y) volume u v :=
    (indicator_integrable hf measurableSet_Ioi).const_mul _
  have heq :
      (∑ i ∈ s, w i * r i ^ (-p)) =
        v ^ (-p) * (∑ i ∈ s, w i) +
          ∫ y in u..v, ∑ i ∈ s,
            w i * (Set.Ioi (r i)).indicator (heightKernel p) y := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
    simp only [intervalIntegral.integral_const_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i his
    rw [integral_height_tail hu (hr i his).1 (hr i his).2]
    ring
  rw [heq]
  apply add_le_add le_rfl
  have his : IntervalIntegrable (fun y => ∑ i ∈ s,
      w i * (Set.Ioi (r i)).indicator (heightKernel p) y) volume u v := by
    convert! IntervalIntegrable.sum s (fun i _ => hi i) using 1
    ext y
    simp only [Finset.sum_apply]
  apply intervalIntegral.integral_mono_on huv his (cumulative_integrable s r w hf)
  intro y hy
  rw [cumulative_integrand]
  apply Finset.sum_le_sum
  intro i his
  apply mul_le_mul_of_nonneg_left _ (hw i his)
  have hk : 0 ≤ heightKernel p y :=
    mul_nonneg hp (Real.rpow_nonneg (hu.trans_le hy.1).le _)
  by_cases hlt : r i < y
  · simp [Set.indicator, hlt, hlt.le]
  · by_cases hle : r i ≤ y <;> simp [Set.indicator, hlt, hle, hk]

def betaKernel (X alpha : ℝ) : ℝ := X ^ (alpha - 1) * Real.log X

theorem betaKernel_continuous {X : ℝ} (hX : 0 < X) :
    Continuous (betaKernel X) := by
  unfold betaKernel
  have hX0 := hX.ne'
  fun_prop

theorem integral_betaKernel {X : ℝ} (hX : 0 < X) (a b : ℝ) :
    (∫ alpha in a..b, betaKernel X alpha) = X ^ (b - 1) - X ^ (a - 1) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro alpha _
    simpa only [betaKernel, id_eq, mul_one, one_mul, mul_comm] using
      ((hasDerivAt_id alpha).sub_const 1).const_rpow hX
  · exact (betaKernel_continuous hX).intervalIntegrable _ _

def upperMass {ι : Type*} (s : Finset ι) (b w : ι → ℝ) (alpha : ℝ) : ℝ :=
  ∑ i ∈ s.filter (fun i => alpha ≤ b i), w i

theorem upperMass_integrand {ι : Type*} (s : Finset ι) (b w : ι → ℝ)
    (f : ℝ → ℝ) (alpha : ℝ) :
    f alpha * upperMass s b w alpha =
      ∑ i ∈ s, w i * (Set.Iic (b i)).indicator f alpha := by
  simp only [upperMass, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : alpha ≤ b i <;> simp [Set.indicator, ha, mul_comm]

theorem upperMass_integrable {ι : Type*} (s : Finset ι) (b w : ι → ℝ)
    {f : ℝ → ℝ} {a c : ℝ} (hf : IntervalIntegrable f volume a c) :
    IntervalIntegrable (fun alpha => f alpha * upperMass s b w alpha) volume a c := by
  simp_rw [upperMass_integrand]
  convert! IntervalIntegrable.sum s (fun i _ =>
    (indicator_integrable hf (s := Set.Iic (b i)) measurableSet_Iic).const_mul (w i)) using 1
  ext alpha
  simp only [Finset.sum_apply]

theorem finite_beta_partialSummation {ι : Type*} (s : Finset ι) (b w : ι → ℝ)
    {X a c : ℝ} (hX : 0 < X) (hb : ∀ i ∈ s, a ≤ b i ∧ b i ≤ c) :
    (∑ i ∈ s, w i * X ^ (b i - 1)) =
      X ^ (a - 1) * (∑ i ∈ s, w i) +
        ∫ alpha in a..c, betaKernel X alpha * upperMass s b w alpha := by
  simp_rw [upperMass_integrand]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hic : (∫ alpha in a..c, (Set.Iic (b i)).indicator (betaKernel X) alpha) =
        ∫ alpha in a..b i, betaKernel X alpha :=
      intervalIntegral.integral_indicator (hb i hi)
    rw [hic, integral_betaKernel hX]
    ring
  · intro i _
    exact (indicator_integrable ((betaKernel_continuous hX).intervalIntegrable _ _)
      measurableSet_Iic).const_mul _

end LiuWang.Proof.SourceRoute.ThirdArc
