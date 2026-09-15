import LiuWang.Proof.SourceRoute.HighSum.HeightIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual finite-count Fubini identity, main paper (2.22) -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum

theorem zeroValues_rectangle_filter {q : ℕ} [NeZero q] (chi : Character q)
    {a alpha y T : ℝ} (ha : a ≤ alpha) (hyT : y ≤ T) :
    zeroValues chi alpha y =
      (zeroValues chi a T).filter (fun rho => alpha ≤ rho.re ∧ |rho.im| ≤ y) := by
  ext rho
  simp only [Finset.mem_filter, mem_zeroValues]
  constructor
  · rintro ⟨hz, ⟨h0, h1, hy⟩, hb⟩
    exact ⟨⟨hz, ⟨h0, h1, hy.trans hyT⟩, ha.trans hb⟩, hb, hy⟩
  · rintro ⟨⟨hz, ⟨h0, h1, _⟩, _⟩, hb, hy⟩
    exact ⟨hz, ⟨h0, h1, hy⟩, hb⟩

theorem count_rectangle_integrand (N : ℕ) {q : ℕ} [NeZero q] (chi : Character q)
    {a alpha y T : ℝ} (ha : a ≤ alpha) (hyT : y ≤ T) :
    layerKernel N alpha * heightKernel y * (count chi alpha y : ℝ) =
      ∑ rho ∈ zeroValues chi a T, (analyticOrderNatAt chi.LFunction rho : ℝ) *
        ((Set.Iic rho.re).indicator (layerKernel N) alpha *
          (Set.Ici |rho.im|).indicator heightKernel y) := by
  rw [count, zeroValues_rectangle_filter chi ha hyT, Nat.cast_sum]
  simp only [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hb : alpha ≤ rho.re <;> by_cases hy : |rho.im| ≤ y <;>
    simp [Set.mem_Iic, Set.mem_Ici, hb, hy, mul_comm]

theorem count_rectangle_integrable {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    IntegrableOn (fun z : ℝ × ℝ =>
      layerKernel N z.1 * heightKernel z.2 * (count chi z.1 z.2 : ℝ))
      (Set.uIoc (19 / 20 : ℝ) 1 ×ˢ Set.uIoc u T) := by
  have atom (rho : ℂ) :
      IntegrableOn (fun z : ℝ × ℝ =>
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          ((Set.Iic rho.re).indicator (layerKernel N) z.1 *
            (Set.Ici |rho.im|).indicator heightKernel z.2))
        (Set.uIoc (19 / 20 : ℝ) 1 ×ˢ Set.uIoc u T) := by
    have h := ((indicator_layer_integrable hN rho.re).def'.mul_prod
      (height_indicator_integrable hu huT |rho.im|).def').const_mul
        (analyticOrderNatAt chi.LFunction rho : ℝ)
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  have hs : IntegrableOn (fun z : ℝ × ℝ =>
      ∑ rho ∈ zeroValues chi (19 / 20) T,
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          ((Set.Iic rho.re).indicator (layerKernel N) z.1 *
            (Set.Ici |rho.im|).indicator heightKernel z.2))
      (Set.uIoc (19 / 20 : ℝ) 1 ×ˢ Set.uIoc u T) := by
    exact integrable_finsetSum _ (fun rho _ => atom rho)
  apply hs.congr_fun _ (measurableSet_uIoc.prod measurableSet_uIoc)
  intro z hz
  rw [Set.mem_prod, Set.uIoc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1),
    Set.uIoc_of_le huT] at hz
  exact (count_rectangle_integrand N chi hz.1.1.le hz.2.2).symm

theorem family_rectangle_integrable {N q : ℕ} [NeZero q] (hN : 0 < N)
    {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    IntegrableOn (fun z : ℝ × ℝ =>
      layerKernel N z.1 * heightKernel z.2 * (familyCount q z.1 z.2 : ℝ))
      (Set.uIoc (19 / 20 : ℝ) 1 ×ˢ Set.uIoc u T) := by
  simp only [familyCount, Nat.cast_sum, Finset.mul_sum]
  exact integrable_finsetSum _ (fun chi _ => count_rectangle_integrable hN chi hu huT)

theorem family_height_alpha_swap {N q : ℕ} [NeZero q] (hN : 0 < N)
    {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    (∫ alpha in (19 / 20 : ℝ)..1, layerKernel N alpha *
      ∫ y in u..T, heightKernel y * (familyCount q alpha y : ℝ)) =
    ∫ y in u..T, heightKernel y *
      ∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha y : ℝ) := by
  have h := intervalIntegral_intervalIntegral_swap
    (F := fun alpha y =>
      layerKernel N alpha * heightKernel y * (familyCount q alpha y : ℝ))
    (family_rectangle_integrable (q := q) hN hu huT)
  calc
    _ = ∫ alpha in (19 / 20 : ℝ)..1, ∫ y in u..T,
        layerKernel N alpha * heightKernel y * (familyCount q alpha y : ℝ) := by
      simp only [mul_assoc, intervalIntegral.integral_const_mul]
    _ = _ := h
    _ = _ := by
      simp only [mul_assoc, mul_left_comm (layerKernel N _) (heightKernel _),
        intervalIntegral.integral_const_mul]

theorem family_height_alpha_integrable {N q : ℕ} [NeZero q] (hN : 0 < N)
    {u T : ℝ} (hu : 0 < u) (huT : u ≤ T) :
    IntervalIntegrable (fun alpha => layerKernel N alpha *
      ∫ y in u..T, heightKernel y * (familyCount q alpha y : ℝ))
      volume (19 / 20) 1 := by
  have h := family_rectangle_integrable (q := q) hN hu huT
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  have hi := h.integral_prod_left
  rw [intervalIntegrable_iff]
  simpa only [IntegrableOn, Set.uIoc_of_le huT, intervalIntegral.integral_of_le huT,
    mul_assoc, integral_const_mul] using hi

theorem count_alpha_integrable {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) (y : ℝ) :
    IntervalIntegrable (fun alpha =>
      layerKernel N alpha * (count chi alpha y : ℝ)) volume (19 / 20) 1 := by
  have hs : IntervalIntegrable (fun alpha =>
      ∑ rho ∈ zeroValues chi (19 / 20) y,
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          (Set.Iic rho.re).indicator (layerKernel N) alpha) volume (19 / 20) 1 := by
    convert! IntervalIntegrable.sum (zeroValues chi (19 / 20) y) (fun rho _ =>
      (indicator_layer_integrable hN rho.re).const_mul
        (analyticOrderNatAt chi.LFunction rho : ℝ)) using 1
    ext alpha
    simp only [Finset.sum_apply]
  apply hs.congr
  intro alpha ha
  rw [Set.uIoc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)] at ha
  change (∑ rho ∈ zeroValues chi (19 / 20) y,
    (analyticOrderNatAt chi.LFunction rho : ℝ) *
      (Set.Iic rho.re).indicator (layerKernel N) alpha) =
        layerKernel N alpha * (DirichletZeroCount.count chi alpha y : ℝ)
  rw [DirichletZeroCount.count, zeroValues_rectangle_filter chi ha.1.le le_rfl,
    Nat.cast_sum]
  simp only [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hy := (mem_zeroValues.mp hrho).2.1.2.2
  by_cases hb : alpha ≤ rho.re <;> simp [Set.mem_Iic, hb, hy, mul_comm]

theorem family_alpha_integrable {N q : ℕ} [NeZero q] (hN : 0 < N) (y : ℝ) :
    IntervalIntegrable (fun alpha =>
      layerKernel N alpha * (familyCount q alpha y : ℝ)) volume (19 / 20) 1 := by
  simp only [familyCount, Nat.cast_sum, Finset.mul_sum]
  convert! IntervalIntegrable.sum (Finset.univ : Finset (Character q))
    (fun chi _ => count_alpha_integrable hN chi y) using 1
  ext alpha
  simp only [Finset.sum_apply]

end LiuWang.Proof.SourceRoute.HighSum
