import LiuWang.Proof.SourceRoute.SecondArc.HeightAbel

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc

def alphaKernel (x alpha : ℝ) : ℝ := x ^ (alpha - 1) * Real.log x

theorem continuous_alphaKernel {x : ℝ} (hx : 0 < x) :
    Continuous (alphaKernel x) := by
  have hx0 : x ≠ 0 := hx.ne'
  unfold alphaKernel
  fun_prop

theorem integral_alphaKernel {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    (∫ alpha in a..b, alphaKernel x alpha) = x ^ (b - 1) - x ^ (a - 1) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro alpha _
    have h := ((hasDerivAt_id alpha).sub_const 1).const_rpow hx
    simpa only [alphaKernel, id_eq, mul_one, mul_comm, one_mul] using h
  · exact (continuous_alphaKernel hx).intervalIntegrable _ _

theorem alpha_indicator_integrable {x : ℝ} (hx : 0 < x) (a b beta : ℝ) :
    IntervalIntegrable ((Set.Iic beta).indicator (alphaKernel x)) volume a b := by
  rw [intervalIntegrable_iff]
  exact ((continuous_alphaKernel hx).intervalIntegrable a b).def'.indicator measurableSet_Iic

theorem alpha_indicator_integral {x a b beta : ℝ} (hx : 0 < x)
    (ha : a ≤ beta) (hb : beta ≤ b) :
    (∫ alpha in a..b, (Set.Iic beta).indicator (alphaKernel x) alpha) =
      x ^ (beta - 1) - x ^ (a - 1) := by
  calc
    _ = ∫ alpha in a..beta, alphaKernel x alpha :=
      intervalIntegral.integral_indicator ⟨ha, hb⟩
    _ = _ := integral_alphaKernel hx a beta

def bandMass (q : ℕ) [NeZero q] (alpha u v : ℝ) : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ bandValues chi alpha u v,
    (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|

theorem bandMass_alpha_integrand {q : ℕ} [NeZero q] {a alpha : ℝ}
    (ha : a ≤ alpha) (x u v : ℝ) :
    alphaKernel x alpha * bandMass q alpha u v =
      ∑ chi : Character q, ∑ rho ∈ bandValues chi a u v,
        ((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) *
          (Set.Iic rho.re).indicator (alphaKernel x) alpha := by
  have hs (chi : Character q) :
      bandValues chi alpha u v =
        (bandValues chi a u v).filter (fun rho => alpha ≤ rho.re) := by
    ext rho
    simp only [Finset.mem_filter, mem_bandValues]
    constructor
    · rintro ⟨hz, hs, hb, hh⟩
      exact ⟨⟨hz, hs, ha.trans hb, hh⟩, hb⟩
    · rintro ⟨⟨hz, hs, _, hh⟩, hb⟩
      exact ⟨hz, hs, hb, hh⟩
  simp only [bandMass, hs, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hb : alpha ≤ rho.re <;> simp [Set.indicator, hb, mul_comm]

theorem bandMass_alpha_integrable {q : ℕ} [NeZero q] {x a b : ℝ}
    (hx : 0 < x) (hab : a ≤ b) (u v : ℝ) :
    IntervalIntegrable (fun alpha => alphaKernel x alpha * bandMass q alpha u v)
      volume a b := by
  have hf : IntervalIntegrable (fun alpha =>
      ∑ chi : Character q, ∑ rho ∈ bandValues chi a u v,
        ((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) *
          (Set.Iic rho.re).indicator (alphaKernel x) alpha) volume a b := by
    have hc (chi : Character q) : IntervalIntegrable (fun alpha =>
        ∑ rho ∈ bandValues chi a u v,
          ((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) *
            (Set.Iic rho.re).indicator (alphaKernel x) alpha) volume a b := by
      convert! IntervalIntegrable.sum (bandValues chi a u v)
        (fun rho _ => (alpha_indicator_integrable hx a b rho.re).const_mul
          ((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|)) using 1
      ext alpha
      simp only [Finset.sum_apply]
    convert! IntervalIntegrable.sum (Finset.univ : Finset (Character q))
      (fun chi _ => hc chi) using 1
    ext alpha
    simp only [Finset.sum_apply]
  apply hf.congr_ae
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro alpha ha
  rw [Set.uIoc_of_le hab] at ha
  exact (bandMass_alpha_integrand ha.1.le x u v).symm

/-- The real-part partial summation used in (5.3), with the original window base. -/
theorem band_weight_alpha_identity {q : ℕ} [NeZero q] {x a : ℝ}
    (hx : 0 < x) (ha : a ≤ 1) (u v : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi a u v,
      ((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) *
        x ^ (rho.re - 1)) =
      x ^ (a - 1) * bandMass q a u v +
        ∫ alpha in a..1, alphaKernel x alpha * bandMass q alpha u v := by
  have he : (∫ alpha in a..1, alphaKernel x alpha * bandMass q alpha u v) =
      ∑ chi : Character q, ∑ rho ∈ bandValues chi a u v,
        ((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) *
          (x ^ (rho.re - 1) - x ^ (a - 1)) := by
    calc
      _ = ∫ alpha in a..1, ∑ chi : Character q, ∑ rho ∈ bandValues chi a u v,
          ((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) *
            (Set.Iic rho.re).indicator (alphaKernel x) alpha := by
        apply intervalIntegral.integral_congr
        intro alpha ha'
        rw [Set.uIcc_of_le ha] at ha'
        exact bandMass_alpha_integrand ha'.1 x u v
      _ = _ := by
        have hc (chi : Character q) : IntervalIntegrable (fun alpha =>
            ∑ rho ∈ bandValues chi a u v,
              ((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) *
                (Set.Iic rho.re).indicator (alphaKernel x) alpha) volume a 1 := by
          convert! IntervalIntegrable.sum (bandValues chi a u v)
            (fun rho _ => (alpha_indicator_integrable hx a 1 rho.re).const_mul
              ((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|)) using 1
          ext alpha
          simp only [Finset.sum_apply]
        rw [intervalIntegral.integral_finsetSum (fun chi _ => hc chi)]
        apply Finset.sum_congr rfl
        intro chi _
        rw [intervalIntegral.integral_finsetSum
          (fun rho _ => (alpha_indicator_integrable hx a 1 rho.re).const_mul _)]
        apply Finset.sum_congr rfl
        intro rho hr
        rw [intervalIntegral.integral_const_mul,
          alpha_indicator_integral hx (mem_bandValues.mp hr).2.2.1
            (mem_bandValues.mp hr).2.1.2.1.le]
  rw [he]
  simp only [bandMass, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro rho _
  ring

theorem band_weight_alpha_split {q : ℕ} [NeZero q] {x a b : ℝ}
    (hx : 0 < x) (hab : a ≤ b) (hb : b ≤ 1) (u v : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ bandValues chi a u v,
      ((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) *
        x ^ (rho.re - 1)) =
      x ^ (a - 1) * bandMass q a u v +
        (∫ alpha in a..b, alphaKernel x alpha * bandMass q alpha u v) +
        ∫ alpha in b..1, alphaKernel x alpha * bandMass q alpha u v := by
  rw [band_weight_alpha_identity hx (hab.trans hb) u v,
    ← intervalIntegral.integral_add_adjacent_intervals
      (bandMass_alpha_integrable hx hab u v) (bandMass_alpha_integrable hx hb u v)]
  ring

end LiuWang.Proof.SourceRoute.SecondArc
