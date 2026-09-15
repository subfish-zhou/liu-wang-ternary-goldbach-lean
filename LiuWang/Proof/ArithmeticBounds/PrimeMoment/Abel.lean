import LiuWang.Proof.ArithmeticBounds.PrimeMoment.Mangoldt

/-! 双端点 Abel 估计：减去积分时消费 Λ 倒数和的下界。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.PrimeMoment

open scoped BigOperators
open Finset Real MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

theorem continuousOn_inv_Icc {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc a b) :=
  continuousOn_id.inv₀ (fun _ ht => ne_of_gt (ha.trans_le ht.1))

theorem mangoldt_log_abel {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ d ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, log d * (Λ d / d)) =
      log b * mangoldtReciprocal b - log a * mangoldtReciprocal a -
        ∫ t in a..b, t⁻¹ * mangoldtReciprocal t := by
  have hder : IntegrableOn (deriv log) (Set.Icc a b) := by
    simpa only [Real.deriv_log'] using
      (continuousOn_inv_Icc (show 0 < a by linarith) (b := b)).integrableOn_Icc
        (μ := volume)
  simpa only [mangoldtReciprocal, Real.deriv_log,
    intervalIntegral.integral_of_le hab] using
    sum_mul_eq_sub_sub_integral_mul (fun d : ℕ => Λ d / d)
      (f := log) (show 0 ≤ a by linarith) hab
      (fun t ht => differentiableAt_log (by linarith [ht.1])) hder

theorem integral_mangoldt_log_lower {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (log b ^ 2 / 2 - 2 * log b) - (log a ^ 2 / 2 - 2 * log a) ≤
      ∫ t in a..b, t⁻¹ * mangoldtReciprocal t := by
  have ha0 : 0 < a := by linarith
  have hlog : ContinuousOn log (Set.Icc a b) :=
    fun t ht => (continuousAt_log (ne_of_gt (ha0.trans_le ht.1))).continuousWithinAt
  have hinv := continuousOn_inv_Icc (b := b) ha0
  have hlo : IntervalIntegrable (fun t : ℝ => (log t - 2) / t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact ((hlog.sub continuousOn_const).mul hinv).integrableOn_Icc
  have hhi : IntervalIntegrable
      (fun t : ℝ => t⁻¹ * mangoldtReciprocal t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact integrableOn_mul_sum_Icc (fun d : ℕ => Λ d / d) ha0.le hinv.integrableOn_Icc
  have hint : (∫ t in a..b, (log t - 2) / t) =
      (log b ^ 2 / 2 - 2 * log b) - (log a ^ 2 / 2 - 2 * log a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => log t ^ 2 / 2 - 2 * log t) _ hlo
    intro t ht
    have ht0 : t ≠ 0 := by
      rw [Set.uIcc_of_le hab] at ht
      linarith [ht.1]
    convert (((hasDerivAt_log ht0).pow 2).div_const 2).sub
      ((hasDerivAt_log ht0).const_mul 2) using 1
    · funext x
      simp only [Pi.sub_apply, Pi.pow_apply]
    · ring
  rw [← hint]
  apply intervalIntegral.integral_mono_on hab hlo hhi
  intro t ht
  have ht1 := ha.trans ht.1
  have ht0 : 0 ≤ t := by linarith
  have := mul_le_mul_of_nonneg_left (mangoldtReciprocal_bounds ht1).1
    (inv_nonneg.mpr ht0)
  simpa only [div_eq_mul_inv, mul_comm] using this

theorem mangoldt_log_interval_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ d ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, log d * (Λ d / d)) ≤
      (log b ^ 2 - log a ^ 2) / 2 + 8 * log b := by
  rw [mangoldt_log_abel ha hab]
  have hu := mul_le_mul_of_nonneg_left (mangoldtReciprocal_bounds (ha.trans hab)).2
    (log_nonneg (ha.trans hab))
  have hl := mul_le_mul_of_nonneg_left (mangoldtReciprocal_bounds ha).1
    (log_nonneg ha)
  have hi := integral_mangoldt_log_lower ha hab
  nlinarith

theorem prime_log_sq_interval_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, log p ^ 2 / p) ≤
      (log b ^ 2 - log a ^ 2) / 2 + 8 * log b := by
  calc
    _ = ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, log p * (Λ p / p) := by
      apply sum_congr rfl
      intro p hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2]
      ring
    _ ≤ ∑ d ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, log d * (Λ d / d) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro d _ _
      exact mul_nonneg (log_natCast_nonneg d) (by positivity)
    _ ≤ _ := mangoldt_log_interval_le ha hab

end LiuWang.Proof.ArithmeticBounds.PrimeMoment
