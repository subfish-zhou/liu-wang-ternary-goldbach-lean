import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.ScalarReduction

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral

def expPrimitive (s b : ℝ) : ℕ → ℝ → ℝ
  | 0, y => if s = 0 then Real.exp b * y else Real.exp (s * y + b) / s
  | n + 1, y => if s = 0 then Real.exp b * y ^ (n + 2) / (n + 2) else
      (y ^ (n + 1) * Real.exp (s * y + b) - (n + 1) * expPrimitive s b n y) / s

theorem expPrimitive_zero (n : ℕ) (b y : ℝ) :
    expPrimitive 0 b n y = Real.exp b * y ^ (n + 1) / (n + 1) := by
  cases n <;> simp [expPrimitive, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]

theorem expPrimitive_hasDerivAt (n : ℕ) (s b y : ℝ) :
    HasDerivAt (expPrimitive s b n) (y ^ n * Real.exp (s * y + b)) y := by
  by_cases hs : s = 0
  · subst s
    have he : expPrimitive 0 b n =
        fun y : ℝ => Real.exp b * y ^ (n + 1) / (n + 1) :=
      funext (expPrimitive_zero n b)
    rw [he]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    convert! ((((hasDerivAt_id y).pow (n + 1)).const_mul (Real.exp b)).div_const
      ((n : ℝ) + 1)) using 1
    simp [Nat.cast_add, Nat.cast_one]
    field_simp
  · induction n with
    | zero =>
      have he : expPrimitive s b 0 = fun y => Real.exp (s * y + b) / s := by
        funext y
        simp [expPrimitive, hs]
      rw [he]
      convert! ((((hasDerivAt_id y).const_mul s).add_const b).exp.div_const s) using 1
      simp [hs]
    | succ n ih =>
      have he : expPrimitive s b (n + 1) = fun y =>
          (y ^ (n + 1) * Real.exp (s * y + b) - (n + 1) * expPrimitive s b n y) / s := by
        funext y
        simp [expPrimitive, hs]
      rw [he]
      convert! (((((hasDerivAt_id y).pow (n + 1)).mul
        (((hasDerivAt_id y).const_mul s).add_const b).exp).sub
          (ih.const_mul ((n : ℝ) + 1))).div_const s) using 1
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one, id_eq, Pi.pow_apply]
      field_simp
      ring

def expMoment (n : ℕ) (s b u v : ℝ) : ℝ :=
  expPrimitive s b n v - expPrimitive s b n u

theorem integral_power_exp (n : ℕ) (s b u v : ℝ) :
    (∫ y in u..v, y ^ n * Real.exp (s * y + b)) = expMoment n s b u v := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => expPrimitive_hasDerivAt n s b y)
    ((by fun_prop : Continuous (fun y : ℝ => y ^ n * Real.exp (s * y + b))).intervalIntegrable u v)

theorem expMoment_zero (n : ℕ) (b u v : ℝ) :
    expMoment n 0 b u v = Real.exp b * (v ^ (n + 1) - u ^ (n + 1)) / (n + 1) := by
  unfold expMoment
  rw [expPrimitive_zero, expPrimitive_zero]
  ring

theorem expMoment_nonnegative (n : ℕ) {s b u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    0 ≤ expMoment n s b u v := by
  rw [← integral_power_exp]
  apply intervalIntegral.integral_nonneg huv
  intro y hy
  have hy0 := hu.trans hy.1
  positivity

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral
