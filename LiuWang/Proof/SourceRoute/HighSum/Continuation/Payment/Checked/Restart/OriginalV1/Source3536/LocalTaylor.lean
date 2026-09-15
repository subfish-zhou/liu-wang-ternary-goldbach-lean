import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Reduction
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.RationalExp
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Rat.Floor

set_option autoImplicit false
noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

def odeResidual (A u : ℝ) (Q : ℝ[X]) : ℝ[X] :=
  (X + C u) ^ 2 * Q.derivative - (C A - (X + C u) ^ 2) * Q

theorem ode_pointwise_upper (A : ℝ) {u : ℝ} (hu : 0 < u) (Q : ℝ[X])
    (hQ : Q.eval 0 = 1) (hres : ∀ t : ℝ, 0 ≤ t → 0 ≤ (odeResidual A u Q).eval t)
    {s : ℝ} (hs : u ≤ s) :
    Real.exp (phase A s) ≤ Real.exp (phase A u) * Q.eval (s - u) := by
  let g := fun x : ℝ => Q.eval (x - u) * Real.exp (-phase A x)
  let dg := fun x : ℝ =>
    Real.exp (-phase A x) / x ^ 2 * (odeResidual A u Q).eval (x - u)
  have hd (x : ℝ) (hx : x ∈ Set.Ici u) : HasDerivAt g (dg x) x := by
    have hx0 : x ≠ 0 := (hu.trans_le hx).ne'
    have hq := (Q.hasDerivAt (x - u)).comp x ((hasDerivAt_id x).sub_const u)
    have he := (((hasDerivAt_id x).neg.sub
      ((hasDerivAt_const x A).div (hasDerivAt_id x) hx0)).neg.exp)
    convert! hq.mul he using 1
    dsimp [dg, odeResidual, phase]
    simp only [eval_sub, eval_mul, eval_pow, eval_add, eval_X, eval_C]
    field_simp
    ring
  have hg : ContinuousOn g (Set.Ici u) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici u) hg
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => mul_nonneg (by positivity)
      (hres (x - u) (sub_nonneg.mpr (interior_subset hx))))
  have hh := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
  dsimp [g] at hh
  rw [sub_self, hQ, one_mul] at hh
  have ht := mul_le_mul_of_nonneg_right hh (Real.exp_pos (phase A s + phase A u)).le
  simp only [mul_assoc, ← Real.exp_add] at ht
  rw [show -phase A u + (phase A s + phase A u) = phase A s by ring,
    show -phase A s + (phase A s + phase A u) = phase A u by ring] at ht
  simpa only [mul_comm] using ht

theorem ode_integral_upper (A : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (R : ℝ[X]) (hR : R.derivative.eval 0 = 1)
    (hres : ∀ t : ℝ, 0 ≤ t → 0 ≤ (odeResidual A u R.derivative).eval t) :
    (∫ s in u..v, Real.exp (phase A s)) ≤
      Real.exp (phase A u) * (R.eval (v - u) - R.eval 0) := by
  have hd (s : ℝ) :
      HasDerivAt (fun s => R.eval (s - u)) (R.derivative.eval (s - u)) s := by
    convert! (R.hasDerivAt (s - u)).comp s ((hasDerivAt_id s).sub_const u) using 1
    simp
  have hi : IntervalIntegrable (fun s => R.derivative.eval (s - u)) volume u v := by
    apply Continuous.intervalIntegrable
    exact R.derivative.continuous.comp (continuous_id.sub continuous_const)
  have hh := intervalIntegral.integral_mono_on huv (exp_phase_integrable A hu huv)
    (hi.const_mul (Real.exp (phase A u)))
    (fun s hs => ode_pointwise_upper A hu R.derivative hR hres hs.1)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi, sub_self] at hh
  exact hh

def coefficient (A u : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => (A - u ^ 2) / u ^ 2
  | 2 => ((A - u ^ 2 - 2 * u) * coefficient A u 1 - 2 * u) / (2 * u ^ 2)
  | n + 3 =>
      ((A - u ^ 2 - 2 * u * (n + 2)) * coefficient A u (n + 2) -
        (2 * u + (n + 1)) * coefficient A u (n + 1) - coefficient A u n) /
          ((n + 3) * u ^ 2)

def upperPrimitive (A u : ℚ) : ℚ[X] :=
  (∑ k ∈ Finset.range 7, C (coefficient A u k / (k + 1)) * X ^ (k + 1)) +
    C (1 / 80000) * X ^ 8

def taylor12 (x : ℚ) : ℚ := ∑ k ∈ Finset.range 12, x ^ k / (k.factorial : ℚ)

def expUpper (x : ℚ) : ℚ :=
  1 / ((27182818283 / 10000000000 : ℚ) ^ ⌊x⌋₊ * taylor12 (x - ⌊x⌋₊))

theorem exp_upper {x : ℚ} (hx : 0 ≤ x) : Real.exp (-(x : ℝ)) ≤ (expUpper x : ℝ) := by
  have hdq : 0 ≤ x - (⌊x⌋₊ : ℚ) := sub_nonneg.mpr (Nat.floor_le hx)
  have hd : 0 ≤ (x : ℝ) - (⌊x⌋₊ : ℝ) := by exact_mod_cast hdq
  have ht := Real.sum_le_exp_of_nonneg hd 12
  have ht0 : 1 ≤ (taylor12 (x - ⌊x⌋₊) : ℝ) := by
    have h := Finset.single_le_sum (f := fun k : ℕ =>
      ((x : ℝ) - (⌊x⌋₊ : ℝ)) ^ k / (k.factorial : ℝ))
      (fun k _ => by positivity) (by decide : 0 ∈ Finset.range 12)
    simpa [taylor12] using h
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le ⌊x⌋₊
  rw [← Real.exp_nat_mul, mul_one] at hpow
  have hh := mul_le_mul hpow ht (by positivity) (Real.exp_pos _).le
  rw [← Real.exp_add, add_sub_cancel] at hh
  have htcast : (taylor12 (x - ⌊x⌋₊) : ℝ) =
      ∑ k ∈ Finset.range 12, ((x : ℝ) - (⌊x⌋₊ : ℝ)) ^ k / (k.factorial : ℝ) := by
    simp [taylor12]
  rw [← htcast] at hh
  unfold expUpper
  push_cast
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le
    (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 27182818283 / 10000000000) _)
      (lt_of_lt_of_le zero_lt_one ht0))
  convert hh using 1
  norm_num

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
