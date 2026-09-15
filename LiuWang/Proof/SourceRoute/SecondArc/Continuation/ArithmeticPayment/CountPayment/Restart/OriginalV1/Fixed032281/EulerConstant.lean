import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral.FiniteExpression

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

theorem log_correction_lower {t : ℝ} (ht : 0 ≤ t) :
    t / 2 + t / (2 * (1 + t)) - t ^ 2 / 12 + t ^ 2 / (12 * (1 + t) ^ 2) ≤
      Real.log (1 + t) := by
  let f : ℝ → ℝ := fun t => Real.log (1 + t) - t / 2 -
    t / (2 * (1 + t)) + t ^ 2 / 12 - t ^ 2 / (12 * (1 + t) ^ 2)
  have hd (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt f (x ^ 4 / (6 * (1 + x) ^ 3)) x := by
    have hxp : 0 < 1 + x := by linarith
    have h1 := ((hasDerivAt_id x).const_add 1)
    have h2 := (hasDerivAt_id x).div (h1.const_mul 2)
      (show 2 * (1 + x) ≠ 0 by positivity)
    have h3 := ((hasDerivAt_id x).pow 2).div ((h1.pow 2).const_mul 12)
      (show 12 * (1 + x) ^ 2 ≠ 0 by positivity)
    convert! (((((h1.log hxp.ne').sub ((hasDerivAt_id x).div_const 2)).sub h2).add
      (((hasDerivAt_id x).pow 2).div_const 12)).sub h3) using 1
    norm_num only [Pi.pow_apply, id_eq, Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one]
    field_simp
    ring
  have hm : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        have hx0 : 0 ≤ x := interior_subset hx
        rw [(hd x hx0).deriv]
        positivity)
  have h := hm (by simp) ht ht
  dsimp [f] at h
  norm_num at h
  linarith

def correctedEuler (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) -
    1 / (2 * (n + 1)) + 1 / (12 * (n + 1) ^ 2)

theorem correctedEuler_antitone : Antitone correctedEuler := by
  apply antitone_nat_of_succ_le
  intro n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hn2 : 0 < (n : ℝ) + 2 := by positivity
  have hl := log_correction_lower (t := 1 / ((n : ℝ) + 1)) (by positivity)
  have he : 1 + 1 / ((n : ℝ) + 1) = ((n : ℝ) + 2) / ((n : ℝ) + 1) := by field_simp; ring
  rw [he, Real.log_div hn2.ne' hn.ne'] at hl
  unfold correctedEuler
  rw [harmonic_succ]
  simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add,
    Nat.cast_one, Rat.cast_one]
  have hr : (1 / ((n : ℝ) + 1)) / 2 +
      (1 / ((n : ℝ) + 1)) / (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) -
      (1 / ((n : ℝ) + 1)) ^ 2 / 12 +
      (1 / ((n : ℝ) + 1)) ^ 2 / (12 * (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ 2) =
      1 / ((n : ℝ) + 2) + 1 / (2 * ((n : ℝ) + 1)) -
        1 / (2 * ((n : ℝ) + 2)) - 1 / (12 * ((n : ℝ) + 1) ^ 2) +
        1 / (12 * ((n : ℝ) + 2) ^ 2) := by field_simp; ring
  rw [hr] at hl
  convert (show (harmonic (n + 1) : ℝ) + 1 / ((n : ℝ) + 2) -
      Real.log ((n : ℝ) + 2) - 1 / (2 * ((n : ℝ) + 2)) +
      1 / (12 * ((n : ℝ) + 2) ^ 2) ≤
      (harmonic (n + 1) : ℝ) - Real.log ((n : ℝ) + 1) -
      1 / (2 * ((n : ℝ) + 1)) + 1 / (12 * ((n : ℝ) + 1) ^ 2) by linarith) using 1 <;>
    congr 1 <;> ring

theorem euler_le_correctedEuler (n : ℕ) :
    Real.eulerMascheroniConstant ≤ correctedEuler n := by
  have hs : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hs
  have hc : Tendsto correctedEuler atTop (𝓝 Real.eulerMascheroniConstant) := by
    have he := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
    have ht := (he.sub (hinv.const_mul (1 / 2 : ℝ))).add
      ((hinv.pow 2).const_mul (1 / 12 : ℝ))
    convert ht using 1
    · ext k
      unfold correctedEuler
      simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
      field_simp
    · simp
  exact correctedEuler_antitone.le_of_tendsto hc n

theorem euler_upper : Real.eulerMascheroniConstant ≤ 0.57721568 := by
  have hg := euler_le_correctedEuler 31
  have hl : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    norm_num
  norm_num [correctedEuler] at hg
  rw [hl] at hg
  linarith [Real.log_two_gt_d9]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
