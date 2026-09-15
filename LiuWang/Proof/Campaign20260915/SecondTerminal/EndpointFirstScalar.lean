import LiuWang.Proof.Campaign20260915.SecondTerminal.EndpointDensitySplit

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

def endpointFirstScalar (L : ℝ) : ℝ :=
  16 * 4.4772 * L * (254231 / upperLog L + 17102) * upperLog L ^ (6 : ℕ) *
    Real.exp (-(13 / 30 : ℝ) * upperLog L -
      0.478 * (L + Real.log 0.001) / upperLog L)

theorem endpointFirstScalar_le_base {L : ℝ} (hL : 3100 ≤ L) :
    endpointFirstScalar L ≤ endpointFirstScalar 3100 := by
  let t := L / 3100
  let y := upperLog 3100
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 < t := by linarith
  have hLt : L = 3100 * t := by dsimp [t]; ring
  have hd := base_log_domain
  have hy20 : 20 ≤ y := by dsimp [y]; linarith [hd.1, hd.2.2]
  have hy60 : y ≤ 60 := hd.2.1
  have hy0 : 0 < y := by linarith
  have hz := shifted_height_bounds ht hy20 (k := (7 : ℝ)) (by norm_num) le_rfl
  have hH := window_H_scaling hL
  have hphase := shifted_phase_gain hH.1 ht hH.2 hy20 hy60 (k := (7 : ℝ))
    (by norm_num) le_rfl
  have hscale : upperLog L = y + 7 * Real.log t := (source_log_scaling hL).2
  have he : Real.exp (-(13 / 30 : ℝ) * upperLog L -
      0.478 * (L + Real.log 0.001) / upperLog L) ≤
      Real.exp (-10.516 * Real.log t) *
        Real.exp (-(13 / 30 : ℝ) * y -
          0.478 * ((3100 : ℝ) + Real.log 0.001) / y) := by
    rw [hscale, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [div_eq_mul_inv] at hphase ⊢
    nlinarith only [hphase, hz.2.1]
  have hpoly : upperLog L ^ (6 : ℕ) ≤ t ^ (6 : ℕ) * y ^ (6 : ℕ) := by
    rw [hscale, ← mul_pow]
    exact pow_le_pow_left₀ hz.1.le hz.2.2 _
  have hcoef : L * (254231 / upperLog L + 17102) ≤
      (3100 * (254231 / y + 17102)) * t := by
    have hr : 254231 / upperLog L ≤ 254231 / y := by
      rw [hscale]
      exact div_le_div_of_nonneg_left (by norm_num) hy0 hz.2.1
    have hm := mul_le_mul_of_nonneg_left (add_le_add_right hr 17102)
      (show 0 ≤ L by linarith)
    calc
      _ ≤ L * (254231 / y + 17102) := by simpa only [add_comm] using hm
      _ = _ := by rw [hLt]; ring
  have hm := mul_le_mul (mul_le_mul hcoef hpoly (by positivity) (by positivity))
    he (Real.exp_pos _).le (by positivity)
  have habs : t ^ (7 : ℕ) * Real.exp (-10.516 * Real.log t) ≤ 1 := by
    rw [← Real.exp_log ht0, ← Real.exp_nat_mul, Real.exp_log ht0, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have hl := Real.log_nonneg ht
    norm_num only [Nat.cast_ofNat]
    linarith
  have hp := mul_le_mul_of_nonneg_left habs
    (show 0 ≤ (3100 * (254231 / y + 17102)) * y ^ (6 : ℕ) *
      Real.exp (-(13 / 30 : ℝ) * y -
        0.478 * ((3100 : ℝ) + Real.log 0.001) / y) by positivity)
  unfold endpointFirstScalar
  change _ ≤ 16 * 4.4772 * 3100 * (254231 / y + 17102) * y ^ (6 : ℕ) *
    Real.exp (-(13 / 30 : ℝ) * y - 0.478 * ((3100 : ℝ) + Real.log 0.001) / y)
  nlinarith only [hm, hp]

theorem endpoint_first_base_phase :
    -(13 / 30 : ℝ) * upperLog 3100 -
      0.478 * ((3100 : ℝ) + Real.log 0.001) / upperLog 3100 ≤ -50.6358 := by
  have hlo := upperLog_base_lower
  have hup := Fixed032281.upper_endpoint
  have hH := Fixed032281.window_H_lower
  have hy0 : 0 < upperLog 3100 := by linarith
  have hr : 0.478 * (3093.092244719 : ℝ) / 59.721417 ≤
      0.478 * ((3100 : ℝ) + Real.log 0.001) / upperLog 3100 := by
    apply (div_le_div_of_nonneg_left (by norm_num) hy0 hup).trans
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hH (by norm_num)) hy0.le
  norm_num at hr
  linarith

theorem exp_endpoint_first_base :
    Real.exp (-50.6358 : ℝ) ≤ 0.00000000000000000000010213 := by
  have he := Real.sum_le_exp_of_nonneg (x := (0.6358 : ℝ)) (by norm_num) 12
  have h1 : (2.718281828 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := mul_le_mul (pow_le_pow_left₀ (by norm_num) h1 50) he
    (by positivity) (by positivity)
  rw [← Real.exp_nat_mul, ← Real.exp_add] at hp
  norm_num [Finset.sum_range_succ] at hp
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith only [hp]

theorem endpointFirstScalar_fixed :
    endpointFirstScalar 3100 ≤ 0.02198 := by
  have hlo := upperLog_base_lower
  have hy0 : 0 < upperLog 3100 := by linarith
  have hc := add_le_add_right
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 254231)
      (by norm_num : (0 : ℝ) < 59.7214) hlo) 17102
  have hup := pow_le_pow_left₀ hy0.le Fixed032281.upper_endpoint 6
  have he := (Real.exp_le_exp.mpr endpoint_first_base_phase).trans exp_endpoint_first_base
  have hh := mul_le_mul (mul_le_mul hc hup (by positivity) (by norm_num))
    he (Real.exp_pos _).le (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hh
    (by norm_num : (0 : ℝ) ≤ 16 * 4.4772 * 3100)
  unfold endpointFirstScalar
  norm_num at hm ⊢
  nlinarith only [hm]

theorem endpointFirstScalar_payment (L : ℝ) (hL : 3100 ≤ L) :
    endpointFirstScalar L ≤ 0.02198 :=
  (endpointFirstScalar_le_base hL).trans endpointFirstScalar_fixed

#print axioms endpointFirstScalar_payment

end LiuWang.Proof.Campaign20260915.SecondTerminal
