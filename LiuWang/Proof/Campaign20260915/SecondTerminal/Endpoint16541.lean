import LiuWang.Proof.Campaign20260915.SecondTerminal.Endpoint14000
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.ConcretePartition

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

def endpointSecondScalar (L : ℝ) : ℝ :=
  16 * 16541 * sourceNu (L ^ (3 : ℕ)) * L * upperLog L ^ (6 : ℕ) *
    Real.exp (-upperLog L / 2 - 0.478 * (L + Real.log 0.001) / upperLog L)

theorem endpointSecondScalar_le_base {L : ℝ} (hL : 3100 ≤ L) :
    endpointSecondScalar L ≤ endpointSecondScalar 3100 := by
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
  have hnu := sourceNu_linear_scaling hL
  have hnu0 := hnu.1
  have hH := window_H_scaling hL
  have hphase := shifted_phase_gain hH.1 ht hH.2 hy20 hy60 (k := (7 : ℝ))
    (by norm_num) le_rfl
  have hscale : upperLog L = y + 7 * Real.log t := (source_log_scaling hL).2
  have he : Real.exp (-upperLog L / 2 - 0.478 * (L + Real.log 0.001) / upperLog L) ≤
      Real.exp (-10.516 * Real.log t) *
        Real.exp (-y / 2 - 0.478 * ((3100 : ℝ) + Real.log 0.001) / y) := by
    rw [hscale, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [div_eq_mul_inv] at hphase ⊢
    nlinarith only [hphase, hz.2.1]
  have hpoly : upperLog L ^ (6 : ℕ) ≤ t ^ (6 : ℕ) * y ^ (6 : ℕ) := by
    rw [hscale, ← mul_pow]
    exact pow_le_pow_left₀ hz.1.le hz.2.2 _
  have hcoef : sourceNu (L ^ (3 : ℕ)) * L ≤
      (sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) * t ^ (2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hnu.2 (show 0 ≤ L by linarith)
    calc
      _ ≤ (t * sourceNu ((3100 : ℝ) ^ (3 : ℕ))) * L := h
      _ = _ := by rw [hLt]; ring
  have hm := mul_le_mul (mul_le_mul hcoef hpoly (by positivity) (by positivity))
    he (Real.exp_pos _).le (by positivity)
  have habs : t ^ (8 : ℕ) * Real.exp (-10.516 * Real.log t) ≤ 1 := by
    rw [← Real.exp_log ht0, ← Real.exp_nat_mul, Real.exp_log ht0, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have hl := Real.log_nonneg ht
    norm_num only [Nat.cast_ofNat]
    linarith
  have hp := mul_le_mul_of_nonneg_left habs
    (show 0 ≤ (sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) * y ^ (6 : ℕ) *
      Real.exp (-y / 2 - 0.478 * ((3100 : ℝ) + Real.log 0.001) / y) by positivity)
  unfold endpointSecondScalar
  change _ ≤ 16 * 16541 * sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100 * y ^ (6 : ℕ) *
    Real.exp (-y / 2 - 0.478 * ((3100 : ℝ) + Real.log 0.001) / y)
  nlinarith only [hm, hp]

theorem upperLog_base_lower : (59.7214 : ℝ) ≤ upperLog 3100 := by
  have hpi : (3.4473 : ℝ) ≤ Real.log (10 * Real.pi) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    have he := Real.exp_bound' (x := (3.4473 / 4 : ℝ)) (by norm_num) (by norm_num)
      (n := 16) (by norm_num)
    have hp := pow_le_pow_left₀ (Real.exp_pos _).le he 4
    rw [← Real.exp_nat_mul] at hp
    norm_num [Finset.sum_range_succ] at hp
    norm_num
    apply hp.trans
    linarith [Real.pi_gt_d6]
  unfold upperLog
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith [Fixed032281.log_3100_interval.1]

theorem endpoint_second_base_phase :
    -upperLog 3100 / 2 -
      0.478 * ((3100 : ℝ) + Real.log 0.001) / upperLog 3100 ≤ -54.617 := by
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

theorem exp_endpoint_second_base :
    Real.exp (-54.617 : ℝ) ≤ 0.00000000000000000000000191 := by
  have he := Real.sum_le_exp_of_nonneg (x := (0.617 : ℝ)) (by norm_num) 12
  have h1 : (2.718281828 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := mul_le_mul (pow_le_pow_left₀ (by norm_num) h1 54) he
    (by positivity) (by positivity)
  rw [← Real.exp_nat_mul, ← Real.exp_add] at hp
  norm_num [Finset.sum_range_succ] at hp
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith only [hp]

theorem endpointSecondScalar_fixed :
    endpointSecondScalar 3100 ≤ 0.00046 := by
  have hnu := Fixed032281.sourceNu_fixed_upper
  have hnu0 := (sourceNu_linear_scaling (L := (3100 : ℝ)) le_rfl).1
  have hlo := upperLog_base_lower
  have hup := pow_le_pow_left₀ (show 0 ≤ upperLog 3100 by linarith)
    Fixed032281.upper_endpoint 6
  have he := (Real.exp_le_exp.mpr endpoint_second_base_phase).trans exp_endpoint_second_base
  have hc := mul_le_mul
    (mul_le_mul_of_nonneg_right hnu (by norm_num : (0 : ℝ) ≤ 3100)) hup
    (by positivity) (by norm_num)
  have hh := mul_le_mul hc he (Real.exp_pos _).le (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 16 * 16541)
  unfold endpointSecondScalar
  norm_num at hm
  nlinarith only [hm]

theorem endpointSecondScalar_payment (L : ℝ) (hL : 3100 ≤ L) :
    endpointSecondScalar L ≤ 0.00046 :=
  (endpointSecondScalar_le_base hL).trans endpointSecondScalar_fixed

theorem endpoint_sqrt_normalization {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (Real.sqrt q / q.totient) * (1 / Real.sqrt (middleUpper N q)) =
      ((q : ℝ) / q.totient) * Real.exp (-upperLog (sourceL N) / 2) := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have he : 1 / Real.sqrt (10 * Real.pi * sourceL N ^ (7 : ℕ)) =
      Real.exp (-upperLog (sourceL N) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity), one_div, ← Real.exp_neg]
    unfold upperLog
    congr 1
    ring
  rw [middleUpper, Real.sqrt_div (by positivity), one_div_div]
  calc
    _ = ((Real.sqrt q * Real.sqrt q) / q.totient) *
        (1 / Real.sqrt (10 * Real.pi * sourceL N ^ (7 : ℕ))) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hq0.le, he]

theorem endpoint_16541_original_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (16 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((1 / Real.sqrt (middleUpper N q)) *
        (16541 * upperLog (sourceL N) ^ (6 : ℕ) *
          Real.exp (-0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N)))) ≤
      0.00046 * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have heq :
      (16 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((1 / Real.sqrt (middleUpper N q)) *
          (16541 * upperLog (sourceL N) ^ (6 : ℕ) *
            Real.exp (-0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N)))) =
      (16 * 16541 * (N : ℝ)) * ((q : ℝ) / q.totient) * upperLog (sourceL N) ^ (6 : ℕ) *
        Real.exp (-upperLog (sourceL N) / 2 -
          0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N)) := by
    have hex : Real.exp (-upperLog (sourceL N) / 2 -
        0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N)) =
      Real.exp (-upperLog (sourceL N) / 2) *
        Real.exp (-0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hex]
    have h := endpoint_sqrt_normalization (q := q) hN
    linear_combination
      (16 * (N : ℝ) * 16541 * upperLog (sourceL N) ^ (6 : ℕ) *
        Real.exp (-0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N))) * h
  rw [heq]
  have hphi := mul_le_mul_of_nonneg_right hnu
    (show 0 ≤ (16 * 16541 * (N : ℝ)) * upperLog (sourceL N) ^ (6 : ℕ) *
      Real.exp (-upperLog (sourceL N) / 2 -
        0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N)) by positivity)
  have hbudget := mul_le_mul_of_nonneg_left (endpointSecondScalar_payment (sourceL N) hL)
    (show 0 ≤ (N : ℝ) / sourceL N by positivity)
  have hnorm : sourceNu (sourceP N) *
      ((16 * 16541 * (N : ℝ)) * upperLog (sourceL N) ^ (6 : ℕ) *
        Real.exp (-upperLog (sourceL N) / 2 -
          0.478 * (sourceL N + Real.log 0.001) / upperLog (sourceL N))) =
      ((N : ℝ) / sourceL N) * endpointSecondScalar (sourceL N) := by
    unfold endpointSecondScalar sourceP
    field_simp
  rw [hnorm] at hphi
  have hh := hphi.trans hbudget
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

#print axioms endpointSecondScalar_payment
#print axioms endpoint_16541_original_payment

end LiuWang.Proof.Campaign20260915.SecondTerminal
