import LiuWang.Proof.MiddleArcPayment.Continuation.Totient

/-!
# A numerical payment, including the possible exceptional zero

On the original M3, the entire R24 packet costs at most 0.23976 N/L.
This is a proper subpacket of beta>59/60, not a claim to pay that whole band.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.CompleteExpansion

namespace LiuWang.Proof.MiddleArcPayment.Continuation

theorem twentyfive_le_log_power {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    25 ≤ sourceL N ^ (13 / 32 : ℝ) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  apply le_of_pow_le_pow_left₀ (n := 32) (by norm_num) (by positivity)
  rw [← Real.rpow_mul_natCast hL.le,
    show (13 / 32 : ℝ) * (32 : ℕ) = (13 : ℕ) by norm_num, Real.rpow_natCast]
  exact le_trans (by norm_num : (25 : ℝ) ^ 32 ≤ 3100 ^ 13)
    (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 13)

theorem sqrt_div_totient_middle {q N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N < (q : ℝ)) :
    Real.sqrt q / (q.totient : ℝ) ≤ 0.24 / sourceL N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hn
  have hqR : (0 : ℝ) < q := (sourceP_pos hn).trans hq
  have hqN : 0 < q := Nat.cast_pos.mp hqR
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hqN)
  have hQ : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqR
  have hpow : 25 * sourceL N ≤ (q : ℝ) ^ (15 / 32 : ℝ) := by
    calc
      _ ≤ sourceL N ^ (13 / 32 : ℝ) * sourceL N :=
        mul_le_mul_of_nonneg_right (twentyfive_le_log_power hN) hL.le
      _ = sourceL N ^ (45 / 32 : ℝ) := by
        rw [show (45 / 32 : ℝ) = 13 / 32 + 1 by norm_num,
          Real.rpow_add hL, Real.rpow_one]
      _ = (sourceL N ^ (3 : ℕ)) ^ (15 / 32 : ℝ) := by
        rw [← Real.rpow_natCast_mul hL.le]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hq.le (by norm_num)
  calc
    _ = ((q : ℝ) / q.totient) / Real.sqrt q := by
      apply (div_eq_div_iff hphi.ne' hQ.ne').mpr
      field_simp
      nlinarith [Real.sq_sqrt hqR.le]
    _ ≤ (6 * (q : ℝ) ^ (1 / 32 : ℝ)) / Real.sqrt q :=
      div_le_div_of_nonneg_right (totient_ratio_le_six_rpow hqN) hQ.le
    _ = 6 / (q : ℝ) ^ (15 / 32 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      have he : (q : ℝ) ^ (1 / 32 : ℝ) * (q : ℝ) ^ (15 / 32 : ℝ) =
          (q : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hqR]
        norm_num
      apply (div_eq_div_iff (by positivity) (by positivity)).mpr
      nlinarith [he]
    _ ≤ 6 / (25 * sourceL N) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
    _ = _ := by ring

theorem rightmostPacket_middle_paid {q N : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq0 : sourceP N < (q : ℝ))
    {x : ℝ} (hx : 10 ≤ x) (hqx : (q : ℝ) ≤ x)
    (a : ℕ) (ha : Nat.Coprime a q) (eta : ℝ) :
    ‖rightmostPacket q N a eta x‖ ≤ 0.23976 * (N : ℝ) / sourceL N := by
  apply (norm_rightmostPacket_le (exp_2000_le_of_exp_3100_le hN) hx hqx a ha eta).trans
  calc
    _ = (Real.sqrt q / (q.totient : ℝ)) * (0.999 * (N : ℝ)) := by ring
    _ ≤ (0.24 / sourceL N) * (0.999 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (sqrt_div_totient_middle hN hq0) (by positivity)
    _ = _ := by ring

def fullHeightCutoff (q N : ℕ) : ℝ :=
  1 - 1 / (24 * Real.log ((q : ℝ) * sourceT N))

theorem fullHeight_parameters {q N : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    10 ≤ (q : ℝ) * sourceT N ∧ (q : ℝ) ≤ (q : ℝ) * sourceT N ∧
      sourceT N ≤ ((q : ℝ) * sourceT N) / (q : ℝ) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hT : 2000 ≤ sourceT N := by
    apply (sourceL_ge_2000 hN).trans
    simpa only [pow_one, sourceT] using
      pow_le_pow_right₀ (one_le_sourceL hN) (by norm_num : 1 ≤ 15)
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  rw [mul_div_cancel_left₀ _ (by positivity : (q : ℝ) ≠ 0)]

theorem upperPacket_fullHeight_paid {q N : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq0 : sourceP N < (q : ℝ))
    (a : ℕ) (ha : Nat.Coprime a q) (eta : ℝ) :
    ‖upperPacket q N a eta (fullHeightCutoff q N)‖ ≤
      0.23976 * (N : ℝ) / sourceL N := by
  obtain ⟨hx, hqx, hT⟩ := fullHeight_parameters (q := q) (exp_2000_le_of_exp_3100_le hN)
  rw [fullHeightCutoff, upperPacket_eq_rightmost a eta _ hT]
  exact rightmostPacket_middle_paid hN hq0 hx hqx a ha eta

theorem principal_main_middle_paid {q N : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq0 : sourceP N < (q : ℝ))
    (eta : ℝ) :
    ‖principalCoefficient q * J N eta‖ ≤ 0.0001 * (N : ℝ) / sourceL N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hn
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hsmall : (2400 : ℝ) ≤ Real.sqrt q := by
    apply Real.le_sqrt_of_sq_le
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) (sourceL_ge_3100 hN) 3
    change sourceL N ^ 3 < (q : ℝ) at hq0
    norm_num at h
    linarith
  have hcoef : principalMass q ≤ 0.0001 / sourceL N := by
    have hm : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
    have hs := sqrt_div_totient_middle hN hq0
    have hprod : (2400 : ℝ) / q.totient ≤ 0.24 / sourceL N :=
      (div_le_div_of_nonneg_right hsmall hphi.le).trans hs
    have hmul := (div_le_div_iff₀ hphi hL).mp hprod
    unfold principalMass
    apply (div_le_div_iff₀ hphi hL).mpr
    have hh := mul_le_mul_of_nonneg_right hm hL.le
    nlinarith
  rw [norm_mul, norm_principalCoefficient]
  calc
    _ ≤ (0.0001 / sourceL N) * (0.999 * (N : ℝ)) :=
      mul_le_mul hcoef (OscillatoryBounds.J_length N eta) (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      have hs := mul_le_mul_of_nonneg_right (by norm_num : (0.0000999 : ℝ) ≤ 0.0001)
        (show 0 ≤ (N : ℝ) / sourceL N by positivity)
      calc
        _ = 0.0000999 * ((N : ℝ) / sourceL N) := by ring
        _ ≤ 0.0001 * ((N : ℝ) / sourceL N) := hs
        _ = _ := by ring

theorem S_upper_packet_paid {q N a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq0 : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N)
    {eta : ℝ} (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      countPayment q N a eta (fullHeightCutoff q N) +
        0.239860000001 * (N : ℝ) / sourceL N := by
  have hp := principal_main_middle_paid hN hq0 eta
  have hz := upperPacket_fullHeight_paid hN hq0 a hi.2.2 eta
  have he := middle_error_regression (a := a) (exp_2000_le_of_exp_3100_le hN) hq0 hq1 heta
  have hc := S_le_countPayment (exp_2000_le_of_exp_3100_le hN) hi hq1 eta (fullHeightCutoff q N)
  have hnorm := (norm_sub_le _ _).trans (add_le_add hp hz)
  have h := hc.trans (add_le_add (add_le_add hnorm le_rfl) he)
  apply h.trans_eq
  ring

end LiuWang.Proof.MiddleArcPayment.Continuation
