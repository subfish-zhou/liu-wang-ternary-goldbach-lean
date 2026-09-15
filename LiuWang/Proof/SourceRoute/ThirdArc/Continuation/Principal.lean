import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.Totient
import LiuWang.Proof.WeightedLowZeros.Weight

/-! Original (5.19) principal price and the independent (5.21) one-zero price. -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.CompleteExpansion

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation

theorem principalMass_paid {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    principalMass q ≤ 0.00000068 / sourceL N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hq0 := Nat.cast_pos.mp ((sourceP_pos hn).trans_le hq)
  have hf : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq0)
  have hm : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  unfold principalMass
  apply (div_le_div_iff₀ hf (sourceL_pos hn)).mpr
  exact (mul_le_mul_of_nonneg_right hm (sourceL_pos hn).le).trans
    (by simpa only [one_mul] using principal_totient_scale hN hq)

theorem principal_term_paid {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) (eta : ℝ) :
    ‖principalCoefficient q * J N eta‖ ≤ 0.00000068 * (N : ℝ) / sourceL N := by
  rw [norm_mul, norm_principalCoefficient]
  have hj : ‖J N eta‖ ≤ (N : ℝ) :=
    (OscillatoryBounds.J_length N eta).trans (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  exact (mul_le_mul (principalMass_paid hN hq) hj (norm_nonneg _) (by positivity)).trans_eq
    (by ring)

theorem principal_bound_paid {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    principalMass q * (0.999 * (N : ℝ)) ≤ 0.00000068 * (N : ℝ) / sourceL N := by
  have hp := mul_le_mul_of_nonneg_right (principalMass_paid hN hq)
    (show 0 ≤ 0.999 * (N : ℝ) by positivity)
  have hn := Nat.cast_nonneg (α := ℝ) N
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  apply hp.trans
  calc
    _ ≤ (0.00000068 / sourceL N) * (N : ℝ) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    _ = _ := by ring

theorem S_principal_and_error_paid {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq0 : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      sigma4 N q + sigma5 N q + sigma6 N q +
        0.000000680001 * (N : ℝ) / sourceL N := by
  have h := S_M3_fixed hN hi hq0 hq1 heta
  exact (h.trans (add_le_add (add_le_add (principal_bound_paid hN hq0.le) le_rfl)
    le_rfl)).trans_eq (by ring)

theorem one_zero_kernel_paid {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {rho : ℂ} (hb : 0 < rho.re) (hb1 : rho.re ≤ 1) (eta : ℝ) :
    (Real.sqrt q / q.totient) * ‖Jrho N rho eta‖ ≤
      0.11585 * (N : ℝ) / sourceL N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hn
  have hq0 := Nat.cast_pos.mp ((sourceP_pos hn).trans_le hq)
  have hf : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq0)
  have hscale : Real.sqrt q / q.totient ≤ 0.11585 / sourceL N := by
    apply (div_le_div_iff₀ hf (sourceL_pos hn)).mpr
    simpa only [mul_comm] using single_zero_totient_scale hN hq
  have hj : ‖Jrho N rho eta‖ ≤ (N : ℝ) := by
    have hw := WeightedLowZeros.weight_le_one (WeightedLowZeros.source_endpoint_ge_thousand hN)
      hb hb1
    have h := (WeightedLowZeros.Jrho_le_weight (nat_pos_of_exp_le hN) hb eta).trans
      (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _))
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact (mul_le_mul hscale hj (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem actual_simple_zero_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi lowHeight)
    (hsimple : analyticOrderNatAt chi.LFunction rho = 1) (eta : ℝ) :
    (Real.sqrt q / q.totient) *
      ((analyticOrderNatAt chi.LFunction rho : ℝ) * ‖Jrho N rho eta‖) ≤
        0.11585 * (N : ℝ) / sourceL N := by
  rw [hsimple, Nat.cast_one, one_mul]
  exact one_zero_kernel_paid hN hq (mem_zeroValues.mp hr).2.1
    (mem_zeroValues.mp hr).2.2.1.le eta

theorem one_zero_lowKernel_paid {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {rho : ℂ} (hb : 0 < rho.re) (hb1 : rho.re ≤ 1) :
    (Real.sqrt q / q.totient) * lowKernel N rho ≤
      0.11585 * (N : ℝ) / sourceL N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hn
  have hq0 := Nat.cast_pos.mp ((sourceP_pos hn).trans_le hq)
  have hf : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq0)
  have hscale : Real.sqrt q / q.totient ≤ 0.11585 / sourceL N := by
    apply (div_le_div_iff₀ hf hL).mpr
    simpa only [mul_comm] using single_zero_totient_scale hN hq
  have hw := WeightedLowZeros.weight_le_one (WeightedLowZeros.source_endpoint_ge_thousand hN)
    hb hb1
  have hk : lowKernel N rho ≤ (N : ℝ) := by
    rw [lowKernel, ← WeightedLowZeros.weight_mul_endpoint (nat_pos_of_exp_le hN)]
    exact (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)).trans
      (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  exact (mul_le_mul hscale hk (lowKernel_nonneg hb) (by positivity)).trans_eq (by ring)

theorem actual_simple_lowKernel_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi lowHeight)
    (hsimple : analyticOrderNatAt chi.LFunction rho = 1) :
    (Real.sqrt q / q.totient) *
      ((analyticOrderNatAt chi.LFunction rho : ℝ) * lowKernel N rho) ≤
        0.11585 * (N : ℝ) / sourceL N := by
  rw [hsimple, Nat.cast_one, one_mul]
  exact one_zero_lowKernel_paid hN hq (mem_zeroValues.mp hr).2.1
    (mem_zeroValues.mp hr).2.2.1.le

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation
