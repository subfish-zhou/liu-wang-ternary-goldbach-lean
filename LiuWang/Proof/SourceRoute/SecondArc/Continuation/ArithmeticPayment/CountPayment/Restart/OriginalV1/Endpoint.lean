import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.SparseBands

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

def endpointDensityBound (q : ℕ) (y : ℝ) : ℝ :=
  (254231 / Real.log ((q : ℝ) * y) + 17102) *
    ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 / 60 : ℝ) *
    Real.log ((q : ℝ) * y) ^ (6 : ℕ) +
      16541 * Real.log ((q : ℝ) * y) ^ (6 : ℕ)

theorem sourceSeven_endpoint_envelope {q : ℕ} [NeZero q] {alpha y : ℝ}
    (hy : 1 ≤ y) (hz : 1 ≤ Real.log ((q : ℝ) * y))
    (ha : 59 / 60 ≤ alpha) (ha1 : alpha ≤ 1) :
    sourceSevenBound q alpha y ≤ endpointDensityBound q y := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hy0 : 0 < y := by linarith
  have hlog : Real.log y ≤ Real.log ((q : ℝ) * y) :=
    Real.log_le_log hy0 (le_mul_of_one_le_left hy0.le hq)
  have hp := pow_le_pow_left₀ (Real.log_nonneg hy) hlog 6
  have hb : 1 ≤ (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq) (one_le_pow₀ hy)
  have hr := Real.rpow_le_rpow_of_exponent_le hb
    (by linarith : 1 - alpha ≤ (1 / 60 : ℝ))
  have hl : Real.log ((q : ℝ) * y) ^ (6 * alpha) ≤
      Real.log ((q : ℝ) * y) ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hz (by norm_num; linarith)
  unfold sourceSevenBound endpointDensityBound
  have hc : 0 ≤ 17102 + 254231 / Real.log ((q : ℝ) * y) := by positivity
  calc
    _ ≤ 16541 * Real.log ((q : ℝ) * y) ^ (6 : ℕ) +
        (17102 + 254231 / Real.log ((q : ℝ) * y)) *
          ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 / 60 : ℝ) *
            Real.log ((q : ℝ) * y) ^ (6 : ℕ) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num))
        (mul_le_mul (mul_le_mul_of_nonneg_left hr hc) hl (by positivity) (by positivity))
    _ = _ := by ring

theorem endpoint_log_ge_thirty {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    30 ≤ Real.log ((q : ℝ) * middleUpper N q) := by
  rw [(source_log_endpoints (N := N) (q := q)).2]
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  apply (Real.le_log_iff_exp_le (by positivity)).mpr
  calc
    Real.exp 30 = Real.exp 1 ^ (30 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (3 : ℝ) ^ (30 : ℕ) := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
    _ ≤ 20 * (3100 : ℝ) ^ (7 : ℕ) := by norm_num
    _ ≤ 10 * Real.pi * sourceL N ^ (7 : ℕ) :=
      mul_le_mul (by linarith [Real.two_le_pi])
        (pow_le_pow_left₀ (by norm_num) hL _) (by positivity) (by positivity)

theorem truncated_endpoint_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y) :
    (1 / Real.sqrt (middleUpper N q)) *
      (∫ alpha in (59 / 60 : ℝ)..siegelCutoff q (middleUpper N q),
        alphaKernel (0.001 * (N : ℝ)) alpha *
          (familyCount q alpha (middleUpper N q) : ℝ)) ≤
      (1 / Real.sqrt (middleUpper N q)) *
        (endpointDensityBound q (middleUpper N q) *
          Real.exp (-0.478 * (sourceL N + Real.log 0.001) /
            Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ))) +
          14000 * Real.exp (-0.10367089 * (sourceL N + Real.log 0.001) /
            Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)))) := by
  have hh := middle_height_domain hN hq
  have hd := middle_log_domain hN hq ⟨hh.2.1, le_rfl⟩
  have hz := endpoint_log_ge_thirty (q := q) hN
  have hz0 : 0 < Real.log ((q : ℝ) * middleUpper N q) := by linarith
  have hn := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have hx1 := window_base_ge_one hN
  have ha : (59 / 60 : ℝ) ≤ stripLower q (middleUpper N q) := by
    have hdiv : 0.478 / Real.log ((q : ℝ) * middleUpper N q) ≤ (1 / 60 : ℝ) :=
      (div_le_iff₀ hz0).mpr (by linarith)
    unfold stripLower
    linarith
  have hb : stripLower q (middleUpper N q) ≤ siegelCutoff q (middleUpper N q) :=
    (strip_order (q := q) hd.1).trans (sparse_cutoff_order hd.2.1).2.1
  have hc := (sparse_cutoff_order hd.2.1).2.2
  have hB : 0 ≤ endpointDensityBound q (middleUpper N q) := by
    unfold endpointDensityBound
    positivity
  have hfirst := count_strip_le_constant hx1 ha (K := endpointDensityBound q (middleUpper N q))
    (y := middleUpper N q) (by
      intro alpha halpha
      exact (hseven _ (densityGate_le_middle hN hq) alpha
        (by linarith [halpha.1]) ((halpha.2.trans_le hb).trans hc)).trans
          (sourceSeven_endpoint_envelope hd.1 hd.2.1 halpha.1.le
            ((halpha.2.trans_le hb).trans hc).le))
  have htail := count_strip_le_constant hx1 hb (K := (14000 : ℝ))
    (y := middleUpper N q) (fun alpha halpha =>
      actual_familyCount_14000 hN hq hh.2.1 halpha.1.le)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (count_alpha_integrable (q := q) hx ha (middleUpper N q))
    (count_alpha_integrable (q := q) hx hb (middleUpper N q))
  have hbound :
      (∫ alpha in (59 / 60 : ℝ)..siegelCutoff q (middleUpper N q),
        alphaKernel (0.001 * (N : ℝ)) alpha *
          (familyCount q alpha (middleUpper N q) : ℝ)) ≤
      endpointDensityBound q (middleUpper N q) *
        (0.001 * (N : ℝ)) ^ (stripLower q (middleUpper N q) - 1) +
      14000 * (0.001 * (N : ℝ)) ^ (siegelCutoff q (middleUpper N q) - 1) := by
    rw [← hsplit]
    exact add_le_add
      (hfirst.trans (mul_le_mul_of_nonneg_left
        (sub_le_self _ (Real.rpow_nonneg hx.le _)) hB))
      (htail.trans (mul_le_mul_of_nonneg_left
        (sub_le_self _ (Real.rpow_nonneg hx.le _)) (by norm_num)))
  have hpow1 : (0.001 * (N : ℝ)) ^ (stripLower q (middleUpper N q) - 1) =
      Real.exp (-0.478 * Real.log (0.001 * (N : ℝ)) /
        Real.log ((q : ℝ) * middleUpper N q)) := by
    rw [Real.rpow_def_of_pos hx]
    unfold stripLower
    congr 1
    ring
  have hpow2 : (0.001 * (N : ℝ)) ^ (siegelCutoff q (middleUpper N q) - 1) ≤
      Real.exp (-0.10367089 * Real.log (0.001 * (N : ℝ)) /
        Real.log ((q : ℝ) * middleUpper N q)) := by
    rw [Real.rpow_def_of_pos hx]
    apply Real.exp_le_exp.mpr
    have hr := mul_le_mul_of_nonneg_right
      (by norm_num : (0.10367089 : ℝ) ≤ 1 / 9.645908801) (Real.log_nonneg hx1)
    have hr' := div_le_div_of_nonneg_right hr hz0.le
    unfold siegelCutoff
    calc
      _ = -(((1 : ℝ) / 9.645908801) * Real.log (0.001 * (N : ℝ)) /
          Real.log ((q : ℝ) * middleUpper N q)) := by ring
      _ ≤ -(0.10367089 * Real.log (0.001 * (N : ℝ)) /
          Real.log ((q : ℝ) * middleUpper N q)) := neg_le_neg hr'
      _ = _ := by ring
  rw [hpow1] at hbound
  have hpaid := hbound.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hpow2 (by norm_num : (0 : ℝ) ≤ 14000)))
  rw [log_window_eq (nat_pos_of_exp_le hN), (source_log_endpoints (N := N) (q := q)).2] at hpaid
  exact mul_le_mul_of_nonneg_left hpaid (by positivity)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1
