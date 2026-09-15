import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.BandMass

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart

theorem normalized_height_bounds {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    Real.sqrt q * Real.sqrt (middleUpper N q) ≤
        5.7 * sourceL N ^ (3 : ℕ) * Real.sqrt (sourceL N) ∧
      Real.sqrt q / Real.sqrt (omegaCutoff N q) ≤ sourceL N ^ (2 : ℕ) := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have hL1 : 1 ≤ sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hd := middle_height_domain hN hq
  have hqv : (q : ℝ) * middleUpper N q = 10 * Real.pi * sourceL N ^ (7 : ℕ) := by
    unfold middleUpper
    field_simp
  constructor
  · apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hq0.le, Real.sq_sqrt (hd.1.le.trans hd.2.1), hqv]
    have hs := Real.sq_sqrt hLp.le
    have hp := mul_le_mul_of_nonneg_right
      (by nlinarith [Real.pi_lt_d2] : 10 * Real.pi ≤ (5.7 : ℝ) ^ (2 : ℕ))
      (by positivity : 0 ≤ sourceL N ^ (7 : ℕ))
    calc
      _ ≤ (5.7 : ℝ) ^ (2 : ℕ) * sourceL N ^ (7 : ℕ) := hp
      _ = _ := by rw [mul_pow, mul_pow, hs]; ring
  · have hu : 1 ≤ Real.sqrt (omegaCutoff N q) :=
      (Real.le_sqrt (by norm_num) hd.1.le).mpr
        (by linarith [omegaCutoff_ge (NeZero.pos q) hq])
    have hs : Real.sqrt (q : ℝ) ≤ sourceL N ^ (2 : ℕ) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      apply hq.trans
      change sourceL N ^ (3 : ℕ) ≤ (sourceL N ^ (2 : ℕ)) ^ (2 : ℕ)
      rw [← pow_mul]
      exact pow_le_pow_right₀ hL1 (by norm_num)
    exact (div_le_self (Real.sqrt_nonneg _) hu).trans hs

theorem source_bandMass_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {alpha : ℝ} (ha : 0 ≤ alpha) :
    (Real.sqrt q / q.totient) * bandMass q alpha (omegaCutoff N q) (middleUpper N q) ≤
      4 * sourceL N ^ (3 : ℕ) * Real.sqrt (sourceL N) *
        Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)) := by
  have hd := middle_height_domain hN hq
  have hb := bandMass_le_uniform (q := q) ha (omegaCutoff_ge (NeZero.pos q) hq) hd.2.1
  have hn := normalized_height_bounds hN hq
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have hs1 : 1 ≤ Real.sqrt (sourceL N) :=
    (Real.le_sqrt (by norm_num) hLp.le).mpr (by linarith)
  have hl := (middle_log_domain hN hq
    (show middleUpper N q ∈ Set.Icc (omegaCutoff N q) (middleUpper N q) from
      ⟨hd.2.1, le_rfl⟩)).2.1
  rw [(source_log_endpoints (N := N) (q := q)).2] at hl hb
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ Real.sqrt q / q.totient)
  have he : (Real.sqrt q / (q.totient : ℝ)) *
      ((q.totient : ℝ) * ((2 / 3 : ℝ) * Real.sqrt (middleUpper N q) *
        Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)) +
        (4 * Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)) + 30) /
          Real.sqrt (omegaCutoff N q))) =
      (2 / 3 : ℝ) * (Real.sqrt q * Real.sqrt (middleUpper N q)) *
        Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)) +
      (Real.sqrt q / Real.sqrt (omegaCutoff N q)) *
        (4 * Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)) + 30) := by field_simp
  rw [he] at hh
  apply hh.trans
  have hmain := mul_le_mul_of_nonneg_right hn.1
    (by linarith : 0 ≤ (2 / 3 : ℝ) * Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)))
  have hsmall := mul_le_mul hn.2
    (by linarith : 4 * Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)) + 30 ≤
      34 * Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)))
    (by positivity : 0 ≤ 4 * Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)) + 30)
    (by positivity : 0 ≤ sourceL N ^ (2 : ℕ))
  have hcoef : 34 * sourceL N ^ (2 : ℕ) ≤
      0.2 * sourceL N ^ (3 : ℕ) * Real.sqrt (sourceL N) := by
    have hm := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ sourceL N ^ (3 : ℕ))
    have hh' := mul_nonneg (by linarith : 0 ≤ 0.2 * sourceL N - 34)
      (by positivity : 0 ≤ sourceL N ^ (2 : ℕ))
    nlinarith only [hm, hh']
  have hc := mul_le_mul_of_nonneg_right hcoef (by linarith : 0 ≤
    Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)))
  nlinarith only [hmain, hsmall, hc]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
