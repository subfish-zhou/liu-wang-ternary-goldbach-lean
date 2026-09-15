import LiuWang.Proof.SourceRoute.SecondArc.Continuation.MovingStrip

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation

def stripLower (q : ℕ) (y : ℝ) : ℝ := 1 - 0.478 / Real.log ((q : ℝ) * y)
def stripUpper (q : ℕ) (y : ℝ) : ℝ := 1 - 0.2067 / Real.log ((q : ℝ) * y)

def actualStripIntegral (N q : ℕ) [NeZero q] : ℝ :=
  ∫ y in (omegaCutoff N q)..(middleUpper N q), heightKernel y *
    ∫ alpha in (stripLower q y)..(stripUpper q y),
      alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)

theorem strip_bounds_continuous {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    ContinuousOn (stripLower q) (Set.Icc (omegaCutoff N q) (middleUpper N q)) ∧
      ContinuousOn (stripUpper q) (Set.Icc (omegaCutoff N q) (middleUpper N q)) := by
  have hprod : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q), (q : ℝ) * y ≠ 0 := by
    intro y hy
    have hy1 := (middle_log_domain hN hq hy).1
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    positivity
  have hl : ContinuousOn (fun y : ℝ => Real.log ((q : ℝ) * y))
      (Set.Icc (omegaCutoff N q) (middleUpper N q)) :=
    (continuousOn_const.mul continuousOn_id).log hprod
  have hn : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q),
      Real.log ((q : ℝ) * y) ≠ 0 :=
    fun y hy => ne_of_gt (by linarith [(middle_log_domain hN hq hy).2.1])
  exact ⟨continuousOn_const.sub (continuousOn_const.div hl hn),
    continuousOn_const.sub (continuousOn_const.div hl hn)⟩

theorem actualStrip_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    IntervalIntegrable (fun y => heightKernel y *
      ∫ alpha in (stripLower q y)..(stripUpper q y),
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ))
      volume (omegaCutoff N q) (middleUpper N q) := by
  have hh := middle_height_domain hN hq
  have hn := natCast_pos_of_exp_le hN
  have hs := strip_bounds_continuous hN hq
  have ha : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q), 1 / 2 ≤ stripLower q y := by
    intro y hy
    have hd := middle_log_domain hN hq hy
    have hdiv : 0.478 / Real.log ((q : ℝ) * y) ≤ (0.478 : ℝ) :=
      div_le_self (by norm_num) hd.2.1
    unfold stripLower
    linarith
  have hi := moving_count_strip_integrable (q := q) (by positivity : 0 < 0.001 * (N : ℝ))
    hh.2.1 hs.1 hs.2 ha
    (fun y hy => strip_order (q := q) (middle_log_domain hN hq hy).1)
  have hk : ContinuousOn heightKernel (Set.uIcc (omegaCutoff N q) (middleUpper N q)) := by
    rw [Set.uIcc_of_le hh.2.1]
    exact continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt (hh.1.trans_le hy.1)))
  simpa only [mul_comm] using hi.mul_continuousOn hk

theorem actualStripIntegral_nonneg {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    0 ≤ actualStripIntegral N q := by
  have hh := middle_height_domain hN hq
  have hn := natCast_pos_of_exp_le hN
  apply intervalIntegral.integral_nonneg hh.2.1
  intro y hy
  apply mul_nonneg (heightKernel_nonneg (hh.1.le.trans hy.1))
  apply intervalIntegral.integral_nonneg_of_forall
    (strip_order (q := q) (middle_log_domain hN hq hy).1)
  intro alpha
  have hl := Real.log_nonneg (window_base_ge_one hN)
  unfold alphaKernel
  positivity

theorem actualStripIntegral_le_kernel {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    actualStripIntegral N q ≤ 14000 *
      (∫ y in (omegaCutoff N q)..(middleUpper N q), heightKernel y *
        ∫ alpha in (stripLower q y)..(stripUpper q y), alphaKernel (0.001 * (N : ℝ)) alpha) := by
  have hh := middle_height_domain hN hq
  have hn := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have hs := strip_bounds_continuous hN hq
  have hg : ContinuousOn (fun y =>
      (0.001 * (N : ℝ)) ^ (stripUpper q y - 1) -
        (0.001 * (N : ℝ)) ^ (stripLower q y - 1))
      (Set.Icc (omegaCutoff N q) (middleUpper N q)) :=
    ((Real.continuous_const_rpow hx.ne').comp_continuousOn
      (hs.2.sub continuousOn_const)).sub
      ((Real.continuous_const_rpow hx.ne').comp_continuousOn (hs.1.sub continuousOn_const))
  have hk : ContinuousOn heightKernel (Set.Icc (omegaCutoff N q) (middleUpper N q)) :=
    continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt (hh.1.trans_le hy.1)))
  have hig : IntervalIntegrable (fun y => 14000 * (heightKernel y *
      ∫ alpha in (stripLower q y)..(stripUpper q y), alphaKernel (0.001 * (N : ℝ)) alpha))
      volume (omegaCutoff N q) (middleUpper N q) := by
    simp_rw [integral_alphaKernel hx]
    exact ((hk.mul hg).const_mul 14000).intervalIntegrable_of_Icc hh.2.1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hh.2.1 (actualStrip_integrable hN hq) hig
  intro y hy
  have hi := actual_inner_516 hN hq hy.1
  rw [← source_515_first_strip hx] at hi
  exact (mul_le_mul_of_nonneg_left hi (heightKernel_nonneg (hh.1.le.trans hy.1))).trans_eq
    (by unfold stripLower stripUpper; ring)

/-- Original (5.16), now with the actual full-family count rather than only the kernel. -/
theorem actual_contribution_516_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (8 * (N : ℝ) * Real.sqrt q / q.totient) * actualStripIntegral N q ≤
      (112000 * (N : ℝ)) * ((q : ℝ) / q.totient) *
        ∫ z in Real.log (3.36 * sourceL N ^ (3 : ℕ))..
          Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)),
            Real.exp (-z / 2) *
              (Real.exp (-0.2067 * (sourceL N + Real.log (0.001 : ℝ)) / z) -
                Real.exp (-0.478 * (sourceL N + Real.log (0.001 : ℝ)) / z)) := by
  rw [← source_516_kernel_identity hN hq]
  exact (mul_le_mul_of_nonneg_left (actualStripIntegral_le_kernel hN hq)
    (by positivity : 0 ≤ 8 * (N : ℝ) * Real.sqrt q / q.totient)).trans_eq (by
      unfold stripLower stripUpper
      ring)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation
