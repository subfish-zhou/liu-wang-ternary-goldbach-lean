import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.UniformCount
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.GateDomain
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.ExponentialIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment

theorem normalized_linear_height_jacobian {q z : ℝ} (hq : 0 < q) (hz : 0 < z) :
    (Real.sqrt q / q) * heightKernel (z / q) = q * heightKernel z := by
  have h1 := log_height_jacobian hq (Real.log z)
  have h2 := log_height_jacobian (q := 1) (by norm_num) (Real.log z)
  rw [Real.exp_log hz] at h1 h2
  norm_num only [div_one, Real.sqrt_one, one_mul] at h2
  rw [← h2] at h1
  have hs := Real.mul_self_sqrt hq.le
  apply (mul_left_cancel₀ hz.ne')
  have hm := congrArg (fun t : ℝ => Real.sqrt q * t) h1
  calc
    _ = Real.sqrt q * ((z / q) * heightKernel (z / q)) := by ring
    _ = Real.sqrt q * (Real.sqrt q * (z * heightKernel z)) := hm
    _ = z * (q * heightKernel z) := by rw [← mul_assoc, hs]; ring

theorem normalized_envelope_change {q : ℕ} [NeZero q] {u v H : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    Real.sqrt q * (∫ y in u..v, heightKernel y * countEnvelope q y *
      Real.exp (-0.478 * H / Real.log ((q : ℝ) * y))) =
      ∫ z in ((q : ℝ) * u)..((q : ℝ) * v), coupledKernel q H z := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hs := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := (q : ℝ) * u) (b := (q : ℝ) * v)
    (f := fun z : ℝ => z / (q : ℝ)) (f' := fun _ : ℝ => 1 / (q : ℝ))
    (g := fun y : ℝ => heightKernel y * countEnvelope q y *
      Real.exp (-0.478 * H / Real.log ((q : ℝ) * y)))
    (by fun_prop) (fun z _ => (hasDerivAt_id z).div_const (q : ℝ))
    (fun _ _ => by positivity)
  rw [mul_div_cancel_left₀ _ hq.ne', mul_div_cancel_left₀ _ hq.ne'] at hs
  rw [← hs, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro z hz
  rw [Set.uIcc_of_le (mul_le_mul_of_nonneg_left huv hq.le)] at hz
  have hz0 : 0 < z := (mul_pos hq hu).trans_le hz.1
  have hj := normalized_linear_height_jacobian hq hz0
  dsimp only [Function.comp_def, smul_eq_mul]
  unfold countEnvelope coupledKernel
  rw [mul_div_cancel₀ _ hq.ne']
  calc
    _ = ((Real.sqrt q / (q : ℝ)) * heightKernel (z / (q : ℝ))) *
        (((z / (q : ℝ)) / 3 + 4) * Real.log z + 30) *
          Real.exp (-0.478 * H / Real.log z) := by ring
    _ = _ := by rw [hj]; field_simp; ring

theorem lowHeight_le_envelope {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    lowHeightIntegral N q ≤ (q.totient : ℝ) *
      (∫ y in omegaCutoff N q..densityGate q, heightKernel y * countEnvelope q y *
        Real.exp (-0.478 * Real.log (0.001 * (N : ℝ)) / Real.log ((q : ℝ) * y))) := by
  have hd := low_gate_coupled_domain hN hq hgate
  have hi := (source_other_strips_integrable hN hq).1.mono_set
    (by
      rw [Set.uIcc_of_le hgate, Set.uIcc_of_le (middle_height_domain hN hq).2.1]
      exact Set.Icc_subset_Icc le_rfl hd.2.1)
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hl : ContinuousOn (fun y : ℝ => Real.log ((q : ℝ) * y))
      (Set.Icc (omegaCutoff N q) (densityGate q)) :=
    (continuousOn_const.mul continuousOn_id).log (fun y hy => by
      have hy0 := hd.1.trans_le hy.1
      exact mul_ne_zero hq0.ne' hy0.ne')
  have hlog : ∀ y ∈ Set.Icc (omegaCutoff N q) (densityGate q),
      Real.log ((q : ℝ) * y) ≠ 0 := by
    intro y hy
    have hh := exact_scale_domain hN hq hy.1
    exact ne_of_gt (Real.log_pos (by linarith [hh.2.1]))
  have he : ContinuousOn (fun y => heightKernel y * countEnvelope q y *
      Real.exp (-0.478 * Real.log (0.001 * (N : ℝ)) / Real.log ((q : ℝ) * y)))
      (Set.Icc (omegaCutoff N q) (densityGate q)) := by
    unfold countEnvelope heightKernel
    exact ((continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt (hd.1.trans_le hy.1)))).mul
      (((continuousOn_id.div_const 3).add continuousOn_const).mul hl |>.add continuousOn_const)).mul
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.div hl hlog))
  rw [lowHeightIntegral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hgate hi
    ((he.const_mul (q.totient : ℝ)).intervalIntegrable_of_Icc hgate)
  intro y hy
  have hh := actual_inner_le_envelope (q := q) hN
    ((omegaCutoff_ge (NeZero.pos q) hq).trans hy.1)
  exact (mul_le_mul_of_nonneg_left hh (heightKernel_nonneg (hd.1.le.trans hy.1))).trans_eq (by ring)

theorem actual_low_height_coupled_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    (Real.sqrt q / q.totient) * lowHeightIntegral N q ≤
      ∫ z in (3.36 * sourceL N ^ (3 : ℕ))..((q : ℝ) * densityGate q),
        coupledKernel q (sourceL N + Real.log 0.001) z := by
  have hd := low_gate_coupled_domain hN hq hgate
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hh := mul_le_mul_of_nonneg_left (lowHeight_le_envelope hN hq hgate)
    (by positivity : 0 ≤ Real.sqrt q / (q.totient : ℝ))
  have he := normalized_envelope_change (q := q) hd.1 hgate
    (H := Real.log (0.001 * (N : ℝ)))
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hstart : (q : ℝ) * omegaCutoff N q = 3.36 * sourceL N ^ (3 : ℕ) := by
    unfold omegaCutoff sourceP
    field_simp
  rw [hstart, log_window_eq (nat_pos_of_exp_le hN)] at he
  rw [log_window_eq (nat_pos_of_exp_le hN)] at hh
  rw [← he]
  exact hh.trans_eq (by field_simp)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
