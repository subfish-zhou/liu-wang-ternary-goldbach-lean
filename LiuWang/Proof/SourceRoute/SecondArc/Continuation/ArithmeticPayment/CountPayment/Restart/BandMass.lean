import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Packet
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.LowAlphaPayment

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart

theorem integral_height_times_id {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (∫ y in u..v, heightKernel y * y) = 2 * (Real.sqrt v - Real.sqrt u) := by
  have he : (∫ y in u..v, heightKernel y * y) =
      ∫ y in u..v, y ^ (-1 / 2 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le huv] at hy
    have hy0 := hu.trans_le hy.1
    dsimp only [heightKernel]
    nth_rw 2 [← Real.rpow_one y]
    rw [← Real.rpow_add hy0]
    norm_num
  rw [he, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
  norm_num only
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  ring

theorem bandMass_le_uniform {q : ℕ} [NeZero q] {alpha u v : ℝ}
    (ha : 0 ≤ alpha) (hu : 3.36 ≤ u) (huv : u ≤ v) :
    bandMass q alpha u v ≤ (q.totient : ℝ) *
      ((2 / 3 : ℝ) * Real.sqrt v * Real.log ((q : ℝ) * v) +
        (4 * Real.log ((q : ℝ) * v) + 30) / Real.sqrt u) := by
  have hu0 : 0 < u := by linarith
  have hv0 := hu0.trans_le huv
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hl0 := (log_height_shift (NeZero.pos q) (hu.trans huv)).1
  have hc := familyCount_le_envelope q ha (hu.trans huv)
  have hf := family_height_abel q alpha hu0 huv
  have hcont : ContinuousOn (fun y => heightKernel y * y) (Set.Icc u v) := by
    unfold heightKernel
    exact (continuousOn_id.rpow_const
      (fun y hy => Or.inl (ne_of_gt (hu0.trans_le hy.1)))).mul continuousOn_id
  have hi1 := hcont.intervalIntegrable_of_Icc (μ := volume) huv
  have hi2 := heightKernel_integrable hu0 huv
  have hi := intervalIntegral.integral_mono_on huv
    (familyCount_height_integrable q alpha hu0 huv)
    (((hi1.const_mul (Real.log ((q : ℝ) * v) / 3)).add
      (hi2.const_mul (4 * Real.log ((q : ℝ) * v) + 30))).const_mul (q.totient : ℝ))
    (by
      intro y hy
      have hy0 := hu0.trans_le hy.1
      have hl := Real.log_le_log (mul_pos hq0 hy0)
        (mul_le_mul_of_nonneg_left hy.2 hq0.le)
      have hh := familyCount_le_envelope q ha (hu.trans hy.1)
      have hm := mul_le_mul_of_nonneg_left hh (heightKernel_nonneg hy0.le)
      have he : countEnvelope q y ≤
          (y / 3 + 4) * Real.log ((q : ℝ) * v) + 30 := by
        unfold countEnvelope
        gcongr
      have hp := mul_le_mul_of_nonneg_left he
        (mul_nonneg (heightKernel_nonneg hy0.le) (Nat.cast_nonneg q.totient))
      nlinarith only [hm, hp])
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_height_times_id hu0 huv, integral_heightKernel hu0 huv] at hi
  have hv := Real.sq_sqrt hv0.le
  have hvp := Real.sqrt_pos.mpr hv0
  have hup := Real.sqrt_pos.mpr hu0
  have hce := div_le_div_of_nonneg_right hc hvp.le
  apply hf.trans
  calc
    _ ≤ (q.totient : ℝ) * countEnvelope q v / Real.sqrt v +
        (1 / 2 : ℝ) * ((q.totient : ℝ) *
          (Real.log ((q : ℝ) * v) / 3 * (2 * (Real.sqrt v - Real.sqrt u)) +
            (4 * Real.log ((q : ℝ) * v) + 30) *
              (2 * (1 / Real.sqrt u - 1 / Real.sqrt v)))) := by
      linarith only [hce, hi]
    _ = (q.totient : ℝ) *
        ((2 / 3 : ℝ) * Real.sqrt v * Real.log ((q : ℝ) * v) +
          (4 * Real.log ((q : ℝ) * v) + 30) / Real.sqrt u -
            Real.log ((q : ℝ) * v) / 3 * Real.sqrt u) := by
      unfold countEnvelope
      field_simp
      ring_nf
      rw [hv]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact sub_le_self _ (by positivity)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
