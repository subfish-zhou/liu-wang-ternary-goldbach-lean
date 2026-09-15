import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1.FixedSource
import LiuWang.Proof.SourceRoute.MajorException.MixedMoments

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularIntegral LiuWang.Proof.SingularSeries
open LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.SourceRoute.MajorException
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1

theorem continuous_triple_holder (f g h phase : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hp : Continuous phase) (hp1 : ∀ x, ‖phase x‖ = 1)
    {delta K A B C : ℝ} (hd : 0 ≤ delta)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hfm : (∫ x in -delta..delta, ‖f x‖ ^ 3) ≤ K * A ^ 3)
    (hgm : (∫ x in -delta..delta, ‖g x‖ ^ 3) ≤ K * B ^ 3)
    (hhm : (∫ x in -delta..delta, ‖h x‖ ^ 3) ≤ K * C ^ 3) :
    ‖∫ x in -delta..delta, f x * g x * h x * phase x‖ ≤ K * A * B * C := by
  have hif := (hf.norm.pow 3).intervalIntegrable (μ := volume) (-delta) delta
  have hig := (hg.norm.pow 3).intervalIntegrable (μ := volume) (-delta) delta
  have hih := (hh.norm.pow 3).intervalIntegrable (μ := volume) (-delta) delta
  apply (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans
  have hm := intervalIntegral.integral_mono_on (by linarith : -delta ≤ delta)
    ((((hf.mul hg).mul hh).mul hp).norm.intervalIntegrable _ _)
    ((((hif.div_const (A ^ 3)).add (hig.div_const (B ^ 3))).add
      (hih.div_const (C ^ 3))).const_mul (A * B * C / 3))
    (fun x _ => by
      simpa only [Pi.mul_apply, Pi.pow_apply, norm_mul, hp1, mul_one] using
        scaled_triple_young (norm_nonneg (f x)) (norm_nonneg (g x))
          (norm_nonneg (h x)) hA hB hC)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hif.div_const _).add (hig.div_const _)) (hih.div_const _),
    intervalIntegral.integral_add (hif.div_const _) (hig.div_const _),
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_div] at hm
  apply hm.trans
  have hf' := div_le_div_of_nonneg_right hfm (pow_nonneg hA.le 3)
  have hg' := div_le_div_of_nonneg_right hgm (pow_nonneg hB.le 3)
  have hh' := div_le_div_of_nonneg_right hhm (pow_nonneg hC.le 3)
  apply (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hf' hg') hh')
    (show 0 ≤ A * B * C / 3 by positivity)).trans_eq
  field_simp
  ring

def cubicArc (N q : ℕ) (c : ℕ → ℂ) (f g h : ℕ → ℝ → ℂ) : ℂ :=
  ∑ a ∈ numerators q, c a * ∫ eta in -deltaRadius N q..deltaRadius N q,
    f a eta * g a eta * h a eta * arcPhase N a q eta

theorem cubicArc_bound {N q : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : 0 < q)
    (c : ℕ → ℂ) (f g h : ℕ → ℝ → ℂ)
    {D A B C : ℝ} (hD : 0 ≤ D) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hc : ∀ a ∈ numerators q, ‖c a‖ ≤ D)
    (hf : ∀ a ∈ numerators q, Continuous (f a))
    (hg : ∀ a ∈ numerators q, Continuous (g a))
    (hh : ∀ a ∈ numerators q, Continuous (h a))
    (hfm : ∀ a ∈ numerators q,
      (∫ x in -deltaRadius N q..deltaRadius N q, ‖f a x‖ ^ 3) ≤ (N : ℝ) ^ 2 * A ^ 3)
    (hgm : ∀ a ∈ numerators q,
      (∫ x in -deltaRadius N q..deltaRadius N q, ‖g a x‖ ^ 3) ≤ (N : ℝ) ^ 2 * B ^ 3)
    (hhm : ∀ a ∈ numerators q,
      (∫ x in -deltaRadius N q..deltaRadius N q, ‖h a x‖ ^ 3) ≤ (N : ℝ) ^ 2 * C ^ 3) :
    ‖cubicArc N q c f g h‖ ≤ q.totient * D * (N : ℝ) ^ 2 * A * B * C := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a ∈ numerators q, D * ((N : ℝ) ^ 2 * A * B * C) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      exact mul_le_mul (hc a ha)
        (continuous_triple_holder (f a) (g a) (h a) (arcPhase N a q)
          (hf a ha) (hg a ha) (hh a ha) (continuous_arcPhase N a q)
          (norm_arcPhase N a q)
          (deltaRadius_pos (exp_2000_le_of_exp_3100_le hN) hq).le
          hA hB hC (hfm a ha) (hgm a ha) (hhm a ha)) (norm_nonneg _) hD
    _ = _ := by
      have hcard : (numerators q).card = q.totient := reducedResidues_card q
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      ring

theorem ordinaryPacket_cubic {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : Nat.Coprime a q)
    (d : PrimitiveQuadraticDatum) (e : ℂ) {M : ℝ}
    (hM : ordinaryMass N q d e ≤ M) :
    (∫ eta in -deltaRadius N q..deltaRadius N q,
      ‖ordinaryPacket N a q d e eta‖ ^ 3) ≤
        (N : ℝ) ^ 2 * ((Real.sqrt q / q.totient) * radiusRoot N q * M) ^ 3 := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hd := deltaRadius_pos hN' (NeZero.pos q)
  have hn := natCast_pos_of_exp_le hN
  have hm := intervalIntegral.integral_mono_on (by linarith : -deltaRadius N q ≤ deltaRadius N q)
    (((ordinaryPacket_continuous (nat_pos_of_exp_le hN) a d e).norm.pow 3).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume))
    (fun eta he => pow_le_pow_left₀ (norm_nonneg _)
      ((ordinaryPacket_bound hN ha d e (abs_le.mpr he)).trans
        (mul_le_mul_of_nonneg_left hM (by positivity))) 3)
  apply hm.trans_eq
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_neg_eq_add, mul_pow, radiusRoot]
  rw [cubeRoot_cube (by positivity)]
  ring

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1
