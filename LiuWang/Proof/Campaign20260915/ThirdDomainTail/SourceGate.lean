import LiuWang.Proof.Campaign20260915.ThirdDomainTail.DensityGate
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.RealTail

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdDomainTail

theorem source_high_gate_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    middleHeight N q ≤
      max (middleHeight N q) (max (100000 / (q : ℝ)) (10000 * Real.log q)) ∧
    max (middleHeight N q) (max (100000 / (q : ℝ)) (10000 * Real.log q)) ≤ sourceT N ∧
    ∀ y ∈ Set.Icc
      (max (middleHeight N q) (max (100000 / (q : ℝ)) (10000 * Real.log q))) (sourceT N),
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y := by
  refine ⟨le_max_left _ _, max_le ?_ (high_endpoint_source_domain hN hq1), ?_⟩
  · exact (original_height_order (exp_2000_le_of_exp_3100_le hN) hq1).2
  · intro y hy
    exact (le_max_right _ _).trans hy.1

theorem sourceM5_legal_gate_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    let g := max (middleHeight N q) (max (100000 / (q : ℝ)) (10000 * Real.log q))
    sourceM5 N q ≤
      (5 * N * Real.sqrt q / q.totient) *
        (((middleHeight N q)⁻¹ - g⁻¹) *
          countIntegral q N g (59 / 60) (sourceCutoff q 0.478 g) +
          ∫ y in g..sourceT N, y ^ (-2 : ℝ) *
            countIntegral q N y (59 / 60) (sourceCutoff q 0.478 y)) := by
  dsimp only
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hg := source_high_gate_domain hN hq1
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have h := moving_countIntegral_height_gate_split hN hq hX hh.1 hh.2 hg.1
    (d := 0.478) (p := 1) (by norm_num) le_rfl (by norm_num)
  rw [min_eq_right hg.2.1] at h
  simp only [heightKernel, one_mul, Real.rpow_neg_one,
    show -(1 : ℝ) - 1 = -2 by norm_num] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

#print axioms source_high_gate_domain
#print axioms sourceM5_legal_gate_split

end LiuWang.Proof.Campaign20260915.ThirdDomainTail
