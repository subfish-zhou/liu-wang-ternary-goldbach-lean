import LiuWang.Proof.Campaign20260915.ThirdDomainTail.SourceGate

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdDomainTail

theorem source_middle_gate_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    let g := 10000 * Real.log (q : ℝ)
    lowHeight ≤ min (middleHeight N q) g ∧
      max (100000 / (q : ℝ)) g ≤ g ∧
      (middleHeight N q ≤ g → min (middleHeight N q) g = middleHeight N q) ∧
      (g ≤ middleHeight N q →
        ∀ y ∈ Set.Icc g (middleHeight N q), max (100000 / (q : ℝ)) g ≤ y) := by
  dsimp only
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hg := enlarged_height_source_domain hN hq hq1
  exact ⟨le_min hh.1 hg.1, hg.2, min_eq_left,
    fun _ _ hy => hg.2.trans hy.1⟩

theorem sigma5_endpoint_legal_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    let g := max (middleHeight N q) (max (100000 / (q : ℝ)) (10000 * Real.log q))
    sigma5 N q ≤ 0.0011 * (N : ℝ) / sourceL N +
      (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
        countIntegral q (0.001 * N) g (59 / 60) 1 +
      (8 * N * Real.sqrt q / q.totient) *
        ∫ y in lowHeight..middleHeight N q,
          y ^ (-3 / 2 : ℝ) * countIntegral q (0.001 * N) y (59 / 60) 1 := by
  dsimp only
  have h := equation_5_31_actual_count hN hq1
  have he := countIntegral_le_legal_height q (original_middle_base_ge_one hN)
    (a := 59 / 60) (b := 1) (y := middleHeight N q) (by norm_num) (by norm_num)
  have hs := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q) by positivity)
  linarith only [h, hs]

theorem source_middle_moving_gate_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    let g := 10000 * Real.log (q : ℝ)
    (8 * N * Real.sqrt q / q.totient) *
        (∫ y in lowHeight..middleHeight N q, y ^ (-3 / 2 : ℝ) *
          countIntegral q (0.001 * N) y (59 / 60) (sourceCutoff q 0.478 y)) ≤
      (16 * N * Real.sqrt q / q.totient) *
        ((lowHeight ^ (-(1 / 2) : ℝ) - (min (middleHeight N q) g) ^ (-(1 / 2) : ℝ)) *
            countIntegral q (0.001 * N) g (59 / 60) (sourceCutoff q 0.478 g) +
          (1 / 2 : ℝ) * ∫ y in min (middleHeight N q) g..middleHeight N q,
            y ^ (-3 / 2 : ℝ) *
              countIntegral q (0.001 * N) y (59 / 60) (sourceCutoff q 0.478 y)) := by
  dsimp only
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hg := enlarged_height_source_domain hN hq hq1
  have h := moving_countIntegral_height_gate_split hN hq (original_middle_base_ge_one hN)
    le_rfl hh.1 hg.1 (d := 0.478) (p := 1 / 2)
    (by norm_num) le_rfl (by norm_num)
  simp only [heightKernel, show -(1 / 2 : ℝ) - 1 = -3 / 2 by norm_num,
    mul_assoc, intervalIntegral.integral_const_mul] at h
  have hs := mul_le_mul_of_nonneg_left h
    (show 0 ≤ 16 * N * Real.sqrt q / q.totient by positivity)
  simp only [div_eq_mul_inv] at hs ⊢
  nlinarith only [hs]

#print axioms source_middle_gate_domain
#print axioms sigma5_endpoint_legal_height
#print axioms source_middle_moving_gate_split

end LiuWang.Proof.Campaign20260915.ThirdDomainTail
