import LiuWang.Proof.Campaign20260915.ZetaGramBlocks.GramBlocks

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaGramBlocks

theorem log_two_pi_lower : 89 / 50 < Real.log (2 * Real.pi) := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 * 3)
    (show (2 : ℝ) * 3 ≤ 2 * Real.pi by linarith [Real.pi_gt_three])
  rw [Real.log_mul (by norm_num) (by norm_num)] at h
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

theorem brent_threshold_implies_lehman_criterion {T K d : ℝ}
    (hT : 168 * Real.pi < T) (hspan : K ≤ d)
    (hK : 0.0061 * (Real.log T) ^ 2 + 0.08 * Real.log T ≤ K) :
    0.152 * Real.log (T / (2 * Real.pi)) +
      0.0091 * (Real.log (T / (2 * Real.pi))) ^ 2 < K + d / 2 := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hT0 : 0 < T := lt_trans (by positivity) hT
  have hratio : 1 ≤ T / (2 * Real.pi) := by
    rw [le_div_iff₀ hp]
    linarith [Real.pi_pos]
  have hx : 0 ≤ Real.log (T / (2 * Real.pi)) := Real.log_nonneg hratio
  have he := Real.log_div hT0.ne' hp.ne'
  have hl : Real.log (T / (2 * Real.pi)) + 89 / 50 < Real.log T := by
    rw [he]
    linarith [log_two_pi_lower]
  have hs : (Real.log (T / (2 * Real.pi)) + 89 / 50) ^ 2 ≤ (Real.log T) ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg (Real.log (T / (2 * Real.pi)))]

theorem consecutive_blocks_lehman_criterion {g : ℤ → ℝ} (v : ℕ → ℤ) (K : ℕ)
    (hB : ∀ j < K, IsGramBlock g (v j) (v (j + 1)))
    (hT : 168 * Real.pi < g (v K))
    (hK : 0.0061 * (Real.log (g (v K))) ^ 2 +
      0.08 * Real.log (g (v K)) ≤ (K : ℝ)) :
    0.152 * Real.log (g (v K) / (2 * Real.pi)) +
      0.0091 * (Real.log (g (v K) / (2 * Real.pi))) ^ 2 <
        (K : ℝ) + ((v K : ℝ) - v 0) / 2 := by
  apply brent_threshold_implies_lehman_criterion hT _ hK
  exact_mod_cast consecutive_block_span v K hB

#print axioms brent_threshold_implies_lehman_criterion
#print axioms consecutive_blocks_lehman_criterion

end LiuWang.Proof.Campaign20260915.ZetaGramBlocks
