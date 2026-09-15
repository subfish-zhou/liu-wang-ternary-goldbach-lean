import LiuWang.Proof.Campaign20260915.RSMertensTransport.SharpTail

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.Mertens

namespace LiuWang.Proof.Campaign20260915.RSMertensTransport

theorem logarithmicCorrection_tail_eq_prime_tsum {x : ℝ} (hx : 0 ≤ x) :
    logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊ =
      ∑' p : ℕ, if p.Prime ∧ x < (p : ℝ) then
        -Real.log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ) else 0 := by
  classical
  have hs := summable_logarithmicCorrectionTerm.sum_add_tsum_compl
    (s := Finset.range (⌊x⌋₊ + 1))
  rw [← logarithmicCorrection_eq_sum_range, tsum_subtype] at hs
  have heq :
      (∑' p : ℕ, ((Finset.range (⌊x⌋₊ + 1) : Set ℕ)ᶜ).indicator
        logarithmicCorrectionTerm p) =
      ∑' p : ℕ, if p.Prime ∧ x < (p : ℝ) then
        -Real.log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ) else 0 := by
    apply tsum_congr
    intro p
    have hcut : p ∉ Finset.range (⌊x⌋₊ + 1) ↔ x < (p : ℝ) := by
      simpa only [Finset.mem_range, not_lt, Nat.add_one_le_iff] using
        (Nat.floor_lt hx : ⌊x⌋₊ < p ↔ x < (p : ℝ))
    simp only [Set.indicator_apply, Set.mem_compl_iff, Finset.mem_coe, hcut,
      logarithmicCorrectionTerm]
    split_ifs <;> simp_all
  rw [heq] at hs
  change logarithmicCorrection ⌊x⌋₊ + _ = logarithmicCorrectionLimit at hs
  linarith

theorem logarithmicCorrection_tail_eq_prime_power_tsum {x : ℝ} (hx : 0 ≤ x) :
    logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊ =
      ∑' p : ℕ, if p.Prime ∧ x < (p : ℝ) then
        ∑' k : ℕ, (1 / (p : ℝ)) ^ (k + 2) / (k + 2) else 0 := by
  rw [logarithmicCorrection_tail_eq_prime_tsum hx]
  apply tsum_congr
  intro p
  split_ifs with hp
  · simpa only [logarithmicCorrectionTerm, if_pos hp.1] using
      (hasSum_logarithmicCorrection_prime hp.1).tsum_eq.symm
  · rfl

theorem original_signed_log_tail_eq {x : ℝ} (hx : 0 ≤ x) :
    (∑' p : ℕ, if p.Prime ∧ x < (p : ℝ) then
      Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) else 0) =
      -(logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊) := by
  rw [logarithmicCorrection_tail_eq_prime_tsum hx, ← tsum_neg]
  apply tsum_congr
  intro p
  split_ifs <;> ring

theorem original_signed_log_tail_bounds_of_theta {x : ℝ} (hx : 1 < x)
    (htheta : ∀ t ∈ Set.Ici x, Chebyshev.theta t ≤ 1.02 * t) :
    -1.02 / ((x - 1) * Real.log x) ≤
      (∑' p : ℕ, if p.Prime ∧ x < (p : ℝ) then
        Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) else 0) ∧
      (∑' p : ℕ, if p.Prime ∧ x < (p : ℝ) then
        Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) else 0) ≤ 0 := by
  rw [original_signed_log_tail_eq (by linarith : 0 ≤ x)]
  have hb := logarithmicCorrection_tail_le_original_of_theta hx htheta
  constructor
  · simpa only [neg_div] using neg_le_neg hb.2
  · exact neg_nonpos.mpr hb.1

#print axioms logarithmicCorrection_tail_eq_prime_tsum
#print axioms logarithmicCorrection_tail_eq_prime_power_tsum
#print axioms original_signed_log_tail_bounds_of_theta

end LiuWang.Proof.Campaign20260915.RSMertensTransport
