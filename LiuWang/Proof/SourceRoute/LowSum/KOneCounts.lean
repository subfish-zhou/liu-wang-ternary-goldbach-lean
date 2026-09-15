import LiuWang.Proof.SourceRoute.LowSum.KOneNumerics

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.LowSum

theorem counting_integral_le_open {ι : Type*} [Fintype ι] {N : ℕ} (hN : 0 < N)
    (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ) {a b D : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hcount : ∀ alpha ∈ Set.Ioo a b, countingFunction Z m alpha ≤ D) :
    (∫ alpha in a..b, kernel N alpha * countingFunction Z m alpha) ≤
      ∫ alpha in a..b, D * kernel N alpha := by
  apply intervalIntegral.integral_mono_on_of_le_Ioo hab
    (counting_integrand_integrable hN ha hab Z m) ((kernel_integrable hN ha hab).const_mul D)
  intro alpha halpha
  rw [mul_comm D]
  exact mul_le_mul_of_nonneg_left (hcount alpha halpha) (kernel_nonneg hN (ha.trans halpha.1))

theorem counting_integral_two_pieces {ι : Type*} [Fintype ι] {N : ℕ} (hN : 0 < N)
    (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ) {a c b D E : ℝ}
    (ha : 0 < a) (hac : a ≤ c) (hcb : c ≤ b)
    (hD : ∀ alpha ∈ Set.Ioo a c, countingFunction Z m alpha ≤ D)
    (hE : ∀ alpha ∈ Set.Ioo c b, countingFunction Z m alpha ≤ E) :
    (∫ alpha in a..b, kernel N alpha * countingFunction Z m alpha) ≤
      (∫ alpha in a..c, D * kernel N alpha) + ∫ alpha in c..b, E * kernel N alpha := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (counting_integrand_integrable hN ha hac Z m)
    (counting_integrand_integrable hN (ha.trans_le hac) hcb Z m)]
  exact add_le_add (counting_integral_le_open hN Z m ha hac hD)
    (counting_integral_le_open hN Z m (ha.trans_le hac) hcb hE)

theorem original_K1_small_from_counts {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ)
    (h13 : countingFunction Z m (cap N 0.33) ≤ 13)
    (h2 : ∀ alpha ∈ Set.Ioo (cap N 0.3221) (paperCap N), countingFunction Z m alpha ≤ 2) :
    (∫ alpha in cap N 0.33..paperCap N, kernel N alpha * countingFunction Z m alpha) ≤
      0.0104 / sourceL N := by
  have hcap : cap N 0.3221 ≤ paperCap N := by
    apply (cap_order hN (by norm_num : (0.11 : ℝ) ≤ 0.3221)).trans
    dsimp [cap, paperCap]
    linarith [paper_gap_le_low_gap hN]
  apply le_trans _ (original_K1_small hN)
  exact counting_integral_two_pieces (nat_pos_of_exp_le hN) Z m
    (by linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)])
    (cap_order hN (by norm_num)) hcap
    (fun _ halpha => (countingFunction_antitone Z m halpha.1.le).trans h13) h2

theorem original_K1_middle_from_counts {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ)
    (h13 : countingFunction Z m (cap N 0.33) ≤ 13)
    (h2 : ∀ alpha ∈ Set.Ioo (cap N 0.2743) (cap N 0.12), countingFunction Z m alpha ≤ 2) :
    (∫ alpha in cap N 0.33..cap N 0.12, kernel N alpha * countingFunction Z m alpha) ≤
      0.0027 / sourceL N := by
  apply le_trans _ (original_K1_middle hN)
  exact counting_integral_two_pieces (nat_pos_of_exp_le hN) Z m
    (by linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)])
    (cap_order hN (by norm_num)) (cap_order hN (by norm_num))
    (fun _ halpha => (countingFunction_antitone Z m halpha.1.le).trans h13) h2

theorem original_K1_last_from_counts {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ)
    (h13 : countingFunction Z m (cap N 0.33) ≤ 13)
    (h4 : ∀ alpha ∈ Set.Ioo (cap N 0.26213) (cap N 0.2067), countingFunction Z m alpha ≤ 4)
    (h2 : ∀ alpha ∈ Set.Ioo (cap N 0.2067) (cap N 0.15), countingFunction Z m alpha ≤ 2) :
    (∫ alpha in cap N 0.33..cap N 0.15, kernel N alpha * countingFunction Z m alpha) ≤
      0.0001 / sourceL N := by
  have hn := nat_pos_of_exp_le hN
  have hpos : 0 < cap N 0.33 := by linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)]
  have hmid : 0 < cap N 0.2067 := by linarith [cap_ge_098 hN (by norm_num : (0.2067 : ℝ) ≤ 0.478)]
  have hi := counting_integral_two_pieces hn Z m hpos
    (cap_order hN (by norm_num : (0.26213 : ℝ) ≤ 0.33))
    (cap_order hN (by norm_num : (0.2067 : ℝ) ≤ 0.26213))
    (fun _ halpha => (countingFunction_antitone Z m halpha.1.le).trans h13) h4
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (counting_integrand_integrable hn hpos (cap_order hN (by norm_num)) Z m)
    (counting_integrand_integrable hn hmid (cap_order hN (by norm_num)) Z m)]
  exact (add_le_add hi
    (counting_integral_le_open hn Z m hmid (cap_order hN (by norm_num)) h2)).trans (original_K1_last hN)

end LiuWang.Proof.SourceRoute.LowSum
