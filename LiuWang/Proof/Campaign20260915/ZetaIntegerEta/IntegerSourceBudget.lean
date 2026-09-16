import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.CompleteSourceBudget

set_option autoImplicit false
noncomputable section
open Complex Filter Set
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta

private theorem integer_bound_of_paid_noninteger {n : ℕ} (hn : 0 < n)
    (H c : ℝ) (N k : ℕ) (ht : H < (n : ℝ) ^ 2)
    (hpaid : ∀ {eta : ℝ}, 0 ≤ eta → H < eta ^ 2 → (∀ z : ℤ, eta ≠ z) →
      ‖sourceZetaPolynomialRemainder (1 / 2) eta ⌊eta⌋₊ N‖ ≤
        c * (eta ^ (-(1 / 2 : ℝ)) / eta ^ k)) :
    ‖sourceZetaPolynomialRemainder (1 / 2) n n N‖ ≤
      c * ((n : ℝ) ^ (-(1 / 2 : ℝ)) / (n : ℝ) ^ k) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := (sourceZetaPolynomialRemainder_norm_tendsto_right (1 / 2) hn N).mono_left
    (nhdsWithin_mono _ (show Ioi (n : ℝ) ⊆ Ici (n : ℝ) by
      intro x hx
      simp only [mem_Ioi, mem_Ici] at hx ⊢
      exact hx.le))
  have hc : ContinuousAt (fun x : ℝ => c * (x ^ (-(1 / 2 : ℝ)) / x ^ k)) (n : ℝ) :=
    continuousAt_const.mul ((Real.continuousAt_rpow_const _ _ (Or.inl hn0.ne')).div
      (by fun_prop) (pow_ne_zero _ hn0.ne'))
  apply le_of_tendsto_of_tendsto hr (hc.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (n : ℝ))))
  filter_upwards [Ioo_mem_nhdsGT (show (n : ℝ) < n + 1 by linarith),
    (strict_height_eventually H n ht).filter_mono
      (nhdsWithin_le_nhds (s := Ioi (n : ℝ)))] with eta heta hH
  have hint : ∀ z : ℤ, eta ≠ z := by
    intro z hz
    have hi : (n : ℤ) < z ∧ z < (n : ℤ) + 1 := by
      exact_mod_cast (hz ▸ And.intro heta.1 heta.2)
    omega
  exact hpaid (by linarith [heta.1]) hH hint

theorem complete_source_R0_integer {n : ℕ} (hn : 0 < n) (ht : 125 < (n : ℝ) ^ 2) :
    ‖sourceZetaPolynomialRemainder (1 / 2) n n 1‖ ≤
      (371 / 500) * ((n : ℝ) ^ (-(1 / 2 : ℝ)) / (n : ℝ)) := by
  simpa only [pow_one] using integer_bound_of_paid_noninteger hn 125 (371 / 500) 1 1 ht
    (fun he hH hint => by simpa only [pow_one] using complete_source_R0_noninteger he hH hint)

theorem complete_source_R2_integer {n : ℕ} (hn : 0 < n) (ht : 2000 < (n : ℝ) ^ 2) :
    ‖sourceZetaPolynomialRemainder (1 / 2) n n 7‖ ≤
      (129 / 125) * ((n : ℝ) ^ (-(1 / 2 : ℝ)) / (n : ℝ) ^ 3) :=
  integer_bound_of_paid_noninteger hn 2000 (129 / 125) 7 3 ht
    (fun he hH hint => complete_source_R2_noninteger he hH hint)

private theorem nat_endpoint_of_integer {eta : ℝ} (he : 0 ≤ eta)
    (hi : ¬ ∀ z : ℤ, eta ≠ z) : ∃ n : ℕ, eta = n := by
  push Not at hi
  obtain ⟨z, hz⟩ := hi
  have hz0 : 0 ≤ z := by exact_mod_cast (hz ▸ he)
  refine ⟨z.toNat, ?_⟩
  have h : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
  exact hz.trans (by exact_mod_cast h.symm)

theorem complete_source_R0_all {eta : ℝ} (he : 0 ≤ eta) (ht : 125 < eta ^ 2) :
    ‖sourceZetaPolynomialRemainder (1 / 2) eta ⌊eta⌋₊ 1‖ ≤
      (371 / 500) * (eta ^ (-(1 / 2 : ℝ)) / eta) := by
  by_cases hint : ∀ z : ℤ, eta ≠ z
  · exact complete_source_R0_noninteger he ht hint
  · obtain ⟨n, rfl⟩ := nat_endpoint_of_integer he hint
    rw [Nat.floor_natCast]
    exact complete_source_R0_integer (by
      have hn0 : (0 : ℝ) < n := by nlinarith
      exact_mod_cast hn0) ht

theorem complete_source_R2_all {eta : ℝ} (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) :
    ‖sourceZetaPolynomialRemainder (1 / 2) eta ⌊eta⌋₊ 7‖ ≤
      (129 / 125) * (eta ^ (-(1 / 2 : ℝ)) / eta ^ 3) := by
  by_cases hint : ∀ z : ℤ, eta ≠ z
  · exact complete_source_R2_noninteger he ht hint
  · obtain ⟨n, rfl⟩ := nat_endpoint_of_integer he hint
    rw [Nat.floor_natCast]
    exact complete_source_R2_integer (by
      have hn0 : (0 : ℝ) < n := by nlinarith
      exact_mod_cast hn0) ht

theorem complete_source_R0_margin {eta : ℝ} (he : 0 ≤ eta) (ht : 125 < eta ^ 2) :
    ‖sourceZetaPolynomialRemainder (1 / 2) eta ⌊eta⌋₊ 1‖ +
      (1 / 125) * (eta ^ 2) ^ (-(3 / 4 : ℝ)) ≤
        (3 / 4) * (eta ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have h := complete_source_R0_all he ht
  have he0 : 0 < eta := by nlinarith
  have hs := source_error_scale_original he0 1
  norm_num only [pow_one, Nat.cast_one] at hs
  rw [hs] at h
  linarith

theorem complete_source_R2_margin {eta : ℝ} (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) :
    ‖sourceZetaPolynomialRemainder (1 / 2) eta ⌊eta⌋₊ 7‖ +
      (27 / 250) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) ≤
        (57 / 50) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) := by
  have h := complete_source_R2_all he ht
  have he0 : 0 < eta := by nlinarith
  have hs := source_error_scale_original he0 3
  norm_num only [Nat.cast_ofNat] at hs
  rw [hs] at h
  linarith

theorem complete_source_R0_strict {eta : ℝ} (he : 0 ≤ eta) (ht : 125 < eta ^ 2) :
    2 * ‖sourceZetaPolynomialRemainder (1 / 2) eta ⌊eta⌋₊ 1‖ <
      (3 / 2) * (eta ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have h := complete_source_R0_margin he ht
  have hp := Real.rpow_pos_of_pos (show 0 < eta ^ 2 by linarith) (-(3 / 4 : ℝ))
  linarith

theorem complete_source_R2_strict {eta : ℝ} (he : 0 ≤ eta) (ht : 2000 < eta ^ 2) :
    2 * ‖sourceZetaPolynomialRemainder (1 / 2) eta ⌊eta⌋₊ 7‖ <
      (57 / 25) * (eta ^ 2) ^ (-(7 / 4 : ℝ)) := by
  have h := complete_source_R2_margin he ht
  have hp := Real.rpow_pos_of_pos (show 0 < eta ^ 2 by linarith) (-(7 / 4 : ℝ))
  linarith

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
