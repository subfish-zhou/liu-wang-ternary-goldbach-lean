import LiuWang.Proof.Campaign20260915.Totient.ProductKeyWindows
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LiuWang.Proof.Campaign20260915.Totient
noncomputable section
private theorem unitsFrom_mem_of_key (rs : List (ℕ × ℤ)) (p : ℕ)
    (h : p ∈ rs.map Prod.fst) : (p, unitsFrom rs p) ∈ rs := by
  induction rs with
  | nil => simp at h
  | cons r rs ih =>
    rcases r with ⟨q, u⟩
    simp only [List.map_cons, List.mem_cons] at h
    by_cases he : p = q
    · subst p
      simp [unitsFrom]
    · have ht := ih (h.resolve_left he)
      simp only [unitsFrom, if_neg he, List.mem_cons]
      exact Or.inr ht

private theorem log_row_lookup {p : ℕ} (hp : p.Prime) (hlo : 286 ≤ p) (hhi : p ≤ 1420) :
    (p, unitsFrom thetaLogRows p) ∈ thetaLogRows ∧ logScale (p : ℚ) ≤ 10 := by
  have hk := product_keys_complete hlo hhi hp
  refine ⟨unitsFrom_mem_of_key _ _ hk, ?_⟩
  have hlog := Nat.log_mono_right (b := 2) hhi
  have hb : Nat.log 2 1420 ≤ 10 := by decide +kernel
  simpa only [logScale, Nat.floor_natCast] using hlog.trans hb

#check log_row_lookup

theorem log_units_bounds {p : ℕ} (hp : p.Prime) (hlo : 286 ≤ p) (hhi : p ≤ 1420) :
    (unitsFrom thetaLogRows p : ℝ) / 10000000000 ≤ Real.log p ∧
      Real.log p ≤ (unitsFrom thetaLogRows p + 61 : ℝ) / 10000000000 := by
  obtain ⟨hr, hs⟩ := log_row_lookup hp hlo hhi
  have hu := (theta_log_rows_checked _ hr).2
  have h := rational_log_bounds (x := (p : ℚ)) (by exact_mod_cast hp.one_lt.le)
  unfold logHi logLo at h
  rw [← hu] at h
  push_cast at h
  have hsR : (logScale (p : ℚ) : ℝ) ≤ 10 := by exact_mod_cast hs
  constructor
  · exact h.1
  · linarith [h.2]


end
end LiuWang.Proof.Campaign20260915.Totient
