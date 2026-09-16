import LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.PositiveKernel
import LiuWang.Proof.Campaign20260915.LowZeroMoment.AllZerosFourteen

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.ZetaMomentTransport
open LiuWang.Proof.Campaign20260915.LowZeroMoment

namespace LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel

def windowMomentCost {n : ℕ} (lo : Fin n → ℚ) (cap : Fin n → ℕ) : ℚ :=
  ∑ i, (cap i : ℚ) / (max 14 (lo i)) ^ 2

theorem positive_interval_count {a b : ℝ} (hab : a ≤ b) :
    (∑ z ∈ (positiveValues b).filter (fun z => a < z.im),
      analyticOrderNatAt riemannZeta z) = positiveCount b - positiveCount a := by
  classical
  have he : (positiveValues b).filter (fun z => ¬ a < z.im) = positiveValues a := by
    ext z
    simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨hz, ha⟩
      obtain ⟨hz, h0, h1, hp, _⟩ := mem_positiveValues.mp hz
      exact mem_positiveValues.mpr ⟨hz, h0, h1, hp, ha⟩
    · intro hz
      obtain ⟨hz, h0, h1, hp, ha⟩ := mem_positiveValues.mp hz
      exact ⟨mem_positiveValues.mpr ⟨hz, h0, h1, hp, ha.trans hab⟩, ha⟩
  have hs := Finset.sum_filter_add_sum_filter_not (positiveValues b)
    (fun z : ℂ => a < z.im) (analyticOrderNatAt riemannZeta)
  rw [he] at hs
  change _ + positiveCount a = positiveCount b at hs
  omega

theorem positive_clipped_interval_count {H a b : ℝ} (hab : a ≤ b) :
    (∑ z ∈ (positiveValues H).filter (fun z => a < z.im ∧ z.im ≤ b),
      analyticOrderNatAt riemannZeta z) ≤ positiveCount b - positiveCount a := by
  classical
  rw [← positive_interval_count hab]
  apply Finset.sum_le_sum_of_subset
  intro z hz
  obtain ⟨hz, ha, hb⟩ := Finset.mem_filter.mp hz
  obtain ⟨hz, h0, h1, hp, _⟩ := mem_positiveValues.mp hz
  exact Finset.mem_filter.mpr ⟨mem_positiveValues.mpr ⟨hz, h0, h1, hp, hb⟩, ha⟩

theorem positive_clipped_interval_moment {H a b : ℝ} {c : ℕ} (hab : a ≤ b)
    (hc : positiveCount b - positiveCount a ≤ c) :
    (∑ z ∈ (positiveValues H).filter (fun z => a < z.im ∧ z.im ≤ b),
      (analyticOrderNatAt riemannZeta z : ℝ) / z.im ^ 2) ≤
        c / (max 14 a) ^ 2 := by
  classical
  have hd : 0 < max (14 : ℝ) a := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  calc
    _ ≤ ∑ z ∈ (positiveValues H).filter (fun z => a < z.im ∧ z.im ≤ b),
        (analyticOrderNatAt riemannZeta z : ℝ) / (max 14 a) ^ 2 := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hz, ha, _⟩ := Finset.mem_filter.mp hz
      obtain ⟨hz, h0, h1, hp, _⟩ := mem_positiveValues.mp hz
      have ht := zeta_zero_height_gt_fourteen hz h0 h1
      rw [abs_of_pos hp] at ht
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (sq_pos_of_pos hd)
        (pow_le_pow_left₀ hd.le (max_le ht.le ha.le) 2)
    _ = ((∑ z ∈ (positiveValues H).filter (fun z => a < z.im ∧ z.im ≤ b),
        analyticOrderNatAt riemannZeta z : ℕ) : ℝ) / (max 14 a) ^ 2 := by
      rw [Nat.cast_sum, Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right
      (Nat.cast_le.mpr ((positive_clipped_interval_count hab).trans hc)) (sq_nonneg _)

/-- Overlaps are allowed and conservatively charged twice; no simplicity is assumed. -/
theorem positive_finite_window_moment {n : ℕ} (H : ℝ)
    (lo hi : Fin n → ℚ) (cap : Fin n → ℕ)
    (hinterval : ∀ i, lo i ≤ hi i)
    (hcover : ∀ z ∈ positiveValues H, ∃ i, (lo i : ℝ) < z.im ∧ z.im ≤ (hi i : ℝ))
    (hcount : ∀ i, positiveCount (hi i) - positiveCount (lo i) ≤ cap i) :
    (∑ z ∈ positiveValues H, (analyticOrderNatAt riemannZeta z : ℝ) / z.im ^ 2) ≤
      (windowMomentCost lo cap : ℝ) := by
  classical
  calc
    _ ≤ ∑ z ∈ positiveValues H, ∑ i : Fin n,
        if (lo i : ℝ) < z.im ∧ z.im ≤ (hi i : ℝ) then
          (analyticOrderNatAt riemannZeta z : ℝ) / z.im ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨i, hi⟩ := hcover z hz
      have hs := Finset.single_le_sum (s := Finset.univ) (a := i)
        (f := fun j : Fin n => if (lo j : ℝ) < z.im ∧ z.im ≤ (hi j : ℝ) then
          (analyticOrderNatAt riemannZeta z : ℝ) / z.im ^ 2 else 0)
        (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
      simpa only [if_pos hi] using hs
    _ = ∑ i : Fin n, ∑ z ∈ (positiveValues H).filter
        (fun z => (lo i : ℝ) < z.im ∧ z.im ≤ (hi i : ℝ)),
          (analyticOrderNatAt riemannZeta z : ℝ) / z.im ^ 2 := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ i : Fin n, (cap i : ℝ) / (max 14 (lo i : ℝ)) ^ 2 :=
      Finset.sum_le_sum (fun i _ =>
        positive_clipped_interval_moment (Rat.cast_le.mpr (hinterval i)) (hcount i))
    _ = _ := by
      unfold windowMomentCost
      push_cast
      rfl

theorem closed_moment_eq_two_positive (H : ℝ) :
    (∑' p, closedMomentTerm H 0 p) =
      2 * ∑ z ∈ positiveValues H, (analyticOrderNatAt riemannZeta z : ℝ) / z.im ^ 2 := by
  have h := sum_closed_eq_two_positive H (fun z : ℂ => 1 / z.im ^ 2) (fun z => by simp)
  have ht := tsum_closed_eq_sum H (fun z : ℂ => 1 / z.im ^ 2)
  simpa [closedMomentTerm, rsZeroMoment, sq_abs, mul_one_div] using ht.trans h

theorem closed_moment_le_window_cost {n : ℕ} (H : ℝ)
    (lo hi : Fin n → ℚ) (cap : Fin n → ℕ)
    (hinterval : ∀ i, lo i ≤ hi i)
    (hcover : ∀ z ∈ positiveValues H, ∃ i, (lo i : ℝ) < z.im ∧ z.im ≤ (hi i : ℝ))
    (hcount : ∀ i, positiveCount (hi i) - positiveCount (lo i) ≤ cap i) :
    (∑' p, closedMomentTerm H 0 p) ≤ 2 * (windowMomentCost lo cap : ℝ) := by
  rw [closed_moment_eq_two_positive]
  exact mul_le_mul_of_nonneg_left
    (positive_finite_window_moment H lo hi cap hinterval hcover hcount) (by norm_num)

#print axioms positive_interval_count
#print axioms positive_finite_window_moment
#print axioms closed_moment_le_window_cost

end LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel
