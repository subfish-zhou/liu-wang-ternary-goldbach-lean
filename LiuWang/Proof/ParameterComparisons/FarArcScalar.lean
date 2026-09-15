import LiuWang.Proof.ArcGeometry.Main
import LiuWang.Proof.ParameterComparisons.VaughanRange

/-! Join the actual far-arc rational approximation to the proved scalar budget.
The analytic inequality bounding `S` by this majorant remains a separate input. -/
set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.ParameterComparisons
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.ArcGeometry

/-- The literal three-term majorant in the source Vaughan estimate. -/
def vaughanMajorant (N : ℕ) (q : ℝ) : ℝ :=
  (0.28 : ℝ) * (N : ℝ) * q ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ) +
    4 * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) +
    (0.09 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2) *
      sourceL N ^ ((5 : ℝ) / 2)

/-- One actual far-arc approximation supplies both the source `1/q²` parameter
and the small majorant; the witnesses are not selected independently. -/
theorem M4_exists_vaughan_approximation {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ∃ (q a : ℕ) (θ : ℝ), sourceP1 N < (q : ℝ) ∧ (q : ℝ) ≤ sourceQ N ∧
      sourceIndex a q ∧ |θ| ≤ 1 ∧
      α = rationalCenter a q + θ / (q : ℝ) ^ (2 : ℕ) ∧
      vaughanMajorant N q ≤ (0.294 : ℝ) * (N : ℝ) / sourceL N := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  obtain ⟨q, a, hqL, hqU, hi, ha⟩ := M4_rational_approximation h2000 hα
  have hq : (0 : ℝ) < q := by exact_mod_cast sourceIndex_den_pos hi
  have hq2 : (0 : ℝ) < (q : ℝ) ^ (2 : ℕ) := pow_pos hq _
  have hr : 1 / ((q : ℝ) * sourceQ N) ≤ 1 / (q : ℝ) ^ (2 : ℕ) :=
    one_div_le_one_div_of_le hq2 (by nlinarith)
  have he := ((mem_approximationArc_iff N a q α).mp ha).trans hr
  refine ⟨q, a, (α - rationalCenter a q) * (q : ℝ) ^ (2 : ℕ),
    hqL, hqU, hi, ?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hq2]
    exact (le_div_iff₀ hq2).mp he
  · rw [mul_div_cancel_right₀ _ hq2.ne']
    ring
  · exact vaughan_scalar_range_margin hN hqL.le hqU

end LiuWang.Proof.ParameterComparisons
