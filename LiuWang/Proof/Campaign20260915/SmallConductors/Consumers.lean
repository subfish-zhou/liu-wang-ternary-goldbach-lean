import LiuWang.Proof.Campaign20260915.SmallConductors.Coverage
import LiuWang.Proof.MajorZeroInteraction.Exceptional

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.SmallConductorExpansion
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.Campaign20260915.SmallConductors

theorem actual_exceptional_conductor_restrictions {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    84 ≤ chi.conductor ∧ chi.conductor ≠ 163 ∧ chi.conductor % 4 ≠ 2 ∧
      ¬16 ∣ chi.conductor ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p ^ 2 ∣ chi.conductor := by
  classical
  have hN' := exp_2000_le_of_exp_3100_le hN
  obtain ⟨d, hd, hdc, _, hdz, _⟩ := exceptionalValues_same_source hN' hq hr
  have hi := (exceptionalValues_quadratic_simple hN' hq hr).2.2.1
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  have hreg := (Finset.mem_filter.mp hr).2
  have hb := r24_re_in_original_real_region (sourceP_ge_ten hN') hreg.1
  have hbound := original_source_unpaid83 d (sourceP_ge_ten hN') hd hb
    (by simpa only [he] using hdz)
  simpa only [hdc] using hbound

#print axioms actual_exceptional_conductor_restrictions

end LiuWang.Proof.Campaign20260915.SmallConductors
