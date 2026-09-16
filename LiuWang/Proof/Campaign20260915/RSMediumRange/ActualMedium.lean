import LiuWang.Proof.Campaign20260915.RSMediumRange.FullCertificate
import LiuWang.Proof.Campaign20260915.RSMediumRange.StartAndTransport
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.UpperFinite

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

theorem actual_medium_start : Chunk0000Start.Actual :=
  medium_start_actual RSFiniteExtension.medium_start.1
    RSFiniteExtension.theta_16000_enclosure.2 RSFiniteExtension.medium_start.2

theorem actual_medium_bounds {x : ℝ} (hx : 16000 ≤ x) (hi : x ≤ 100000000) :
    MediumBounds x :=
  fullMediumBounds_of_start actual_medium_start x hx hi

theorem theta_theorem19_medium {x : ℝ} (hx : 16000 ≤ x) (hi : x ≤ 100000000) :
    x - 2 * Real.sqrt x < Chebyshev.theta x :=
  (actual_medium_bounds hx hi).1.1

theorem theta_theorem18_medium {x : ℝ} (hx : 16000 ≤ x) (hi : x ≤ 100000000) :
    x - 2.05282 * Real.sqrt x < Chebyshev.theta x ∧ Chebyshev.theta x < x := by
  have h := (actual_medium_bounds hx hi).1
  exact ⟨by nlinarith [Real.sqrt_nonneg x, h.1], h.2⟩

theorem theta_3_14_medium {x : ℝ} (hx : 16000 ≤ x) (hi : x ≤ 100000000) :
    x * (1 - 1 / (2 * Real.log x)) < Chebyshev.theta x :=
  theta_3_14_from_medium hx (theta_theorem19_medium hx hi)

theorem theorem23_upper_medium {x : ℝ} (hx : 16000 ≤ x) (hi : x ≤ 100000000) :
    (∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / (p - 1)) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  have h := (actual_medium_bounds hx hi).2.1
  unfold Totient.prefixEuler at h
  push_cast at h
  convert h using 1
  ring

theorem product_3_29_medium {x : ℝ} (hx : 16000 ≤ x) (hi : x ≤ 100000000) :
    (∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / (p - 1)) <
      Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * Real.log x ^ 2)) := by
  have h := (actual_medium_bounds hx hi).2.2
  rw [product_envelope_source_form hx] at h
  unfold Totient.prefixEuler at h
  push_cast at h
  exact h

theorem medium_consumers_paid :
    ∀ x : ℝ, 16000 ≤ x → x ≤ 100000000 →
      (x - 2 * Real.sqrt x < Chebyshev.theta x ∧ Chebyshev.theta x < x) ∧
      (∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / (p - 1)) <
        Real.exp Real.eulerMascheroniConstant * Real.log x +
          2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x ∧
      (∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / (p - 1)) <
        Real.exp Real.eulerMascheroniConstant * Real.log x *
          (1 + 1 / (2 * Real.log x ^ 2)) := by
  intro x hx hi
  exact ⟨(actual_medium_bounds hx hi).1, theorem23_upper_medium hx hi,
    product_3_29_medium hx hi⟩

#print axioms actual_medium_start
#print axioms theta_theorem19_medium
#print axioms theta_theorem18_medium
#print axioms theta_3_14_medium
#print axioms theorem23_upper_medium
#print axioms product_3_29_medium
#print axioms medium_consumers_paid

end LiuWang.Proof.Campaign20260915.RSMediumRange
