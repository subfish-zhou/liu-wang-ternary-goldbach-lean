import LiuWang.Proof.Campaign20260915.Totient.RSAnalyticAudit

/-! Parent consumption of the exact-R high-zero region and effective integral.
No full sharp counting estimate, Table I, or global totient bound is asserted.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open BombieriVinogradov.SiegelWalfisz MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.Parent.TotientRSAnalyticAudit
open LiuWang.Proof.Campaign20260915.Totient

theorem actual_high_zero_region (p : RiemannXiDivisorZeroIndex)
    (ht : rsA ≤ |(riemannXiDivisorZeroValue p).im|) :
    1 / (rsR * Real.log |(riemannXiDivisorZeroValue p).im|) <
      1 - (riemannXiDivisorZeroValue p).re :=
  rs_zero_gap p ht

theorem actual_weighted_integral {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 ≤ L)
    (hupper : L < 1748 * (m : ℝ) ^ 2 / ((m : ℝ) + 0.123)) :
    IntegrableOn (fun t => rsPhi m L t * Real.log (t / (2 * Real.pi))) (Ioi rsA) ∧
    rsQ rsA * (∫ t in Ioi rsA, rsPhi m L t * Real.log (t / (2 * Real.pi))) ≤
      (1.298 * (m : ℝ) + 0.1592) /
        ((1 - ((m : ℝ) + 0.123) * L / (1748 * (m : ℝ) ^ 2)) *
          (m : ℝ) ^ 2 * rsA ^ m * Real.exp (L / 175)) :=
  ⟨(rs_phi_integral_original hm hL hupper).1, rsQ_phi_integral_original hm hL hupper⟩

#print axioms actual_high_zero_region
#print axioms actual_weighted_integral
end LiuWang.Proof.Campaign20260915.Parent.TotientRSAnalyticAudit
