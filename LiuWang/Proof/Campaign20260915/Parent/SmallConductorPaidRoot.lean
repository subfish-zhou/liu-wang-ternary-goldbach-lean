import LiuWang.Proof.Campaign20260915.Parent.DensityPaidRoot
import LiuWang.Proof.Campaign20260915.SmallConductors.All

/-! Original large-odd-N root with density and small-conductor inputs discharged.
Two mathematical inputs remain: finite-height zeta verification and global totient.
Neither the unconditional large-N theorem nor the below-threshold range is claimed.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open LiuWang.Proof.Interfaces
namespace LiuWang.Proof.Campaign20260915.Parent.SmallConductorPaidRoot

theorem threeOddPrimes_of_two_shared_inputs {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hzeta : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      16 < |s.im| → |s.im| < 1894438 → s.re = 1 / 2)
    (htotient : ∀ q : ℕ, 3 ≤ q → (q : ℝ) / (q.totient : ℝ) ≤
      LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.nu q) :
    LiuWang.IsThreeOddPrimeSum N := by
  apply DensityPaidRoot.threeOddPrimes_of_three_shared_inputs hN hodd hzeta htotient
  intro q _ chi hp hc hsq x beta hx hqx hb hz
  by_contra h
  exact SmallConductors.primitive_le_986_original_region (by omega)
    chi hp hc hsq hx hqx hb hz

#print threeOddPrimes_of_two_shared_inputs
#print axioms threeOddPrimes_of_two_shared_inputs
end LiuWang.Proof.Campaign20260915.Parent.SmallConductorPaidRoot

#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.primitive_le_986_original_region
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.original_source_conductor_ge_987
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.actual_exceptional_conductor_ge_987
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.paper_source_conductor_ge_987
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.actual_exceptional_gap_paid
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.actual_pure_integrals_conductor_paid
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.actual_mixed_totals_conductor_paid
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.caseII_conductor_paid
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.localC1Data_exists
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.equation_5_27_local_region_paid
