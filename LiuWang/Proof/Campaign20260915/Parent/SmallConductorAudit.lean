import LiuWang.Proof.WeightedLowZeros.Continuation.PaperSource
import LiuWang.Proof.Campaign20260915.SmallConductors.Through150
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Batch978_986
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q168.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q840.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q924.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q977.Consumer

set_option autoImplicit false
noncomputable section
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros.Continuation LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.Campaign20260915.Parent.SmallConductorAudit

theorem paper_source_conductor_ge_151 {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    151 ≤ (d.modulus : ℝ) := by
  have he : (e.re : ℂ) = e := by
    apply Complex.ext <;> simp [hd.2.2.1]
  have h := SmallConductors.original_source_unpaid150 d
    (sourceP_ge_ten (exp_2000_le_of_exp_3100_le hN)) hd.1 hd.2.2.2.2.le
    (by simpa only [he] using hd.2.1)
  exact_mod_cast h.1

#print axioms paper_source_conductor_ge_151
end LiuWang.Proof.Campaign20260915.Parent.SmallConductorAudit

#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.primitive_le_onehundredfifty_original_region
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.original_source_unpaid150
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.actual_exceptional_conductor_restrictions150
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.Fast.range_978_986
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q168.original_region
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q840.original_region
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q924.original_region
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q977.original_region
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q979.original_region
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q983.original_region
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q984.original_region
#print axioms LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q985.original_region
