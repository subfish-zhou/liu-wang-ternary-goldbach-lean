import LiuWang.Proof.Campaign20260915.ZetaGramBlocks.GramPoints
import LiuWang.Proof.Campaign20260915.ZetaMomentTransport.Multiplicity

/-! Explicitly accepted frozen interfaces for cross-lane consumption.
These are general Gram-point and multiplicity-transport tools, not numerical certificates.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.Campaign20260915.Parent.CrossLaneHandoff
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaGramBlocks
open LiuWang.Proof.Campaign20260915.ZetaMomentTransport

theorem gram_exists {n : ℤ} {a b : ℝ} (hab : a < b)
    (ha : criticalGammaArgument a < n * Real.pi)
    (hb : n * Real.pi < criticalGammaArgument b) :
    ∃ t ∈ Set.Ioo a b, IsGramPoint n t :=
  exists_gram_in_Ioo hab ha hb

theorem actual_weight_transport {f : ℂ → ℝ}
    (hf : Summable (fun p => f (riemannXiDivisorZeroValue p))) :
    (∑' p, f (riemannXiDivisorZeroValue p)) = ∑' z, zetaWeight f z :=
  tsum_xi_eq_zetaWeight hf

#print axioms gram_exists
#print axioms actual_weight_transport
end LiuWang.Proof.Campaign20260915.Parent.CrossLaneHandoff

#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.gram_sign_sq
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.phase_at_gram
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.signedZ_at_gram
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.goodGram_iff_positive_zeta_re
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.goodGram_critical_ne_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.exists_gram_in_Ioo
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.exists_gram_of_phase_approximations
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.goodGram_of_uniform_enclosure
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.completed_sign_change_of_normalized
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.consecutive_goodGram_sign_change
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.turingS_at_gram
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.turingSLeft_at_gram
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.gram_left_upper_iff
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.gram_closed_upper_iff
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.gram_left_lower_iff
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.gram_closed_lower_iff
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.xiZetaValue_surjective
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.zetaZero_im_ne_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.xi_fiber_tsum
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.hasSum_zetaWeight
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.tsum_xi_eq_zetaWeight
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.positive_weight_transport
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.zetaClosedValues_eq_xiWindowValues
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.sum_xiWindow_eq_zeta
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.low_window_iff_zetaClosedValues
#print axioms LiuWang.Proof.Campaign20260915.ZetaMomentTransport.low_window_iff_positiveValues
