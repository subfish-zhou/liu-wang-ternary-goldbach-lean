import LiuWang.Proof.Campaign20260915.ZetaGramBlocks.BrentThreshold
import LiuWang.Proof.Campaign20260915.ZetaGramBlocks.WindowCertification

/-! Actual sign witnesses plus a separate counting upper bound certify a window.
Neither that upper bound, concrete high-height data, nor Brent Theorem 3.2 is proved here.
The unaccepted GramSequence and its unpublished Gamma inputs are deliberately excluded.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex
namespace LiuWang.Proof.Campaign20260915.Parent.GramWindowAudit
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.ZetaGramBlocks

theorem actual_signed_window_complete {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {m : ℕ} (l r : Fin m → ℝ) (hlo : ∀ i, a ≤ l i) (hhi : ∀ i, r i ≤ b)
    (hwidth : ∀ i, l i < r i) (hsep : ∀ i j, i < j → r i ≤ l j)
    (hsign : ∀ i, criticalCompletedZeta (l i) * criticalCompletedZeta (r i) < 0)
    (hupper : positiveCountLeft b ≤ positiveCount a + m) :
    positiveCountLeft b = positiveCount a + m ∧
      ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
        a < z.im → z.im < b → z.re = 1 / 2 ∧ analyticOrderNatAt riemannZeta z = 1 :=
  signed_window_complete_of_count_upper ha hab l r hlo hhi hwidth hsep hsign hupper

#print axioms actual_signed_window_complete
end LiuWang.Proof.Campaign20260915.Parent.GramWindowAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.positive_order_one_le
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.card_le_criticalBlockCount
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.finite_zero_count_increment
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.criticalBlockCount_add_le_strictCount
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.baseline_zero_area
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.finite_zero_left_area
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.integral_strictCount_deficit
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.finite_zero_right_area
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.sign_window_evidence
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.sign_windows_count_and_areas
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.integral_turingS_count_identity
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.sign_windows_turing_areas
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.IsGramBlock
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.rosserRule_of_signs
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.rosser_count_increment
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.rosser_turing_increment
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.turingSLeft_le_turingS
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.consecutive_rosser_turing_closed
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.consecutive_rosser_turing_strict
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.consecutive_signed_blocks_turing
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.consecutive_block_span
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.signed_block_turing_areas
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.log_two_pi_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.brent_threshold_implies_lehman_criterion
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.consecutive_blocks_lehman_criterion
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.openWindow_count_identity
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.openWindow_exhaustion
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.signed_window_complete_of_count_upper
#print axioms LiuWang.Proof.Campaign20260915.ZetaGramBlocks.strict_closed_count_eq_iff
