import LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.PrimePowerReserve
import LiuWang.Proof.Campaign20260915.RosserCount.OriginalCountConsumers
import LiuWang.Proof.Campaign20260915.ZetaMomentTransport.EndpointConsumers

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.RosserCount
open LiuWang.Proof.Campaign20260915.ZetaMomentTransport

namespace LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail

theorem selected_actual_high_tail {L : ℝ} (hL : 5000 ≤ L) :
    (∑' p, rsHighTerm (spectralCutoff L) 1 L p) <
      4 * rosserError (spectralCutoff L) * rsPhi 1 L (spectralCutoff L) +
        2 * (rsQ (spectralCutoff L) * ∫ t in Ioi (spectralCutoff L),
          rsPhi 1 L t * Real.log (t / (2 * Real.pi))) := by
  have hK := spectralCutoff_ge_rsA hL
  have hL0 : 0 ≤ L := by linarith
  have hupper : L ≤ ((1 : ℕ) + 1 : ℝ) * rsR *
      Real.log (spectralCutoff L) ^ 2 := by
    norm_num only [Nat.cast_one]
    exact (spectralCutoff_theorem27_domain hL).2.2
  have hs := rosser_positive_tail_theorem27 hK hL0 (by norm_num : 1 ≤ (1 : ℕ)) hupper
  have ht := rsHighTerm_sum_le_positive_xiPhi hK hL0 (by norm_num : 1 ≤ (1 : ℕ))
  change (∑' p, rsHighTerm (spectralCutoff L) 1 L p) ≤
    2 * ∑' p, rsPositivePhiTerm (spectralCutoff L) 1 L p at ht
  have hmul := mul_lt_mul_of_pos_left hs (by norm_num : (0 : ℝ) < 2)
  exact ht.trans_lt (hmul.trans_eq (by ring))

theorem actual_high_smoothing_budget {L : ℝ} (hL : 5000 ≤ L) :
    Real.exp (-L / 2) * (∑' p, rsZeroMoment 1 0 p) +
      (∑' p, rsHighTerm rsA 1 L p) <
        (smoothingStep L / 2) ^ (1 + 1 : ℕ) := by
  have htail := selected_actual_high_tail hL
  rw [rosserError] at htail
  have hbudget := selected_spectral_budget hL
  rw [actual_high_spectrum_split (by linarith : 0 ≤ L) (spectralCutoff_ge_rsA hL)]
  linarith

theorem actual_high_error_budget {L : ℝ} (hL : 5000 ≤ L) :
    (∑' p, rsHighTerm rsA 1 L p) <
      (9 / 4 : ℝ) * saddle L ^ 2 * Real.exp (-2 * saddle L) := by
  have h := actual_high_smoothing_budget hL
  rw [smoothingStep_moment_budget] at h
  have hn : 0 ≤ Real.exp (-L / 2) * (∑' p, rsZeroMoment 1 0 p) := by
    apply mul_nonneg (Real.exp_pos _).le
    exact tsum_nonneg (fun p => by unfold rsZeroMoment; positivity)
  linarith

#print axioms selected_actual_high_tail
#print axioms actual_high_smoothing_budget
#print axioms actual_high_error_budget

end LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail
