import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.ArithmeticPilot
import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.BatchEvaluator
import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.CutoffIntervals
import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.FiniteEvaluator
import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.OriginalHeightConsumer
import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.SharedCache
import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowEvaluator
import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowPilot
import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.Audit
import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.CertifiedEnclosures
import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.CorrectionEnclosures
import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.DerivativeApproximation
import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.DerivativeBounds
import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.KernelBounds
import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.MachinPrecision
import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.MomentConsumers
import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.PhiApproximation
import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.PrecisionBounds
import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.SincApproximation
import LiuWang.Proof.Campaign20260915.Parent.JnCentralAudit

/-! Joint evaluation of the actual normalized critical zeta value.
The analytic budget is inherited once from the paid Jn/two-tail theorem.
The center still contains the real eta and is not a computed zeta sign certificate.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure
open LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator

/-- Three rational Phi centers, with the actual real inverse powers of eta. -/
def phiRealCenter (r d : ℚ) (eta : ℝ) : ℝ :=
  ((precisePhi r d).center : ℝ) - ((precisePhiOne r d).center : ℝ) / eta +
    ((precisePhiTwo r d).center : ℝ) / eta ^ 2

def phiRealError (eta : ℝ) : ℝ :=
  1 / 10 ^ 20 + (1 / 10 ^ 9) / eta + (1 / 10 ^ 6) / eta ^ 2

/-- Exactly the existing analytic payment, with no second moment/phase charge. -/
def paidAnalyticBudget (eta : ℝ) : ℝ :=
  eta ^ (-(1 / 2 : ℝ)) *
    (120000 / eta * Real.exp (-Real.pi * eta ^ 2 / 8) +
      sourceSevenUniformBudget eta (sourcePhiParameter eta ⌊eta⌋₊) +
      (51 / 50) / eta ^ 3) + 1 / (10 * eta ^ 4) +
    11 / (2 * Real.pi) * eta ^ (-(3 / 2 : ℝ)) * Real.exp (-sourceTime eta / 11)

/-- Continuous-domain Phi certification pays the actual real correction. -/
theorem phiRealCenter_error (r d : ℚ) {eta z : ℝ} (he : 0 ≤ eta)
    (hr : |r| ≤ 1) (hd : d ≤ (1 : ℚ) / 10 ^ 24)
    (hz : |z| ≤ 1) (hinput : |z - r| ≤ (d : ℝ)) :
    |sourceRealCorrection eta z - phiRealCenter r d eta| ≤ phiRealError eta := by
  obtain ⟨h0, h1, h2⟩ := certified_phi_errors r d hr hd hz hinput
  have hd1 := div_le_div_of_nonneg_right h1 he
  have hd2 := div_le_div_of_nonneg_right h2 (sq_nonneg eta)
  calc
    |sourceRealCorrection eta z - phiRealCenter r d eta| =
        |(rsPhi z - ((precisePhi r d).center : ℝ)) -
          (rsPhiOne z - ((precisePhiOne r d).center : ℝ)) / eta +
          (rsPhiTwo z - ((precisePhiTwo r d).center : ℝ)) / eta ^ 2| := by
            congr 1
            unfold sourceRealCorrection phiRealCenter
            ring
    _ ≤ |rsPhi z - ((precisePhi r d).center : ℝ)| +
          |(rsPhiOne z - ((precisePhiOne r d).center : ℝ)) / eta| +
          |(rsPhiTwo z - ((precisePhiTwo r d).center : ℝ)) / eta ^ 2| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ phiRealError eta := by
      rw [abs_div, abs_div, abs_of_nonneg he, abs_of_nonneg (sq_nonneg eta)]
      exact add_le_add (add_le_add h0 hd1) hd2

/-- The signed amplitude is paid only after the actual Phi error is constructed. -/
theorem signed_phiRealCenter_error (r d : ℚ) {eta z : ℝ} (m : ℕ) (he : 0 ≤ eta)
    (hr : |r| ≤ 1) (hd : d ≤ (1 : ℚ) / 10 ^ 24)
    (hz : |z| ≤ 1) (hinput : |z - r| ≤ (d : ℝ)) :
    |sourceSignedAmplitude eta m * sourceRealCorrection eta z -
      sourceSignedAmplitude eta m * phiRealCenter r d eta| ≤
        eta ^ (-(1 / 2 : ℝ)) * phiRealError eta := by
  rw [← mul_sub, abs_mul, abs_sourceSignedAmplitude he]
  exact mul_le_mul_of_nonneg_left (phiRealCenter_error r d he hr hd hz hinput)
    (Real.rpow_nonneg he _)

/-- Actual zeta joint error: analytic remainder, finite main sum, and Phi evaluation.
No hypothesis carries the zeta conclusion. Height and Gamma input enclosures
refer to the same actual sourceTime eta. The inherited noninteger domain remains.
-/
theorem actual_zeta_evaluator_inputs_paid
    {D S P : ℕ} (hD : 1 ≤ D) (hS : 1 ≤ S)
    {eta : ℝ} (he : 0 ≤ eta) (hlarge : 2000 < eta ^ 2)
    (hint : ∀ k : ℤ, eta ≠ k)
    (r d t₀ θ₀ dt dθ : ℚ)
    (hr : |r| ≤ 1) (hd : d ≤ (1 : ℚ) / 10 ^ 24)
    (hz : |sourcePhiParameter eta ⌊eta⌋₊ - r| ≤ (d : ℝ))
    (ht : |sourceTime eta - (t₀ : ℝ)| ≤ (dt : ℝ))
    (hθ : |criticalGammaArgument (sourceTime eta) - (θ₀ : ℝ)| ≤ (dθ : ℝ))
    (hfit : ∀ n, 1 ≤ n → n ≤ ⌊eta⌋₊ → PhaseFits (makeEntry S P n) t₀ θ₀) :
    |normalizedCriticalZeta (sourceTime eta) -
      ((evaluate D (makeEntry S P) t₀ θ₀ ⌊eta⌋₊ : ℝ) +
        sourceSignedAmplitude eta ⌊eta⌋₊ * phiRealCenter r d eta)| ≤
      paidAnalyticBudget eta +
        (evaluationRadius D (makeEntry S P) t₀ dt dθ ⌊eta⌋₊ : ℝ) +
          eta ^ (-(1 / 2 : ℝ)) * phiRealError eta := by
  have hf := sourceFraction_floor he hint
  have hphi := signed_phiRealCenter_error r d ⌊eta⌋₊ he hr hd
    (sourcePhiParameter_mem hf.1.le hf.2.le) hz
  have hmain := makeEntry_evaluate_error hD hS ht hθ hfit
  rw [finiteMainSum_eq_sourceRealMainSum] at hmain
  have hanalytic := JnCentralAudit.actual_zeta_Jn_and_both_tails_paid he hlarge hint
  change |normalizedCriticalZeta (sourceTime eta) -
    (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
      sourceSignedAmplitude eta ⌊eta⌋₊ *
        sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊))| ≤
          paidAnalyticBudget eta at hanalytic
  have hsum := abs_add_le
    (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ -
      (evaluate D (makeEntry S P) t₀ θ₀ ⌊eta⌋₊ : ℝ))
    (sourceSignedAmplitude eta ⌊eta⌋₊ *
      sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊) -
        sourceSignedAmplitude eta ⌊eta⌋₊ * phiRealCenter r d eta)
  have htri := abs_sub_le (normalizedCriticalZeta (sourceTime eta))
    (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
      sourceSignedAmplitude eta ⌊eta⌋₊ *
        sourceRealCorrection eta (sourcePhiParameter eta ⌊eta⌋₊))
    ((evaluate D (makeEntry S P) t₀ θ₀ ⌊eta⌋₊ : ℝ) +
      sourceSignedAmplitude eta ⌊eta⌋₊ * phiRealCenter r d eta)
  have hid (a b c e : ℝ) : a + b - (c + e) = (a - c) + (b - e) := by ring
  rw [hid] at htri
  linarith

end LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit

/-! Complete explicitly named source API, including definitions and structures. -/
set_option pp.fullNames true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 10000000
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.BatchInput
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.BatchInput
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.BatchInput
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.CutoffWindow
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.CutoffWindow
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.CutoffWindow
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.EntryValid
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.EntryValid
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.EntryValid
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.PhaseFits
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.PhaseFits
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.PhaseFits
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.SharedEntry
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.SharedEntry
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.SharedEntry
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowChecks
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowChecks
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowChecks
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowInput
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowInput
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowInput
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowReady
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowReady
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowReady
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.boundaryPilot
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.boundaryPilot
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.boundaryPilot
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.boundaryPilot_output
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.boundaryPilot_output
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.boundaryPilot_source_enclosure
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.boundaryPilot_source_enclosure
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.buildSharedCache
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.buildSharedCache
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.buildSharedCache
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.buildSharedCache_eq
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.buildSharedCache_eq
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.checkedBatch
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.checkedBatch
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.checkedBatch
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.checkedBatch_getElem
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.checkedBatch_getElem
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.checkedBatch_sound
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.checkedBatch_sound
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.checkedWindow
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.checkedWindow
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.checkedWindow
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.checkedWindow_sound
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.checkedWindow_sound
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.cutoffWindow_bounds
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.cutoffWindow_bounds
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.cutoffWindow_constant
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.cutoffWindow_constant
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluate
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluate
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluate
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluateBatch
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluateBatch
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluateBatch
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluateBatch_getElem
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluateBatch_getElem
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluateEntries
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluateEntries
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluateEntries
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluateEntries_sharedCache
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluateEntries_sharedCache
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluatePrefix
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluatePrefix
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluatePrefix
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluatePrefix_finite_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluatePrefix_finite_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluatePrefix_insufficient
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluatePrefix_insufficient
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluatePrefix_sharedCache
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluatePrefix_sharedCache
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluatePrefix_sourceWindow_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluatePrefix_sourceWindow_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluate_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluate_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluate_window_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluate_window_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluationRadius
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluationRadius
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.evaluationRadius
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.finiteMainSum
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.finiteMainSum
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.finiteMainSum
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.finiteMainSum_eq_sourceRealMainSum
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.finiteMainSum_eq_sourceRealMainSum
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.finiteMainSum_length_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.finiteMainSum_length_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.invalidHeightRadius_rejected
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.invalidHeightRadius_rejected
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.logExponent
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.logExponent
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.logExponent
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.logExponent_normalizes
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.logExponent_normalizes
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.makeEntry
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.makeEntry
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.makeEntry
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.makeEntry_evaluate_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.makeEntry_evaluate_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.makeEntry_valid
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.makeEntry_valid
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalCache
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalCache
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalCache
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalCache_logRadius
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalCache_logRadius
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalCache_phaseFits
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalCache_phaseFits
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalHeight_cutoff
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalHeight_cutoff
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalMainCenter
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalMainCenter
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalMainCenter
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalMainCenter_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalMainCenter_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalMainRadius
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalMainRadius
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalMainRadius
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalMainRadius_le
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.originalMainRadius_le
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.original_source_main_enclosure
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.original_source_main_enclosure
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.phaseArgument
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.phaseArgument
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.phaseArgument
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.phaseValue
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.phaseValue
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.phaseValue
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.phase_cos_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.phase_cos_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.phase_input_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.phase_input_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.piLower
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.piLower
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.piLower
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.piUpper
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.piUpper
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.piUpper
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pi_enclosure
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pi_enclosure
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pilot_boundary_not_constant
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pilot_boundary_not_constant
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pilot_boundary_window
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pilot_boundary_window
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pilot_cache_exact
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pilot_cache_exact
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pilot_insufficient_cache
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pilot_insufficient_cache
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pilot_negative_rounding
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pilot_negative_rounding
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pilot_sequential_rounding
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.pilot_sequential_rounding
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.radiusEntries
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.radiusEntries
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.radiusEntries
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.radiusEntries_sharedCache
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.radiusEntries_sharedCache
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.reciprocalSqrt_width
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.reciprocalSqrt_width
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.roundedSum
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.roundedSum
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.roundedSum
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.roundedSum_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.roundedSum_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sharedCache
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sharedCache
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sharedCache
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sharedCache_getElem
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sharedCache_getElem
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sharedCache_prefix
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sharedCache_prefix
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sharedCache_succ
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sharedCache_succ
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sharedCache_valid
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sharedCache_valid
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceCutoff
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceCutoff
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceCutoff
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceCutoff_boundary
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceCutoff_boundary
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceCutoff_eq_iff
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceCutoff_eq_iff
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceMainSum
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceMainSum
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceMainSum
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceTerm
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceTerm
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceTerm
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceTerm_abs_le_two
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.sourceTerm_abs_le_two
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.termRadius
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.termRadius
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.termRadius
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.termValue
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.termValue
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.termValue
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.termValue_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.termValue_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.windowCenter
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.windowCenter
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.windowCenter
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.windowChecks_height_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.windowChecks_height_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.windowRadius
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.windowRadius
#print LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.windowRadius
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.windowReady_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.windowReady_error
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.zeroCacheGrid_rejected
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.zeroCacheGrid_rejected
#check @LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.zeroGrid_rejected
#print axioms LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.zeroGrid_rejected
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.Contains
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.Contains
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.Contains
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.add
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.add
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.add
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.add_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.add_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.divide
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.divide
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.divide
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.divide_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.divide_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.divide_radius_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.RationalBall.divide_radius_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.certified_phi_errors
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.certified_phi_errors
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.certified_r2_center_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.certified_r2_center_error
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.clamp_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.clamp_error
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.correctionKernel_real_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.correctionKernel_real_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.correctionMoment_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.correctionMoment_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.correctionMoment_rational_truncation
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.correctionMoment_rational_truncation
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.correctionMoment_truncation
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.correctionMoment_truncation
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.correction_center_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.correction_center_norm
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.correction_moment_kernel_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.correction_moment_kernel_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeApprox
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeApprox
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeApprox
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeApprox_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeApprox_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeBudget
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeBudget
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeBudget
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeEnclosure
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeEnclosure
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeEnclosure
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeEnclosure_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.derivativeEnclosure_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.gaussianBudget
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.gaussianBudget
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.gaussianBudget
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.gaussianJet_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.gaussianJet_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.inwardStep
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.inwardStep
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.inwardStep
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.inwardStep_abs
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.inwardStep_abs
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.inwardStep_domain
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.inwardStep_domain
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.inwardStep_ne_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.inwardStep_ne_zero
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.machinPi
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.machinPi
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.machinPi
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.machinPiError
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.machinPiError
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.machinPiError
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.machinPi_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.machinPi_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.momentTailBudget
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.momentTailBudget
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.momentTailBudget
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.negative_half_enclosed
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.negative_half_enclosed
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiApprox
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiApprox
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiApprox
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiApprox_center_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiApprox_center_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiApprox_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiApprox_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiApprox_radius_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiApprox_radius_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiDenominatorApprox
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiDenominatorApprox
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiDenominatorApprox
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiDenominatorError
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiDenominatorError
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiDenominatorError
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiEnclosure
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiEnclosure
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiEnclosure
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiEnclosure_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiEnclosure_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiNumeratorApprox
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiNumeratorApprox
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiNumeratorApprox
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiNumeratorError
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiNumeratorError
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiNumeratorError
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneApprox
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneApprox
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneApprox
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneApprox_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneApprox_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneBudget
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneBudget
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneBudget
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneEnclosure
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneEnclosure
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneEnclosure
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneEnclosure_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneEnclosure_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneInputBudget
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneInputBudget
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiOneInputBudget
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiSafeDenominator
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiSafeDenominator
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiSafeDenominator
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTaylor
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTaylor
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTaylor
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoApprox
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoApprox
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoApprox
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoApprox_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoApprox_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoBudget
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoBudget
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoBudget
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoEnclosure
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoEnclosure
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoEnclosure
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoEnclosure_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoEnclosure_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoInputBudget
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoInputBudget
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phiTwoInputBudget
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phi_arguments_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phi_arguments_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phi_denominator_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phi_denominator_error
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phi_numerator_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.phi_numerator_error
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piApprox
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piApprox
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piApprox
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piApprox_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piApprox_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piError
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piError
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piError
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piFourthError
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piFourthError
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piFourthError
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piFourthError_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piFourthError_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piSquareError
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piSquareError
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piSquareError
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piSquareError_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.piSquareError_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.pi_fourth_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.pi_fourth_lower
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.pi_square_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.pi_square_lower
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.positive_half_enclosed
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.positive_half_enclosed
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.preciseDerivativeCenterBudget
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.preciseDerivativeCenterBudget
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.preciseDerivativeCenterBudget
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.preciseDerivativeRadius
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.preciseDerivativeRadius
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.preciseDerivativeRadius
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.preciseDerivative_bounds
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.preciseDerivative_bounds
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhi
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhi
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhi
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiOne
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiOne
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiOne
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiOne_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiOne_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiOne_radius_small
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiOne_radius_small
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiTwo
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiTwo
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiTwo
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiTwo_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiTwo_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiTwo_radius_small
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhiTwo_radius_small
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhi_center_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhi_center_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhi_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhi_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhi_radius_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhi_radius_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhi_radius_small
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePhi_radius_small
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePi
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePi
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePi
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePiError
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePiError
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePiError
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePiError_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePiError_nonneg
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePiError_small
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePiError_small
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePi_abs_le_four
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePi_abs_le_four
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePi_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.precisePi_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.r2EvaluationError
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.r2EvaluationError
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.r2EvaluationError
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.r2HighMomentBudget
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.r2HighMomentBudget
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.r2HighMomentBudget
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.r2HighMomentBudget_simplified
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.r2HighMomentBudget_simplified
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rationalR2Center
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rationalR2Center
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rationalR2Center
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.roundedMachinError
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.roundedMachinError
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.roundedMachinError
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.roundedMachinPi
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.roundedMachinPi
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.roundedMachinPi
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.roundedMachinPi_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.roundedMachinPi_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhiOne_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhiOne_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhiOne_lipschitz
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhiOne_lipschitz
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhiTwo_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhiTwo_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhiTwo_lipschitz
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhiTwo_lipschitz
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhi_derivative_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhi_derivative_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhi_derivative_input_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhi_derivative_input_error
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhi_derivative_lipschitz
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhi_derivative_lipschitz
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhi_taylor_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.rsPhi_taylor_error
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.scaled_argument_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.scaled_argument_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.siegel_denominator_im
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.siegel_denominator_im
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.siegel_denominator_lower
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.siegel_denominator_lower
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincApprox
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincApprox
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincApprox
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincApprox_abs_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincApprox_abs_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincApprox_cast
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincApprox_cast
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincApprox_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincApprox_error
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincError
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincError
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincError
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincError_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincError_bound
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincPolynomial
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincPolynomial
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincPolynomial
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincPolynomial_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincPolynomial_error
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincPolynomial_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincPolynomial_zero
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincTail
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincTail
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincTail
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincTail128_small
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sincTail128_small
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sinc_argument_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sinc_argument_error
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sinc_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sinc_integral
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sinc_lipschitz
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sinc_lipschitz
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sineJet
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sineJet
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sineJet
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sineJet_correct
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sineJet_correct
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sine_taylor_eq
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sine_taylor_eq
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.small_kernel_pilot_pi_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.small_kernel_pilot_pi_error
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.small_kernel_pilot_radius
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.small_kernel_pilot_radius
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sourceGaussianPhase_norm
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sourceGaussianPhase_norm
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sourceLocalPolynomial_seven_certified
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sourceLocalPolynomial_seven_certified
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sourceLocalPolynomial_seven_high_moment_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sourceLocalPolynomial_seven_high_moment_error
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sourcePhiOne_enclosure
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sourcePhiOne_enclosure
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sourcePhiTwo_enclosure
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sourcePhiTwo_enclosure
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sourcePhi_enclosure
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.sourcePhi_enclosure
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.stencilWeight
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.stencilWeight
#print LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.stencilWeight
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.stencilWeight_abs
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.stencilWeight_abs
#check @LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.stencil_polynomial_identity
#print axioms LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.stencil_polynomial_identity
#check @LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.phiRealCenter
#print axioms LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.phiRealCenter
#check @LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.phiRealError
#print axioms LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.phiRealError
#check @LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.paidAnalyticBudget
#print axioms LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.paidAnalyticBudget
#check @LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.phiRealCenter_error
#print axioms LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.phiRealCenter_error
#check @LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.signed_phiRealCenter_error
#print axioms LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.signed_phiRealCenter_error
#check @LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.actual_zeta_evaluator_inputs_paid
#print axioms LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.actual_zeta_evaluator_inputs_paid

/-! Read actual imported ModuleData names, including private/anonymous/generated
members. Do not invent recursor or equation names. These diagnostics add no axiom.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.ArithmeticPilot,
    `LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.BatchEvaluator,
    `LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.CutoffIntervals,
    `LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.FiniteEvaluator,
    `LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.OriginalHeightConsumer,
    `LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.SharedCache,
    `LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowEvaluator,
    `LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.WindowPilot,
    `LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.Audit,
    `LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.CertifiedEnclosures,
    `LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.CorrectionEnclosures,
    `LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.DerivativeApproximation,
    `LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.DerivativeBounds,
    `LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.KernelBounds,
    `LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.MachinPrecision,
    `LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.MomentConsumers,
    `LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.PhiApproximation,
    `LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.PrecisionBounds,
    `LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.SincApproximation
  ]
  for m in targets do
    let some i := env.header.moduleNames.findIdx? (· == m)
      | throwError "missing census module {m}"
    let md := env.header.moduleData[i]!
    logInfo m!"EVALUATOR_MODULE|{m}|{md.constNames.size}"
    for n in md.constNames do
      let some ci := env.find? n | throwError "missing census member {n}"
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "def"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quot"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
      logInfo m!"EVALUATOR_MEMBER|{m}|{n}|{kind}"
      elabCommand (← `(#check @$(mkIdent n)))
      elabCommand (← `(#print axioms $(mkIdent n)))
  let roots : Array Name := #[
    `LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.phiRealCenter,
    `LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.phiRealError,
    `LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.paidAnalyticBudget,
    `LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.phiRealCenter_error,
    `LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.signed_phiRealCenter_error,
    `LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit.actual_zeta_evaluator_inputs_paid
  ]
  for n in roots do
    let some ci := env.find? n | throwError "missing new declaration {n}"
    if let some v := ci.value? then
      for d in v.getUsedConstants do
        logInfo m!"EVALUATOR_VALUE_EDGE|{n}|{d}"
