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
import LiuWang.Proof.Campaign20260915.Parent.EvaluatorAudit

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.Parent.NineWayAudit
open ZetaValidation ZetaMordell ZetaRealNormalization ZetaPhiEnclosure ZetaMainSumEvaluator
open EvaluatorAudit

theorem actual_zeta_evaluator_interval
    {D S P : ℕ} (hD : 1 ≤ D) (hS : 1 ≤ S)
    {eta : ℝ} (he : 0 ≤ eta) (hlarge : 2000 < eta ^ 2)
    (hint : ∀ k : ℤ, eta ≠ k)
    (r d t₀ θ₀ dt dθ : ℚ)
    (hr : |r| ≤ 1) (hd : d ≤ (1 : ℚ) / 10 ^ 24)
    (hz : |sourcePhiParameter eta ⌊eta⌋₊ - r| ≤ (d : ℝ))
    (ht : |sourceTime eta - (t₀ : ℝ)| ≤ (dt : ℝ))
    (hθ : |criticalGammaArgument (sourceTime eta) - (θ₀ : ℝ)| ≤ (dθ : ℝ))
    (hfit : ∀ n, 1 ≤ n → n ≤ ⌊eta⌋₊ → PhaseFits (makeEntry S P n) t₀ θ₀) :
    normalizedCriticalZeta (sourceTime eta) ∈ Set.Icc
      (((evaluate D (makeEntry S P) t₀ θ₀ ⌊eta⌋₊ : ℝ) +
        sourceSignedAmplitude eta ⌊eta⌋₊ * phiRealCenter r d eta) -
        (paidAnalyticBudget eta +
          (evaluationRadius D (makeEntry S P) t₀ dt dθ ⌊eta⌋₊ : ℝ) +
            eta ^ (-(1 / 2 : ℝ)) * phiRealError eta))
      (((evaluate D (makeEntry S P) t₀ θ₀ ⌊eta⌋₊ : ℝ) +
        sourceSignedAmplitude eta ⌊eta⌋₊ * phiRealCenter r d eta) +
        (paidAnalyticBudget eta +
          (evaluationRadius D (makeEntry S P) t₀ dt dθ ⌊eta⌋₊ : ℝ) +
            eta ^ (-(1 / 2 : ℝ)) * phiRealError eta)) := by
  have h := abs_le.mp (actual_zeta_evaluator_inputs_paid hD hS he hlarge hint
    r d t₀ θ₀ dt dθ hr hd hz ht hθ hfit)
  constructor <;> linarith [h.1, h.2]

end LiuWang.Proof.Campaign20260915.Parent.NineWayAudit
