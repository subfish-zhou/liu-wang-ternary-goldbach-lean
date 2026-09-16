import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.SourceBudgetAudit
import LiuWang.Proof.Campaign20260915.ZetaWinding.TuringEndpoints

set_option autoImplicit false
noncomputable section
open Complex Filter Set
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaWinding

def originalRealRemainderZero (eta : ℝ) (m : ℕ) : ℝ :=
  normalizedCriticalZeta (sourceTime eta) -
    (sourceRealMainSum (sourceTime eta) m +
      sourceSignedAmplitude eta m * rsPhi (sourcePhiParameter eta m))

def originalRealRemainderTwo (eta : ℝ) (m : ℕ) : ℝ :=
  normalizedCriticalZeta (sourceTime eta) -
    (sourceRealMainSum (sourceTime eta) m +
      sourceSignedAmplitude eta m * sourceRealCorrection eta (sourcePhiParameter eta m))

theorem criticalGammaPhase_continuous : Continuous criticalGammaPhase := by
  have he : criticalGammaPhase = fun t : ℝ =>
      Complex.exp ((criticalGammaArgument t : ℂ) * I) :=
    funext criticalGammaPhase_eq_exp_argument
  rw [he]
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp criticalGammaArgument_continuous).mul continuous_const)

theorem normalizedCriticalZeta_continuous : Continuous normalizedCriticalZeta := by
  have hp : Continuous criticalPoint := by
    have he : criticalPoint = (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I) := by
      funext t
      apply Complex.ext <;> simp [criticalPoint]
    rw [he]
    fun_prop
  have hz : Continuous (fun t : ℝ => riemannZeta (criticalPoint t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (differentiableAt_riemannZeta (criticalPoint_ne_one t)).continuousAt.comp
      hp.continuousAt
  have he : normalizedCriticalZeta = fun t =>
      (riemannZeta (criticalPoint t) * criticalGammaPhase t).re := by
    funext t
    exact_mod_cast congrArg Complex.re (normalizedCriticalZeta_ofReal t)
  rw [he]
  exact Complex.continuous_re.comp (hz.mul criticalGammaPhase_continuous)

theorem sourceRealMainSum_continuous (m : ℕ) : Continuous (fun t => sourceRealMainSum t m) := by
  unfold sourceRealMainSum
  apply continuous_const.mul
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul (Real.continuous_cos.comp
    (criticalGammaArgument_continuous.sub (continuous_id.mul continuous_const)))

theorem originalRealRemainderZero_continuousAt (m : ℕ) {eta : ℝ}
    (he : 0 < eta) (hz : |sourcePhiParameter eta m| < 3 / 2) :
    ContinuousAt (fun x => originalRealRemainderZero x m) eta := by
  have ht : ContinuousAt sourceTime eta := by unfold sourceTime; fun_prop
  have ha : ContinuousAt (fun x => sourceSignedAmplitude x m) eta :=
    continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl he.ne'))
  have hp := (rsPhi_analytic hz).continuousAt.comp (f := fun x => sourcePhiParameter x m)
    (show ContinuousAt (fun x => sourcePhiParameter x m) eta by
      unfold sourcePhiParameter; fun_prop)
  exact (normalizedCriticalZeta_continuous.continuousAt.comp ht).sub
    (((sourceRealMainSum_continuous m).continuousAt.comp ht).add (ha.mul hp))

theorem originalRealRemainderTwo_continuousAt (m : ℕ) {eta : ℝ}
    (he : 0 < eta) (hz : |sourcePhiParameter eta m| < 3 / 2) :
    ContinuousAt (fun x => originalRealRemainderTwo x m) eta := by
  have ht : ContinuousAt sourceTime eta := by unfold sourceTime; fun_prop
  have ha : ContinuousAt (fun x => sourceSignedAmplitude x m) eta :=
    continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl he.ne'))
  have hp : ContinuousAt (fun x => sourcePhiParameter x m) eta := by
    unfold sourcePhiParameter; fun_prop
  have hc : ContinuousAt (fun x => sourceRealCorrection x (sourcePhiParameter x m)) eta :=
    (((rsPhi_analytic hz).continuousAt.comp (f := fun x => sourcePhiParameter x m) hp).sub
      (((rsPhiOne_analytic hz).continuousAt.comp (f := fun x => sourcePhiParameter x m) hp).div
        continuousAt_id he.ne')).add
        (((rsPhiTwo_analytic hz).continuousAt.comp (f := fun x => sourcePhiParameter x m) hp).div
          (continuousAt_id.pow 2)
          (pow_ne_zero _ he.ne'))
  exact (normalizedCriticalZeta_continuous.continuousAt.comp ht).sub
    (((sourceRealMainSum_continuous m).continuousAt.comp ht).add (ha.mul hc))

theorem original_endpoint_neighborhood {n : ℕ} (hn : 0 < n)
    (H : ℝ) (ht : H < (n : ℝ) ^ 2) :
    ∀ᶠ eta : ℝ in 𝓝[>] (n : ℝ),
      0 < eta ∧ H < eta ^ 2 ∧ ⌊eta⌋₊ = n ∧ (∀ k : ℤ, eta ≠ k) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  filter_upwards [Ioo_mem_nhdsGT (show (n : ℝ) < n + 1 by linarith),
    (strict_height_eventually H n ht).filter_mono
      (nhdsWithin_le_nhds (s := Ioi (n : ℝ)))] with eta heta hH
  refine ⟨by linarith [heta.1], hH, Nat.floor_eq_on_Ico n eta ⟨heta.1.le, heta.2⟩, ?_⟩
  intro k hk
  have hi : (n : ℤ) < k ∧ k < (n : ℤ) + 1 := by
    exact_mod_cast (hk ▸ And.intro heta.1 heta.2)
  omega

theorem originalRealRemainderZero_tendsto_right {n : ℕ} (hn : 0 < n) :
    Tendsto (fun eta : ℝ => |originalRealRemainderZero eta ⌊eta⌋₊|)
      (𝓝[>] (n : ℝ)) (𝓝 |originalRealRemainderZero n n|) := by
  have h := (originalRealRemainderZero_continuousAt n (eta := n)
    (by exact_mod_cast hn) (by norm_num [sourcePhiParameter])).abs.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (n : ℝ)))
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (n : ℝ) < n + 1 by linarith)] with eta he
  rw [Nat.floor_eq_on_Ico n eta ⟨he.1.le, he.2⟩]

theorem originalRealRemainderTwo_tendsto_right {n : ℕ} (hn : 0 < n) :
    Tendsto (fun eta : ℝ => |originalRealRemainderTwo eta ⌊eta⌋₊|)
      (𝓝[>] (n : ℝ)) (𝓝 |originalRealRemainderTwo n n|) := by
  have h := (originalRealRemainderTwo_continuousAt n (eta := n)
    (by exact_mod_cast hn) (by norm_num [sourcePhiParameter])).abs.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (n : ℝ)))
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (n : ℝ) < n + 1 by linarith)] with eta he
  rw [Nat.floor_eq_on_Ico n eta ⟨he.1.le, he.2⟩]

theorem original_scale_continuousAt {eta : ℝ} (he : 0 < eta) (c p : ℝ) :
    ContinuousAt (fun x : ℝ => c * (x ^ 2) ^ p) eta :=
  continuousAt_const.mul ((continuousAt_id.pow 2).rpow_const
    (Or.inl (pow_ne_zero _ he.ne')))

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
