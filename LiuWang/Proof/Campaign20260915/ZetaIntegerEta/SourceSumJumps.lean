import LiuWang.Proof.Campaign20260915.ZetaIntegerEta.PolynomialLimits
import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelExpandedSource

set_option autoImplicit false
noncomputable section
open Complex Filter Set
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaIntegerEta
open LiuWang.Proof.Campaign20260915.ZetaValidation

def sourceFiniteSums (s : ℂ) (m : ℕ) : ℂ :=
  (∑ k ∈ Finset.range m, 1 / (k + 1 : ℂ) ^ s) +
    (2 * Real.pi : ℂ) ^ s / (2 * Gamma s * cos (Real.pi * s / 2)) *
      ∑ k ∈ Finset.range m, (k + 1 : ℂ) ^ (s - 1)

theorem sourceFiniteSums_succ (s : ℂ) (m : ℕ) :
    sourceFiniteSums s (m + 1) - sourceFiniteSums s m =
      1 / (m + 1 : ℂ) ^ s +
        (2 * Real.pi : ℂ) ^ s / (2 * Gamma s * cos (Real.pi * s / 2)) *
          (m + 1 : ℂ) ^ (s - 1) := by
  simp only [sourceFiniteSums, Finset.sum_range_succ]
  ring

theorem sourceFiniteSums_continuousAt (m : ℕ) {s : ℂ} (ht : 0 < s.im) :
    ContinuousAt (fun z : ℂ => sourceFiniteSums z m) s := by
  have he : (fun z : ℂ => sourceFiniteSums z m) =ᶠ[𝓝 s]
      (fun z : ℂ => (∑ k ∈ Finset.range m, 1 / (k + 1 : ℂ) ^ z) +
        (rsHankelPrefactor z * (exp (Real.pi * I * z) - 1)) *
          ∑ k ∈ Finset.range m, (k + 1 : ℂ) ^ (z - 1)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds ht] with z hz
    rw [sourceFiniteSums, rsHankel_second_prefactor hz]
  apply ContinuousAt.congr _ he.symm
  apply (rsFiniteDirichletSum_differentiable m s).continuousAt.add
  apply ContinuousAt.mul
  · exact (rsHankelPrefactor_differentiableAt ht).continuousAt.mul (by fun_prop)
  · apply tendsto_finsetSum
    intro k _
    exact (show ContinuousAt (fun z : ℂ => z - 1) s by fun_prop).const_cpow
      (Or.inl (by exact_mod_cast (Nat.succ_ne_zero k)))

theorem sourceFiniteSums_tendsto_left (n : ℕ) {s : ℝ → ℂ}
    (hs : ContinuousAt s ((n : ℝ) + 1)) (ht : 0 < (s ((n : ℝ) + 1)).im) :
    Tendsto (fun eta : ℝ => sourceFiniteSums (s eta) ⌊eta⌋₊)
      (𝓝[<] ((n : ℝ) + 1)) (𝓝 (sourceFiniteSums (s ((n : ℝ) + 1)) n)) := by
  have h := ((sourceFiniteSums_continuousAt n ht).comp hs).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Iio ((n : ℝ) + 1)))
  apply h.congr'
  filter_upwards [floor_eventually_left n] with eta he
  simp only [he, Function.comp_def]

theorem sourceFiniteSums_tendsto_right (n : ℕ) {s : ℝ → ℂ}
    (hs : ContinuousAt s (n : ℝ)) (ht : 0 < (s (n : ℝ)).im) :
    Tendsto (fun eta : ℝ => sourceFiniteSums (s eta) ⌊eta⌋₊)
      (𝓝[≥] (n : ℝ)) (𝓝 (sourceFiniteSums (s (n : ℝ)) n)) := by
  have h := ((sourceFiniteSums_continuousAt n ht).comp hs).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ici (n : ℝ)))
  apply h.congr'
  filter_upwards [floor_eventually_right n] with eta he
  simp only [he, Function.comp_def]

theorem expanded_hankel_remainder {m : ℕ} (hm : 0 < m) {s : ℂ}
    (ht : 0 < s.im) {R : ℝ} (hR : (m : ℝ) < R) (hR' : R < m + 1) :
    rsHankelPrefactor s * rsHankelTiltedC1 s m (Real.log R) =
      riemannZeta s - sourceFiniteSums s m := by
  have h := zeta_eq_source_sums_add_expanded_hankel hm ht hR hR'
  change riemannZeta s = sourceFiniteSums s m + _ at h
  linear_combination -h

theorem expanded_hankel_index_jump {m : ℕ} (hm : 0 < m) {s : ℂ}
    (ht : 0 < s.im) {R S : ℝ} (hR : (m : ℝ) < R) (hR' : R < m + 1)
    (hS : (m : ℝ) + 1 < S) (hS' : S < (m : ℝ) + 2) :
    rsHankelPrefactor s *
      (rsHankelTiltedC1 s (m + 1) (Real.log S) - rsHankelTiltedC1 s m (Real.log R)) =
      -(1 / (m + 1 : ℂ) ^ s +
        (2 * Real.pi : ℂ) ^ s / (2 * Gamma s * cos (Real.pi * s / 2)) *
          (m + 1 : ℂ) ^ (s - 1)) := by
  rw [mul_sub, expanded_hankel_remainder (Nat.succ_pos m) ht
    (by simpa using hS) (by push_cast; linarith),
    expanded_hankel_remainder hm ht hR hR']
  linear_combination -(sourceFiniteSums_succ s m)

theorem expanded_hankel_tendsto_left {n : ℕ} (hn : 0 < n) {s : ℝ → ℂ}
    (hs : ContinuousAt s ((n : ℝ) + 1)) (ht : 0 < (s ((n : ℝ) + 1)).im) :
    Tendsto (fun eta : ℝ => rsHankelPrefactor (s eta) *
      rsHankelTiltedC1 (s eta) ⌊eta⌋₊ (Real.log ((⌊eta⌋₊ : ℝ) + 1 / 2)))
      (𝓝[<] ((n : ℝ) + 1))
      (𝓝 (riemannZeta (s ((n : ℝ) + 1)) - sourceFiniteSums (s ((n : ℝ) + 1)) n)) := by
  have hz : s ((n : ℝ) + 1) ≠ 1 := by
    intro he
    rw [he] at ht
    norm_num at ht
  have hc := (differentiableAt_riemannZeta hz).continuousAt.comp hs
  have h := (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio ((n : ℝ) + 1)))).sub
    (sourceFiniteSums_tendsto_left n hs ht)
  have hi : ∀ᶠ eta : ℝ in 𝓝[<] ((n : ℝ) + 1), 0 < (s eta).im :=
    ((continuous_im.continuousAt.comp hs).eventually (Ioi_mem_nhds ht)).filter_mono
      nhdsWithin_le_nhds
  apply h.congr'
  filter_upwards [floor_eventually_left n, hi] with eta he hi
  rw [he, expanded_hankel_remainder hn hi (by linarith : (n : ℝ) < n + 1 / 2)
    (by linarith : (n : ℝ) + 1 / 2 < n + 1)]
  rfl

theorem expanded_hankel_tendsto_right {n : ℕ} (hn : 0 < n) {s : ℝ → ℂ}
    (hs : ContinuousAt s (n : ℝ)) (ht : 0 < (s (n : ℝ)).im) :
    Tendsto (fun eta : ℝ => rsHankelPrefactor (s eta) *
      rsHankelTiltedC1 (s eta) ⌊eta⌋₊ (Real.log ((⌊eta⌋₊ : ℝ) + 1 / 2)))
      (𝓝[≥] (n : ℝ))
      (𝓝 (riemannZeta (s (n : ℝ)) - sourceFiniteSums (s (n : ℝ)) n)) := by
  have hz : s (n : ℝ) ≠ 1 := by
    intro he
    rw [he] at ht
    norm_num at ht
  have hc := (differentiableAt_riemannZeta hz).continuousAt.comp hs
  have h := (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ici (n : ℝ)))).sub
    (sourceFiniteSums_tendsto_right n hs ht)
  have hi : ∀ᶠ eta : ℝ in 𝓝[≥] (n : ℝ), 0 < (s eta).im :=
    ((continuous_im.continuousAt.comp hs).eventually (Ioi_mem_nhds ht)).filter_mono
      nhdsWithin_le_nhds
  apply h.congr'
  filter_upwards [floor_eventually_right n, hi] with eta he hi
  rw [he, expanded_hankel_remainder hn hi (by linarith : (n : ℝ) < n + 1 / 2)
    (by linarith : (n : ℝ) + 1 / 2 < n + 1)]
  rfl

end LiuWang.Proof.Campaign20260915.ZetaIntegerEta
