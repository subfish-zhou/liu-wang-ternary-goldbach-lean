import LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate.StartupPhase
import LiuWang.Proof.Campaign20260915.ZetaGramBlocks.GramPoints

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.ZetaGramBlocks

theorem exists_startup_gram :
    ∃ t ∈ Set.Ioo (12570 : ℝ) 12580, IsGramPoint 13210 t :=
  exists_gram_in_Ioo (by norm_num)
    (by simpa using startup_left_argument) (by simpa using startup_right_argument)

def startupHeight : ℝ := Classical.choose exists_startup_gram

theorem startupHeight_bounds : startupHeight ∈ Set.Ioo (12570 : ℝ) 12580 :=
  (Classical.choose_spec exists_startup_gram).1

theorem startupHeight_isGramPoint : IsGramPoint 13210 startupHeight :=
  (Classical.choose_spec exists_startup_gram).2

theorem startupHeight_source_thresholds :
    (168 : ℝ) * Real.pi < startupHeight ∧
      (250 : ℝ) * Real.pi < startupHeight ∧
        (4000 : ℝ) * Real.pi < startupHeight :=
  ⟨source_thresholds_below_start.1.trans startupHeight_bounds.1,
    source_thresholds_below_start.2.1.trans startupHeight_bounds.1,
    source_thresholds_below_start.2.2.trans startupHeight_bounds.1⟩

theorem lowPrefix_startupHeight : lowPrefix startupHeight = 32768 := by
  have hb := startupHeight_bounds
  unfold lowPrefix
  rw [abs_of_pos (by linarith [hb.1] : 0 < startupHeight)]
  split_ifs <;> linarith [hb.1]

theorem startup_phase_one : criticalGammaPhase startupHeight = 1 := by
  rw [phase_at_gram startupHeight_isGramPoint]
  norm_num

theorem startup_real_remainder :
    |normalizedCriticalZeta startupHeight -
      (eulerMaclaurinApprox (criticalPoint startupHeight) 32768 63).re| ≤
        1 / 1000000000000000000 := by
  have ht : |startupHeight| ≤ 12600 := by
    rw [abs_of_pos (by linarith [startupHeight_bounds.1] : 0 < startupHeight)]
    linarith [startupHeight_bounds.2]
  simpa only [lowPrefix_startupHeight, startup_phase_one, mul_one] using
    low_normalized_order64_remainder ht

theorem through_startup_remainder {s : ℂ}
    (hslo : 1 / 2 ≤ s.re) (hshi : s.re ≤ 2)
    (ht : |s.im| ≤ startupHeight) (hs1 : s ≠ 1) :
    ‖riemannZeta s - eulerMaclaurinApprox s (lowPrefix s.im) 63‖ ≤
      1 / 1000000000000000000 :=
  low_order64_remainder hslo hshi (by linarith [startupHeight_bounds.2]) hs1

def windowValues (H : ℝ) : Finset ℂ :=
  (positiveValues H).filter (fun z => 16 < z.im)

def windowCount (H : ℝ) : ℕ :=
  ∑ z ∈ windowValues H, analyticOrderNatAt riemannZeta z

theorem mem_windowValues {H : ℝ} {z : ℂ} :
    z ∈ windowValues H ↔
      riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ 16 < z.im ∧ z.im ≤ H := by
  simp only [windowValues, Finset.mem_filter, mem_positiveValues]
  constructor
  · rintro ⟨⟨hz, h0, h1, _, hH⟩, h16⟩
    exact ⟨hz, h0, h1, h16, hH⟩
  · rintro ⟨hz, h0, h1, h16, hH⟩
    exact ⟨⟨hz, h0, h1, by linarith, hH⟩, h16⟩

theorem positiveCount_eq_one_add_windowCount {H : ℝ} (hH : 16 ≤ H) :
    positiveCount H = 1 + windowCount H := by
  classical
  have hs := Finset.sum_filter_add_sum_filter_not (positiveValues H)
    (fun z : ℂ => 16 < z.im) (analyticOrderNatAt riemannZeta)
  have hb : (positiveValues H).filter (fun z => ¬16 < z.im) = positiveValues 16 := by
    ext z
    simp only [Finset.mem_filter, mem_positiveValues, not_lt]
    constructor
    · rintro ⟨⟨hz, h0, h1, hp, _⟩, h16⟩
      exact ⟨hz, h0, h1, hp, h16⟩
    · rintro ⟨hz, h0, h1, hp, h16⟩
      exact ⟨⟨hz, h0, h1, hp, h16.trans hH⟩, h16⟩
  rw [hb] at hs
  change windowCount H + positiveCount 16 = positiveCount H at hs
  rw [positiveCount_sixteen] at hs
  omega

theorem startup_count_split :
    positiveCount startupHeight = 1 + windowCount startupHeight :=
  positiveCount_eq_one_add_windowCount (by linarith [startupHeight_bounds.1])

theorem startup_turingS_eq_windowCount :
    turingS startupHeight = (windowCount startupHeight : ℝ) - 13210 := by
  rw [turingS_at_gram startupHeight_isGramPoint, startup_count_split]
  push_cast
  ring

theorem startup_partition :
    Set.Ioc (16 : ℝ) startupHeight ∪ Set.Ioi startupHeight = Set.Ioi 16 := by
  ext t
  simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · rintro (⟨ht, _⟩ | ht)
    · exact ht
    · linarith [startupHeight_bounds.1]
  · intro ht
    by_cases h : t ≤ startupHeight
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr (lt_of_not_ge h)

#print axioms exists_startup_gram
#print axioms startup_real_remainder
#print axioms through_startup_remainder
#print axioms startup_count_split
#print axioms startup_turingS_eq_windowCount

end LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate
