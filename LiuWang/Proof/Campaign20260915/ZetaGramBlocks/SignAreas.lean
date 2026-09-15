import LiuWang.Proof.Campaign20260915.ZetaGramBlocks.ZeroWindows
import LiuWang.Proof.Campaign20260915.ZetaValidation.SignBlocks

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaGramBlocks

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding

theorem sign_window_evidence {a b : ℝ} (ha : 0 ≤ a) {m : ℕ}
    (l r : Fin m → ℝ) (hlo : ∀ i, a ≤ l i) (hhi : ∀ i, r i ≤ b)
    (hwidth : ∀ i, l i < r i) (hsep : ∀ i j, i < j → r i ≤ l j)
    (hsign : ∀ i, criticalCompletedZeta (l i) * criticalCompletedZeta (r i) < 0) :
    ∃ F : Finset ℂ, F.card = m ∧ F ⊆ positiveValues b ∧
      (∀ z ∈ F, a < z.im) ∧ (∀ z ∈ F, z.im < b) ∧
      (∀ z ∈ F, z.re = 1 / 2) ∧
      (∑ i, (b - r i)) ≤
        (∑ z ∈ F, (analyticOrderNatAt riemannZeta z : ℝ) * (b - z.im)) ∧
      (∑ i, (l i - a)) ≤
        (∑ z ∈ F, (analyticOrderNatAt riemannZeta z : ℝ) * (z.im - a)) := by
  classical
  obtain ⟨z, hinj, hz⟩ := exists_injective_critical_zeros l r hwidth hsep hsign
  let F := Finset.univ.image z
  have hza (i : Fin m) : a < (z i).im := (hlo i).trans_lt (hz i).2.2.1
  have hzb (i : Fin m) : (z i).im < b := (hz i).2.2.2.trans_le (hhi i)
  have hmem (i : Fin m) : z i ∈ positiveValues b :=
    mem_positiveValues.mpr ⟨(hz i).1, by rw [(hz i).2.1]; norm_num,
      by rw [(hz i).2.1]; norm_num, ha.trans_lt (hza i), (hzb i).le⟩
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [F, Finset.card_image_of_injective _ hinj]
  · intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact hmem i
  · intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact hza i
  · intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact hzb i
  · intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact (hz i).2.1
  · rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
    apply Finset.sum_le_sum
    intro i _
    have ho : (1 : ℝ) ≤ analyticOrderNatAt riemannZeta (z i) := by
      exact_mod_cast positive_order_one_le (hmem i)
    have hm := mul_le_mul_of_nonneg_right ho (sub_nonneg.mpr (hzb i).le)
    linarith [(hz i).2.2.2]
  · rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
    apply Finset.sum_le_sum
    intro i _
    have ho : (1 : ℝ) ≤ analyticOrderNatAt riemannZeta (z i) := by
      exact_mod_cast positive_order_one_le (hmem i)
    have hm := mul_le_mul_of_nonneg_right ho (sub_nonneg.mpr (hza i).le)
    linarith [(hz i).2.2.1]

theorem sign_windows_count_and_areas {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {m : ℕ}
    (l r : Fin m → ℝ) (hlo : ∀ i, a ≤ l i) (hhi : ∀ i, r i ≤ b)
    (hwidth : ∀ i, l i < r i) (hsep : ∀ i j, i < j → r i ≤ l j)
    (hsign : ∀ i, criticalCompletedZeta (l i) * criticalCompletedZeta (r i) < 0) :
    m ≤ criticalBlockCount a b ∧
      positiveCount a + m ≤ positiveCountLeft b ∧
      (positiveCount a : ℝ) * (b - a) + (∑ i, (b - r i)) ≤
        (∫ t in a..b, (positiveCount t : ℝ)) ∧
      (∑ i, (l i - a)) ≤ (positiveCountLeft b : ℝ) * (b - a) -
        (∫ t in a..b, (positiveCount t : ℝ)) := by
  obtain ⟨F, hc, hf, hl, hh, hr, hal, har⟩ :=
    sign_window_evidence ha l r hlo hhi hwidth hsep hsign
  have hblock : F ⊆ criticalBlockValues a b :=
    fun z hz => Finset.mem_filter.mpr ⟨hf hz, hr z hz, (hl z hz).le, hh z hz⟩
  have hcount := finite_zero_count_increment hab F hf hl hh
  rw [hc] at hcount
  have hleft := finite_zero_left_area hab.le F hf hl
  have hright := finite_zero_right_area hab.le F hf (fun z hz => (hl z hz).le) hh
  refine ⟨?_, hcount, ?_, har.trans hright⟩
  · rw [← hc]
    exact card_le_criticalBlockCount F hblock
  · linarith

theorem integral_turingS_count_identity {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, turingS t) =
      (∫ t in a..b, (positiveCount t : ℝ)) - (b - a) -
        (∫ t in a..b, criticalGammaArgument t) / Real.pi := by
  rw [integral_turingS_eq_zero_areas hab, integral_positiveCount_eq_zero_areas hab]

theorem sign_windows_turing_areas {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {m : ℕ}
    (l r : Fin m → ℝ) (hlo : ∀ i, a ≤ l i) (hhi : ∀ i, r i ≤ b)
    (hwidth : ∀ i, l i < r i) (hsep : ∀ i j, i < j → r i ≤ l j)
    (hsign : ∀ i, criticalCompletedZeta (l i) * criticalCompletedZeta (r i) < 0) :
    ((positiveCount a : ℝ) - 1) * (b - a) + (∑ i, (b - r i)) -
      (∫ t in a..b, criticalGammaArgument t) / Real.pi ≤ (∫ t in a..b, turingS t) ∧
    (∫ t in a..b, turingS t) ≤
      ((positiveCountLeft b : ℝ) - 1) * (b - a) - (∑ i, (l i - a)) -
        (∫ t in a..b, criticalGammaArgument t) / Real.pi := by
  have h := sign_windows_count_and_areas ha hab l r hlo hhi hwidth hsep hsign
  rw [integral_turingS_count_identity hab.le]
  constructor <;> nlinarith [h.2.2.1, h.2.2.2]

#print axioms sign_window_evidence
#print axioms sign_windows_count_and_areas
#print axioms sign_windows_turing_areas

end LiuWang.Proof.Campaign20260915.ZetaGramBlocks
