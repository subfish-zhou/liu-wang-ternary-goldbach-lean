import LiuWang.Proof.DirichletZeroCount.Argument.ContinuousCount
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedRegularLogDerivative

/-! # Exact separation of the conductor, Gamma and ordinary-L argument contributions -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open LiuWang.Proof.Interfaces (Character)
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount.Argument

def ThreeIntegrable (g : ℂ → ℂ) (b H : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (-H : ℝ) * I)) volume (1 / 2) b ∧
  IntervalIntegrable (fun t : ℝ => g ((b : ℂ) + (t : ℂ) * I)) volume (-H) H ∧
  IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (H : ℂ) * I)) volume (1 / 2) b

theorem rightThree_add {f g : ℂ → ℂ} {b H : ℝ}
    (hf : ThreeIntegrable f b H) (hg : ThreeIntegrable g b H) :
    rightThreeIntegral (fun z => f z + g z) b H =
      rightThreeIntegral f b H + rightThreeIntegral g b H := by
  simp only [rightThreeIntegral, HIntegral, VIntegral]
  rw [intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2 hg.2.2, smul_add]
  ring

theorem threeIntegrable_const (c : ℂ) (b H : ℝ) :
    ThreeIntegrable (fun _ => c) b H :=
  ⟨intervalIntegrable_const, intervalIntegrable_const, intervalIntegrable_const⟩

theorem threeIntegrable_add {f g : ℂ → ℂ} {b H : ℝ}
    (hf : ThreeIntegrable f b H) (hg : ThreeIntegrable g b H) :
    ThreeIntegrable (fun s => f s + g s) b H :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.add hg.2.2⟩

theorem rightThree_const (c : ℂ) (b H : ℝ) :
    rightThreeIntegral (fun _ => c) b H = 2 * (H : ℂ) * I * c := by
  simp only [rightThreeIntegral, HIntegral, VIntegral, intervalIntegral.integral_const,
    smul_eq_mul, real_smul, ofReal_sub, ofReal_neg]
  ring

theorem rightThree_congr {f g : ℂ → ℂ} {b H : ℝ}
    (hbot : ∀ x ∈ Set.uIcc (1 / 2) b, f ((x : ℂ) + (-H : ℝ) * I) =
      g ((x : ℂ) + (-H : ℝ) * I))
    (hvert : ∀ t ∈ Set.uIcc (-H) H, f ((b : ℂ) + (t : ℂ) * I) =
      g ((b : ℂ) + (t : ℂ) * I))
    (htop : ∀ x ∈ Set.uIcc b (1 / 2), f ((x : ℂ) + (H : ℂ) * I) =
      g ((x : ℂ) + (H : ℂ) * I)) :
    rightThreeIntegral f b H = rightThreeIntegral g b H := by
  unfold rightThreeIntegral HIntegral VIntegral
  rw [intervalIntegral.integral_congr hbot, intervalIntegral.integral_congr hvert,
    intervalIntegral.integral_congr (fun x hx => htop x (by rwa [Set.uIcc_comm]))]

theorem threeIntegrable_logDeriv {f : ℂ → ℂ} {b H : ℝ} (hb : 1 < b)
    (ha : ∀ s : ℂ, 0 < s.re → AnalyticAt ℂ f s)
    (hbot : ∀ x ∈ Set.uIcc (1 / 2) b, f ((x : ℂ) + (-H : ℝ) * I) ≠ 0)
    (hvert : ∀ t ∈ Set.uIcc (-H) H, f ((b : ℂ) + (t : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Set.uIcc b (1 / 2), f ((x : ℂ) + (H : ℂ) * I) ≠ 0) :
    ThreeIntegrable (logDeriv f) b H := by
  have hp {x : ℝ} (hx : x ∈ Set.uIcc (1 / 2) b) : 0 < x := by
    rw [Set.uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ b)] at hx
    linarith [hx.1]
  have hhor (t : ℝ)
      (hn : ∀ x ∈ Set.uIcc (1 / 2) b, f ((x : ℂ) + (t : ℂ) * I) ≠ 0) :
      IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (t : ℂ) * I))
        volume (1 / 2) b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hax := ha ((x : ℂ) + (t : ℂ) * I) (by simpa using hp hx)
    exact ((hax.deriv.div hax (hn x hx)).continuousAt.comp
      (f := fun y : ℝ => (y : ℂ) + (t : ℂ) * I)
      (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + (t : ℂ) * I) x)).continuousWithinAt
  refine ⟨hhor (-H) hbot, ?_, hhor H (fun x hx => htop x (by rwa [Set.uIcc_comm]))⟩
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have hat := ha ((b : ℂ) + (t : ℂ) * I) (by simpa using (zero_lt_one.trans hb))
  exact ((hat.deriv.div hat (hvert t ht)).continuousAt.comp
    (f := fun y : ℝ => (b : ℂ) + (y : ℂ) * I)
    (by fun_prop : ContinuousAt (fun y : ℝ => (b : ℂ) + (y : ℂ) * I) t)).continuousWithinAt

theorem gammaFactor_analyticAt {q : ℕ} (chi : Character q) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ chi.gammaFactor s := by
  have hd : DifferentiableOn ℂ chi.gammaFactor {z : ℂ | 0 < z.re} :=
    fun z hz => (DirichletCharacter.differentiableAt_gammaFactor_of_re_pos chi hz).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const continuous_re).mem_nhds hs)

theorem completed_three_split {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    rightThreeIntegral (logDeriv (symmetricCompletedLFunction chi)) b H =
      (H * Real.log q : ℝ) * I + rightThreeIntegral (logDeriv chi.LFunction) b H +
        rightThreeIntegral (logDeriv chi.gammaFactor) b H := by
  have hn := completed_border_nonzero hchi hprim hb hH hreg
  obtain ⟨hbot, hvert, htop⟩ := rightThree_nonzero hb hH hn
  have hp {x : ℝ} (hx : x ∈ Set.uIcc (1 / 2) b) : 0 < x := by
    rw [Set.uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ b)] at hx
    linarith [hx.1]
  have hp' {x : ℝ} (hx : x ∈ Set.uIcc b (1 / 2)) : 0 < x := hp (by rwa [Set.uIcc_comm])
  have hlbot : ∀ x ∈ Set.uIcc (1 / 2) b, chi.LFunction ((x : ℂ) + (-H : ℝ) * I) ≠ 0 :=
    fun x hx hz => hbot x hx ((completed_zero_iff_ordinary chi (by simpa using hp hx)).mpr hz)
  have hlvert : ∀ t ∈ Set.uIcc (-H) H, chi.LFunction ((b : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t ht hz => hvert t ht ((completed_zero_iff_ordinary chi
      (by simpa using zero_lt_one.trans hb)).mpr hz)
  have hltop : ∀ x ∈ Set.uIcc b (1 / 2), chi.LFunction ((x : ℂ) + (H : ℂ) * I) ≠ 0 :=
    fun x hx hz => htop x hx ((completed_zero_iff_ordinary chi (by simpa using hp' hx)).mpr hz)
  have hL : Differentiable ℂ chi.LFunction :=
    fun s => DirichletCharacter.differentiableAt_LFunction chi s (Or.inr hchi)
  have hli := threeIntegrable_logDeriv hb (fun s _ => hL.analyticAt s) hlbot hlvert hltop
  have hgi := threeIntegrable_logDeriv (H := H) hb (fun _ hs => gammaFactor_analyticAt chi hs)
    (fun x hx => DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi (by simpa using hp hx))
    (fun t _ => DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi (s := (b : ℂ) + (t : ℂ) * I)
      (by simpa using zero_lt_one.trans hb))
    (fun x hx => DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi (by simpa using hp' hx))
  have he {s : ℂ} (hs : 0 < s.re) (hls : chi.LFunction s ≠ 0) :
      logDeriv (symmetricCompletedLFunction chi) s =
        (Real.log q : ℂ) / 2 + (logDeriv chi.LFunction s + logDeriv chi.gammaFactor s) :=
    logDeriv_symmetricCompletedLFunction_eq_three_factors_of_regular hchi hls
      (DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi hs)
      (DirichletCharacter.differentiableAt_gammaFactor_of_re_pos chi hs)
  rw [rightThree_congr
    (g := fun s => (Real.log q : ℂ) / 2 + (logDeriv chi.LFunction s + logDeriv chi.gammaFactor s))
    (fun x hx => he (by simpa using hp hx) (hlbot x hx))
    (fun t ht => he (by simpa using zero_lt_one.trans hb) (hlvert t ht))
    (fun x hx => he (by simpa using hp' hx) (hltop x hx)),
    rightThree_add (threeIntegrable_const _ b H) (threeIntegrable_add hli hgi),
    rightThree_add hli hgi, rightThree_const]
  push_cast
  ring

theorem completed_count_gamma_split {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    (count chi 0 H : ℝ) =
      (H * Real.log q + (rightThreeIntegral (logDeriv chi.LFunction) b H).im +
        (rightThreeIntegral (logDeriv chi.gammaFactor) b H).im) / Real.pi := by
  rw [completed_count_eq_three_im hchi hprim hb hH hreg,
    completed_three_split hchi hprim hb hH hreg]
  simp only [add_im, mul_im, ofReal_im, ofReal_re, I_re, I_im, zero_mul, add_zero, mul_one]

theorem exists_completed_count_gamma_split {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b y r : ℝ}
    (hb : 1 < b) (hy : 0 ≤ y) (hr : 0 < r) :
    ∃ H : ℝ, y < H ∧ H < y + r ∧ (count chi 0 y : ℝ) =
      (H * Real.log q + (rightThreeIntegral (logDeriv chi.LFunction) b H).im +
        (rightThreeIntegral (logDeriv chi.gammaFactor) b H).im) / Real.pi := by
  obtain ⟨H, hyH, hHr, hc, _, hreg⟩ := Applications.exists_common_count_plateau q (y := y) hr
  refine ⟨H, hyH, hHr, ?_⟩
  rw [← hc chi 0 H hyH.le le_rfl]
  exact completed_count_gamma_split hchi hprim hb (hy.trans hyH.le) (hreg chi)

end LiuWang.Proof.DirichletZeroCount.Argument
