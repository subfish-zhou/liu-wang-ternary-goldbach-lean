import LiuWang.Proof.DirichletZeroCount.Argument.GammaVertical

/-! # The literal companion completion differs only by a fixed nonzero factor -/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped Classical
open LiuWang.Proof.Interfaces (Character)
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount.Argument

def sourceParity {q : ℕ} (chi : Character q) : ℂ := if chi.Even then 0 else 1

def sourceCompletion {q : ℕ} [NeZero q] (chi : Character q) (s : ℂ) : ℂ :=
  ((q : ℂ) / (Real.pi : ℂ)) ^ ((s + sourceParity chi) / 2) *
    Gamma ((s + sourceParity chi) / 2) * chi.LFunction s

def sourceFactor {q : ℕ} (chi : Character q) : ℂ := (q : ℂ) ^ (sourceParity chi / 2)

theorem sourceFactor_ne_zero {q : ℕ} [NeZero q] (chi : Character q) :
    sourceFactor chi ≠ 0 :=
  cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast NeZero.ne q))

theorem sourceCompletion_eq {q : ℕ} [NeZero q] (chi : Character q)
    {s : ℂ} (hs : 0 < s.re) :
    sourceCompletion chi s = sourceFactor chi * symmetricCompletedLFunction chi s := by
  have hg : chi.gammaFactor s =
      (Real.pi : ℂ) ^ (-(s + sourceParity chi) / 2) * Gamma ((s + sourceParity chi) / 2) := by
    rcases chi.even_or_odd with he | ho
    · simp only [sourceParity, if_pos he, add_zero, he.gammaFactor_def, Gammaℝ]
    · simp only [sourceParity, if_neg ho.not_even, ho.gammaFactor_def, Gammaℝ]
  rw [sourceCompletion, symmetricCompletedLFunction,
    DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos chi hs, hg]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [show (q : ℂ) = ((q : ℝ) : ℂ) by simp,
    div_cpow_ofReal_nonneg (Nat.cast_nonneg q) Real.pi_pos.le]
  rw [show -(s + sourceParity chi) / 2 = -((s + sourceParity chi) / 2) by ring,
    cpow_neg]
  rw [show (s + sourceParity chi) / 2 = s / 2 + sourceParity chi / 2 by ring,
    cpow_add _ _ (by simpa using hq)]
  simp only [sourceFactor, div_eq_mul_inv, ofReal_natCast]
  ring

theorem source_logDeriv_eq {q : ℕ} [NeZero q] (chi : Character q) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (sourceCompletion chi) s = logDeriv (symmetricCompletedLFunction chi) s := by
  have he : sourceCompletion chi =ᶠ[nhds s] (fun z => sourceFactor chi * symmetricCompletedLFunction chi z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact sourceCompletion_eq chi hz
  calc
    logDeriv (sourceCompletion chi) s =
        logDeriv (fun z => sourceFactor chi * symmetricCompletedLFunction chi z) s := by
      simp only [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
    _ = logDeriv (symmetricCompletedLFunction chi) s :=
      logDeriv_const_mul s _ (sourceFactor_ne_zero chi)

theorem source_three_eq {q : ℕ} [NeZero q] (chi : Character q) {b H : ℝ} (hb : 1 < b) :
    rightThreeIntegral (logDeriv (sourceCompletion chi)) b H =
      rightThreeIntegral (logDeriv (symmetricCompletedLFunction chi)) b H := by
  have hp {x : ℝ} (hx : x ∈ Set.uIcc (1 / 2) b) : 0 < x := by
    rw [Set.uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ b)] at hx
    linarith [hx.1]
  exact rightThree_congr
    (fun x hx => source_logDeriv_eq chi (by simpa using hp hx))
    (fun t _ => source_logDeriv_eq chi (s := (b : ℂ) + (t : ℂ) * I)
      (by simpa using zero_lt_one.trans hb))
    (fun x hx => source_logDeriv_eq chi (by simpa using hp (by rwa [Set.uIcc_comm] at hx)))

theorem source_log_lift {q : ℕ} [NeZero q] (chi : Character q) {b H : ℝ} (hb : 1 < b)
    {A B C : ℝ → ℂ} (hl : IsThreeLogLift (symmetricCompletedLFunction chi) b H A B C) :
    IsThreeLogLift (sourceCompletion chi) b H
      (fun x => log (sourceFactor chi) + A x)
      (fun t => log (sourceFactor chi) + B t)
      (fun x => log (sourceFactor chi) + C x) := by
  have hp {x : ℝ} (hx : x ∈ Set.uIcc (1 / 2) b) : 0 < x := by
    rw [Set.uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ b)] at hx
    linarith [hx.1]
  rcases hl with ⟨hA, hB, hC, hAe, hBe, hCe, hAB, hBC⟩
  refine ⟨continuousOn_const.add hA, continuousOn_const.add hB, continuousOn_const.add hC,
    ?_, ?_, ?_, by dsimp; rw [hAB], by dsimp; rw [hBC]⟩
  · intro x hx
    rw [exp_add, exp_log (sourceFactor_ne_zero chi), hAe x hx,
      sourceCompletion_eq chi (by simpa using hp hx)]
  · intro t ht
    rw [exp_add, exp_log (sourceFactor_ne_zero chi), hBe t ht,
      sourceCompletion_eq chi (by simpa using zero_lt_one.trans hb)]
  · intro x hx
    rw [exp_add, exp_log (sourceFactor_ne_zero chi), hCe x hx,
      sourceCompletion_eq chi (by simpa using hp (by rwa [Set.uIcc_comm] at hx))]

theorem source_count_continuous_argument {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b H : ℝ} (hb : 1 < b) (hH : 0 ≤ H)
    (hreg : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → chi.LFunction s ≠ 0) :
    ∃ A B C : ℝ → ℂ, IsThreeLogLift (sourceCompletion chi) b H A B C ∧
      (count chi 0 H : ℝ) = (C (1 / 2) - A (1 / 2)).im / Real.pi ∧
      ∀ alpha : ℝ, 0 ≤ alpha → (count chi alpha H : ℝ) ≤
        (C (1 / 2) - A (1 / 2)).im / Real.pi := by
  obtain ⟨A, B, C, hl, he⟩ := completed_count_continuous_argument hchi hprim hb hH hreg
  have hnew : (count chi 0 H : ℝ) =
      ((log (sourceFactor chi) + C (1 / 2)) - (log (sourceFactor chi) + A (1 / 2))).im / Real.pi := by
    simpa only [add_sub_add_left_eq_sub] using he
  exact ⟨_, _, _, source_log_lift chi hb hl, hnew, fun alpha ha =>
    (Nat.cast_le.mpr (count_antitone_alpha chi H ha)).trans_eq hnew⟩

theorem exists_source_count_continuous_argument {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hprim : chi.IsPrimitive) {b y r : ℝ}
    (hb : 1 < b) (hy : 0 ≤ y) (hr : 0 < r) :
    ∃ H : ℝ, y < H ∧ H < y + r ∧ ∃ A B C : ℝ → ℂ,
      IsThreeLogLift (sourceCompletion chi) b H A B C ∧
      (count chi 0 y : ℝ) = (C (1 / 2) - A (1 / 2)).im / Real.pi ∧
      ∀ alpha : ℝ, 0 ≤ alpha → (count chi alpha y : ℝ) ≤
        (C (1 / 2) - A (1 / 2)).im / Real.pi := by
  obtain ⟨H, hyH, hHr, hc, _, hreg⟩ := Applications.exists_common_count_plateau q (y := y) hr
  obtain ⟨A, B, C, hl, he, _⟩ := source_count_continuous_argument hchi hprim hb (hy.trans hyH.le) (hreg chi)
  rw [hc chi 0 H hyH.le le_rfl] at he
  exact ⟨H, hyH, hHr, A, B, C, hl, he, fun alpha ha =>
    (Nat.cast_le.mpr (count_antitone_alpha chi y ha)).trans_eq he⟩

end LiuWang.Proof.DirichletZeroCount.Argument
