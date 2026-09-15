import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.ActualHeight

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

def actualM1 (N q : ℕ) [NeZero q] : ℝ :=
  ∫ y in omegaCutoff N q..middleUpper N q, heightKernel y *
    ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
      alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)

def actualLowPart (N q : ℕ) [NeZero q] : ℝ :=
  if densityGate q ≤ omegaCutoff N q then 0 else lowHeightIntegral N q

theorem actual_M1_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    actualM1 N q = actualLowPart N q +
      ∫ y in max (omegaCutoff N q) (densityGate q)..middleUpper N q, heightKernel y *
        ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ) := by
  unfold actualLowPart
  by_cases hg : densityGate q ≤ omegaCutoff N q
  · rw [if_pos hg, max_eq_left hg, zero_add]
    rfl
  · rw [if_neg hg, max_eq_right (le_of_not_ge hg)]
    exact actual_density_height_split hN hq (le_of_not_ge hg)

theorem actual_low_height_normalized {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) :
    (8 * Real.sqrt q / q.totient) * lowHeightIntegral N q ≤
      8 * originalLowScalar (sourceL N) / sourceL N := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hphi : (q.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hL : sourceL N ≠ 0 := by linarith [sourceL_ge_3100 hN]
  have hb := mul_le_mul_of_nonneg_left (actual_low_height_le_original hN hq hgate)
    (by positivity : 0 ≤ 8 * Real.sqrt q / q.totient)
  have he : (8 * Real.sqrt q / q.totient) *
      ((q.totient / Real.sqrt q) * (originalLowScalar (sourceL N) / sourceL N)) =
        8 * originalLowScalar (sourceL N) / sourceL N := by
    calc
      _ = (8 * Real.sqrt q / q.totient) *
          (originalLowScalar (sourceL N) * (q.totient / Real.sqrt q) / sourceL N) := by ring
      _ = _ := normalized_low_fee hq0 hphi hL
  rwa [he] at hb

theorem actual_M1_high_only {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : densityGate q ≤ omegaCutoff N q)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (8 * Real.sqrt q / q.totient) * actualM1 N q ≤
      ((32281 : ℝ) / 1000000) / sourceL N :=
  Fixed032281.actual_high_alpha_height_032281 hN hq le_rfl
    (middle_height_domain hN hq).2.1 hgate hseven hnu

theorem actual_M1_le_original_low_scalar {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (8 * Real.sqrt q / q.totient) * actualM1 N q ≤
      ((32281 : ℝ) / 1000000 + 8 * originalLowScalar (sourceL N)) / sourceL N := by
  by_cases hg : densityGate q ≤ omegaCutoff N q
  · apply (actual_M1_high_only hN hq hg hseven hnu).trans
    apply div_le_div_of_nonneg_right _ (by linarith [sourceL_ge_3100 hN])
    linarith [originalLowScalar_nonneg (sourceL_ge_3100 hN)]
  · have hl := actual_low_height_normalized hN hq (le_of_not_ge hg)
    have hh := Fixed032281.actual_high_branch_032281 hN hq hseven hnu
    rw [actual_M1_split hN hq, mul_add]
    rw [actualLowPart, if_neg hg]
    calc
      _ ≤ 8 * originalLowScalar (sourceL N) / sourceL N +
          ((32281 : ℝ) / 1000000) / sourceL N := add_le_add hl hh
      _ = _ := by ring

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight
