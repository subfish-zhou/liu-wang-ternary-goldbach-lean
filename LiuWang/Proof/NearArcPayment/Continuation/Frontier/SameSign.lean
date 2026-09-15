import LiuWang.Proof.NearArcPayment.Continuation.TailIntegral

/-! 同号对数相位无驻点；不要求 near-eta 条件，不包含实零点。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Interval
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier

open Interfaces Parameters OscillatoryBounds

theorem sameSign_phase_lower {gamma eta t : ℝ} (ht : 0 ≤ t)
    (hs : 0 ≤ eta * gamma) :
    |gamma| ≤ |gamma + 2 * Real.pi * eta * t| := by
  by_cases hg : 0 ≤ gamma
  · by_cases hz : gamma = 0
    · rw [hz, abs_zero]
      exact abs_nonneg _
    · have he : 0 ≤ eta := nonneg_of_mul_nonneg_left hs (lt_of_le_of_ne hg (Ne.symm hz))
      have hh : 0 ≤ 2 * Real.pi * eta * t := by positivity
      rw [abs_of_nonneg hg, abs_of_nonneg (add_nonneg hg hh)]
      linarith
  · have hg0 : gamma < 0 := lt_of_not_ge hg
    have he : eta ≤ 0 := by nlinarith
    have hh : 2 * Real.pi * eta * t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) he) ht
    rw [abs_of_neg hg0, abs_of_nonpos (by linarith)]
    linarith

theorem Jrho_sameSign {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hb : 0 ≤ rho.re) (hb1 : rho.re ≤ 1) (hg : rho.im ≠ 0) {eta : ℝ}
    (hs : 0 ≤ eta * rho.im) :
    ‖Jrho N rho eta‖ ≤ 4000 * (N : ℝ) ^ rho.re / |rho.im| := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ha : 0 < (N : ℝ) / 1000 := by positivity
  have hab : (N : ℝ) / 1000 ≤ N := by linarith
  have hG : 0 < |rho.im| := abs_pos.mpr hg
  have hr : rho ≠ 0 := by intro hz; exact hg (by simp [hz])
  have hsep : ∀ t ∈ Set.Icc ((N : ℝ) / 1000) N,
      (|rho.im| / (N : ℝ)) * t ≤ |rho.im + 2 * Real.pi * eta * t| := by
    intro t ht
    calc
      _ ≤ (|rho.im| / (N : ℝ)) * N :=
        mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = |rho.im| := div_mul_cancel₀ _ hn.ne'
      _ ≤ _ := sameSign_phase_lower (ha.trans_le ht.1).le hs
  have hk := norm_integral_cpow_charReal_first_derivative ha hab hr hb1
    (div_pos hG hn) hsep
  have hp : ((N : ℝ) / 1000) ^ rho.re ≤ (N : ℝ) ^ rho.re :=
    Real.rpow_le_rpow ha.le hab hb
  have he : ((N : ℝ) / 1000) ^ (rho.re - 1) =
      1000 * (((N : ℝ) / 1000) ^ rho.re) / (N : ℝ) := by
    rw [Real.rpow_sub_one ha.ne']
    ring
  change ‖∫ t in (N : ℝ) / 1000..(N : ℝ),
    (t : ℂ) ^ (rho - 1) * charReal (eta * t)‖ ≤ _
  apply hk.trans
  rw [he]
  calc
    _ = 4000 * (((N : ℝ) / 1000) ^ rho.re) / |rho.im| := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by norm_num)) hG.le

end LiuWang.Proof.NearArcPayment.Continuation.Frontier
