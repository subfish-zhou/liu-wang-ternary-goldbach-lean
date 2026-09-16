import LiuWang.Proof.Campaign20260915.RosserCount.BacklundFiftyBox

set_option autoImplicit false
noncomputable section

open Complex Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

def backlundFiftyTerm (s : ℂ) (n : ℕ) : ℂ :=
  ((backlundFiftyWeight n : ℝ) : ℂ) * (n : ℂ) ^ (-s)

def backlundFiftyMain (s : ℂ) : ℂ :=
  1 + ∑ j ∈ Finset.range 9, backlundFiftyTerm s (j + 2)

private theorem nonnegative_amplitude_interval {a U x l u : ℝ}
    (ha : 0 ≤ a) (hU : a ≤ U) (hl : l ≤ x) (hu : x ≤ u) :
    min 0 l * U ≤ a * x ∧ a * x ≤ max 0 u * U := by
  constructor
  · calc
      _ ≤ min 0 l * a := mul_le_mul_of_nonpos_left hU (min_le_left _ _)
      _ = a * min 0 l := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hl) ha
  · calc
      _ ≤ a * max 0 u := mul_le_mul_of_nonneg_left (hu.trans (le_max_right _ _)) ha
      _ = max 0 u * a := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hU (le_max_left _ _)

theorem backlund_fifty_cpow {s : ℂ} (ht : s.im = 50)
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ (-s) = (((n : ℝ) ^ (-s.re) : ℝ) : ℂ) *
      Complex.exp (((-50 * Real.log (n : ℝ) : ℝ) : ℂ) * I) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hp : -s = ((-s.re : ℝ) : ℂ) + (-50 : ℂ) * I := by
    apply Complex.ext <;> simp [ht]
  have hr : (n : ℂ) ^ ((-s.re : ℝ) : ℂ) = (((n : ℝ) ^ (-s.re) : ℝ) : ℂ) := by
    simpa only [ofReal_natCast] using (Complex.ofReal_cpow (Nat.cast_nonneg n) (-s.re)).symm
  rw [hp, cpow_add _ _ hnC, hr, cpow_def_of_ne_zero hnC]
  have hlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    simpa only [ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [hlog]
  congr 1
  congr 1
  push_cast
  ring

theorem backlundFiftyTerm_rect {s : ℂ} (hs : 1 / 2 ≤ s.re) (ht : s.im = 50)
    {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 10) :
    ((backlundFiftyRect n).1.1 : ℝ) ≤ (backlundFiftyTerm s n).re ∧
      (backlundFiftyTerm s n).re ≤ ((backlundFiftyRect n).1.2 : ℝ) ∧
      ((backlundFiftyRect n).2.1 : ℝ) ≤ (backlundFiftyTerm s n).im ∧
      (backlundFiftyTerm s n).im ≤ ((backlundFiftyRect n).2.2 : ℝ) := by
  let u := Complex.exp (((-50 * Real.log (n : ℝ) : ℝ) : ℂ) * I)
  let a : ℝ := (backlundFiftyWeight n : ℝ) * (n : ℝ) ^ (-s.re)
  let U : ℝ := (backlundFiftyWeight n * reciprocalSqrtUpper n 1000 : ℚ)
  have hw : (0 : ℝ) ≤ backlundFiftyWeight n := by
    dsimp [backlundFiftyWeight]
    split <;> norm_num
  have ha : 0 ≤ a := mul_nonneg hw (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hpow : (n : ℝ) ^ (-s.re) ≤ 1 / Real.sqrt (n : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
      _ = _ := by rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, one_div]
  have hU : a ≤ U := by
    have h := mul_le_mul_of_nonneg_left
      (hpow.trans (reciprocalSqrt_enclosure hn (by norm_num : 1 ≤ 1000)).2) hw
    simpa only [a, U, Rat.cast_mul] using h
  have he : ‖u - (backlundFiftyPhase n).toComplex‖ ≤ 13747 / 100000000 :=
    backlundFiftyPhase_error hn hn'
  have hr : |u.re - ((backlundFiftyPhase n).1 : ℝ)| ≤ 13747 / 100000000 := by
    simpa [QComplex.toComplex] using (abs_re_le_norm (u - (backlundFiftyPhase n).toComplex)).trans he
  have hi : |u.im - ((backlundFiftyPhase n).2 : ℝ)| ≤ 13747 / 100000000 := by
    simpa [QComplex.toComplex] using (abs_im_le_norm (u - (backlundFiftyPhase n).toComplex)).trans he
  have hrb := nonnegative_amplitude_interval (x := u.re) ha hU
    (show ((backlundFiftyPhase n).1 : ℝ) - 13747 / 100000000 ≤ u.re by
      linarith [(abs_le.mp hr).1])
    (show u.re ≤ ((backlundFiftyPhase n).1 : ℝ) + 13747 / 100000000 by
      linarith [(abs_le.mp hr).2])
  have hib := nonnegative_amplitude_interval (x := u.im) ha hU
    (show ((backlundFiftyPhase n).2 : ℝ) - 13747 / 100000000 ≤ u.im by
      linarith [(abs_le.mp hi).1])
    (show u.im ≤ ((backlundFiftyPhase n).2 : ℝ) + 13747 / 100000000 by
      linarith [(abs_le.mp hi).2])
  have hterm : backlundFiftyTerm s n = (a : ℂ) * u := by
    rw [backlundFiftyTerm, backlund_fifty_cpow ht hn]
    dsimp [a, u]
    push_cast
    ring
  rw [hterm]
  dsimp [backlundFiftyRect]
  push_cast
  have hcomb := And.intro hrb.1 (And.intro hrb.2 hib)
  simpa only [U, Rat.cast_mul, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul,
    sub_zero, add_zero] using hcomb

theorem backlundFiftyMain_rect {s : ℂ} (hs : 1 / 2 ≤ s.re) (ht : s.im = 50) :
    -(1 : ℝ) ≤ (backlundFiftyMain s).re ∧ (backlundFiftyMain s).re ≤ 33 / 20 ∧
      -(1 : ℝ) ≤ (backlundFiftyMain s).im ∧ (backlundFiftyMain s).im ≤ 59 / 50 := by
  have h (j : ℕ) (hj : j ∈ range 9) := backlundFiftyTerm_rect hs ht
    (n := j + 2) (by omega) (by have h := mem_range.mp hj; omega)
  have hrl := sum_le_sum (fun j hj => (h j hj).1)
  have hru := sum_le_sum (fun j hj => (h j hj).2.1)
  have hil := sum_le_sum (fun j hj => (h j hj).2.2.1)
  have hiu := sum_le_sum (fun j hj => (h j hj).2.2.2)
  have hb := backlundFiftyBox_bounds
  have hbl : (-1 : ℝ) ≤ (backlundFiftyBox.1.1 : ℝ) := by exact_mod_cast hb.1
  have hbu : (backlundFiftyBox.1.2 : ℝ) ≤ 33 / 20 := by
    have h : (backlundFiftyBox.1.2 : ℝ) ≤ ((33 / 20 : ℚ) : ℝ) := Rat.cast_le.mpr hb.2.1
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  have hbi : (-1 : ℝ) ≤ (backlundFiftyBox.2.1 : ℝ) := by exact_mod_cast hb.2.2.1
  have hbj : (backlundFiftyBox.2.2 : ℝ) ≤ 59 / 50 := by
    have h : (backlundFiftyBox.2.2 : ℝ) ≤ ((59 / 50 : ℚ) : ℝ) := Rat.cast_le.mpr hb.2.2.2
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  dsimp [backlundFiftyBox] at hbl hbu hbi hbj
  push_cast at hbl hbu hbi hbj
  simp only [backlundFiftyMain, add_re, one_re, add_im, one_im, zero_add, re_sum, im_sum]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem backlundFiftyMain_norm_lt {s : ℂ} (hs : 1 / 2 ≤ s.re) (ht : s.im = 50) :
    ‖backlundFiftyMain s‖ < 21 / 10 := by
  obtain ⟨hrl, hru, hil, hiu⟩ := backlundFiftyMain_rect hs ht
  have hr : (backlundFiftyMain s).re ^ 2 ≤ (33 / 20 : ℝ) ^ 2 := by nlinarith
  have hi : (backlundFiftyMain s).im ^ 2 ≤ (59 / 50 : ℝ) ^ 2 := by nlinarith
  have hn := Complex.sq_norm (backlundFiftyMain s)
  rw [normSq_apply] at hn
  nlinarith [norm_nonneg (backlundFiftyMain s)]

theorem backlundFiftyMain_partial_sum (s : ℂ) :
    backlundFiftyMain s = zetaPartialSum s 10 - (10 : ℂ) ^ (-s) / 2 := by
  norm_num only [backlundFiftyMain, backlundFiftyTerm, backlundFiftyWeight,
    zetaPartialSum, sum_range_succ, sum_range_zero, Nat.reduceAdd,
    Nat.cast_ofNat, one_cpow, Rat.cast_one, ofReal_one, one_mul]
  norm_num
  ring

#print axioms backlund_fifty_cpow
#print axioms backlundFiftyTerm_rect
#print axioms backlundFiftyMain_rect
#print axioms backlundFiftyMain_norm_lt
#print axioms backlundFiftyMain_partial_sum

end LiuWang.Proof.Campaign20260915.RosserCount
