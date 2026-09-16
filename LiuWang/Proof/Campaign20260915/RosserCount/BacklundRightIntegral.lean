import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCells

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Finset

namespace LiuWang.Proof.Campaign20260915.RosserCount

def backlundRightProfile (θ : ℝ) : ℝ :=
  Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ))

theorem backlundRightProfile_continuousOn :
    ContinuousOn backlundRightProfile (Set.Icc 0 (Real.pi / 2)) := by
  have hd : ContinuousOn (fun σ => Real.log (backlundDirichletEnvelope 16 σ)) (Ioi 1) :=
    (backlundDirichletEnvelope_continuousOn (by norm_num : 1 ≤ 16)).log
      (fun σ hσ => (backlundDirichletEnvelope_pos (by norm_num) hσ).ne')
  apply hd.comp (by fun_prop : ContinuousOn
    (fun θ : ℝ => 5 / 4 + (33 / 25 : ℝ) * Real.cos θ) (Set.Icc 0 (Real.pi / 2)))
  intro θ hθ
  have hc := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  change 1 < 5 / 4 + (33 / 25 : ℝ) * Real.cos θ
  linarith

theorem backlundRightProfile_intervalIntegrable {a b : ℝ}
    (ha : a ∈ Set.Icc 0 (Real.pi / 2)) (hb : b ∈ Set.Icc 0 (Real.pi / 2)) :
    IntervalIntegrable backlundRightProfile volume a b :=
  (backlundRightProfile_continuousOn.mono
    (Set.uIcc_subset_Icc ha hb)).intervalIntegrable

theorem backlund_right_integral_bound :
    (∫ θ in (0 : ℝ)..Real.pi / 2, backlundRightProfile θ) ≤
      Real.pi * (5471 / 20000) := by
  let a : ℕ → ℝ := fun j => (j : ℝ) * Real.pi / 128
  have ha (j : ℕ) (hj : j ≤ 64) : a j ∈ Set.Icc 0 (Real.pi / 2) := by
    have hjR : (j : ℝ) ≤ 64 := by exact_mod_cast hj
    constructor
    · dsimp [a]; positivity
    · dsimp [a]; nlinarith [Real.pi_pos]
  have hi (j : ℕ) (hj : j < 64) :
      IntervalIntegrable backlundRightProfile volume (a j) (a (j + 1)) :=
    backlundRightProfile_intervalIntegrable (ha j (by omega)) (ha (j + 1) (by omega))
  have hcell (j : ℕ) (hj : j < 64) :
      (∫ θ in a j..a (j + 1), backlundRightProfile θ) ≤
        (Real.pi / 128) * (backlundRightLogUpper j : ℝ) := by
    have hab : a j ≤ a (j + 1) := by dsimp [a]; push_cast; nlinarith [Real.pi_pos]
    have h := intervalIntegral.integral_mono_on hab (hi j hj)
      (intervalIntegrable_const (c := (backlundRightLogUpper j : ℝ))) (fun θ hθ => by
        exact backlund_right_all_cells hj ((ha j (by omega)).1.trans hθ.1) hθ.2)
    rw [intervalIntegral.integral_const] at h
    have he : a (j + 1) - a j = Real.pi / 128 := by dsimp [a]; push_cast; ring
    simpa only [he, smul_eq_mul] using h
  have hsum := sum_le_sum (fun j hj => hcell j (mem_range.mp hj))
  have he := intervalIntegral.sum_integral_adjacent_intervals hi
  rw [he, ← Finset.mul_sum] at hsum
  have hs : (∑ j ∈ range 64, (backlundRightLogUpper j : ℝ)) = 21884 / 625 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) backlund_right_log_sum
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using h
  rw [hs] at hsum
  have ha0 : a 0 = 0 := by simp [a]
  have ha64 : a 64 = Real.pi / 2 := by dsimp [a]; ring
  rw [ha0, ha64] at hsum
  exact hsum.trans_eq (by ring)

#print axioms backlundRightProfile_continuousOn
#print axioms backlundRightProfile_intervalIntegrable
#print axioms backlund_right_integral_bound

end LiuWang.Proof.Campaign20260915.RosserCount
