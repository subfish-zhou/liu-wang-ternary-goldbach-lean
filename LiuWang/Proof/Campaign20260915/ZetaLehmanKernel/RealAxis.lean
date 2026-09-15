import LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.ScalarLift
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaLehmanKernel

open LiuWang.Proof.Campaign20260915.ZetaWinding

def realPair (a : ℝ) : ℝ :=
  logNormPrimitive 0 (2 + a) + logNormPrimitive 0 (2 - a) -
    2 * (logNormPrimitive 0 (1 + a) + logNormPrimitive 0 (1 - a))

theorem zeroLoss_pair_real (a : ℝ) :
    zeroLoss a 0 + zeroLoss (-a) 0 = realPair a := by
  simp only [zeroLoss, realPair, logNormPrimitive, ↓reduceIte, Real.log_neg_eq_log]
  rw [show a + 2 = 2 + a by ring, show -a + 2 = 2 - a by ring,
    show a + 1 = 1 + a by ring, show -a + 1 = 1 - a by ring]
  ring

theorem logNormPrimitive_zero_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (logNormPrimitive 0) (Real.log x) x := by
  have he : logNormPrimitive 0 = fun u : ℝ => u * Real.log u - u := by
    funext u
    simp [logNormPrimitive]
  rw [he]
  convert! (Real.hasDerivAt_mul_log hx).sub (hasDerivAt_id x) using 1
  ring

theorem realPair_hasDerivAt {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    HasDerivAt realPair
      ((Real.log (2 + a) - Real.log (2 - a)) -
        2 * (Real.log (1 + a) - Real.log (1 - a))) a := by
  have h (c : ℝ) (hc : 1 ≤ c) :
      HasDerivAt (fun u => logNormPrimitive 0 (c + u) + logNormPrimitive 0 (c - u))
        (Real.log (c + a) - Real.log (c - a)) a := by
    have hp : c + a ≠ 0 := ne_of_gt (by linarith [ha.1])
    have hm : c - a ≠ 0 := ne_of_gt (by linarith [ha.2])
    convert! ((logNormPrimitive_zero_hasDerivAt hp).comp a
      ((hasDerivAt_id a).const_add c)).add
        ((logNormPrimitive_zero_hasDerivAt hm).comp a
          ((hasDerivAt_id a).const_sub c)) using 1
    simp [sub_eq_add_neg]
  exact (h 2 (by norm_num)).sub ((h 1 (by norm_num)).const_mul 2)

theorem realPair_antitone : AntitoneOn realPair (Set.Icc (0 : ℝ) (1 / 2)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
  · intro a ha
    exact (realPair_hasDerivAt ha).continuousAt.continuousWithinAt
  · intro a ha
    exact (realPair_hasDerivAt (interior_subset ha)).hasDerivWithinAt
  · intro a ha
    have ha' : a ∈ Set.Icc (0 : ℝ) (1 / 2) := interior_subset ha
    have hp : 0 < 1 - a := by linarith [ha'.2]
    have hp2 : 0 < 2 - a := by linarith [ha'.2]
    have h1 : 0 ≤ Real.log (1 + a) - Real.log (1 - a) :=
      sub_nonneg.mpr (Real.log_le_log hp (by linarith [ha'.1]))
    have h2 : Real.log (2 + a) - Real.log (2 - a) ≤
        Real.log (1 + a) - Real.log (1 - a) := by
      rw [← Real.log_div (by linarith [ha'.1] : 2 + a ≠ 0) hp2.ne',
        ← Real.log_div (by linarith [ha'.1] : 1 + a ≠ 0) hp.ne']
      apply Real.log_le_log (div_pos (by linarith [ha'.1]) hp2)
      rw [div_le_div_iff₀ hp2 hp]
      nlinarith [ha'.1]
    linarith

theorem realPair_neg (a : ℝ) : realPair (-a) = realPair a := by
  simp only [realPair, sub_eq_add_neg, neg_neg]
  ring

theorem zeroLoss_pair_real_le {a : ℝ} (ha : |a| ≤ (1 / 2 : ℝ)) :
    zeroLoss a 0 + zeroLoss (-a) 0 ≤ 14 / 5 := by
  have hm := realPair_antitone (by constructor <;> norm_num)
    (show |a| ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨abs_nonneg _, ha⟩) (abs_nonneg a)
  have he : realPair |a| = realPair a := by
    rcases le_total 0 a with hp | hn
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hn, realPair_neg]
  rw [he] at hm
  rw [zeroLoss_pair_real]
  have h0 : realPair 0 = 4 * Real.log 2 := by
    norm_num [realPair, logNormPrimitive]
    ring
  rw [h0] at hm
  linarith [Real.log_two_lt_d9]

theorem zeroLoss_pair_lift {a : ℝ} (ha : |a| ≤ (1 / 2 : ℝ)) (y : ℝ) :
    zeroLoss a y + zeroLoss (-a) y ≤
      (14 / 5 + 2 * y ^ 2) / (1 + y ^ 2) ^ 2 := by
  have hl := zeroLoss_lift y (abs_le.mp ha).1
  have hr := zeroLoss_lift y (a := -a) (by linarith [(abs_le.mp ha).2])
  have hreal := zeroLoss_pair_real_le ha
  have hd : 0 < (1 + y ^ 2) ^ 2 := by positivity
  rw [le_div_iff₀ hd] at hl hr ⊢
  nlinarith

#print axioms zeroLoss_pair_real_le
#print axioms zeroLoss_pair_lift

end LiuWang.Proof.Campaign20260915.ZetaLehmanKernel
