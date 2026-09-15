import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.PowerMoments
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Consumers

set_option autoImplicit false
noncomputable section
open Finset
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart

theorem unweighted_high_prefix_real {s P : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) (hP : 1 ≤ P) :
    (∑ q ∈ denominators P, (q : ℝ) ^ s / (q.totient : ℝ) ^ 2) ≤
      10.3 * (1 + P ^ (s - 1) / (s - 1)) := by
  have hfloor : 1 ≤ ⌊P⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hP)
  apply (unweighted_high_prefix hs1 hs2 hfloor).trans
  have hs : 0 < s - 1 := by linarith
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) hs.le) hs.le))
    (by norm_num)

theorem first_moment_no_RS {P : ℝ} (hP : 100000 ≤ P) :
    totientMoment P (1 / 6) ≤ 3.286 := by
  have ht := unweighted_tail_le (by norm_num : (1 / 6 : ℝ) < 1)
    (m := 100001) (B := ⌊P⌋₊) (by norm_num)
  norm_num only at ht
  have he : (100001 : ℝ) ^ (-5 / 6 : ℝ) ≤ (100000 : ℝ) ^ (-5 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (by norm_num)
  have hnum : (∑ q ∈ Icc 100001 ⌊P⌋₊, (q : ℝ) ^ (1 / 6 : ℝ) / (q.totient : ℝ) ^ 2) ≤
      0.00155 := by
    have hlow := low_endpoint_power
    norm_num only at he hlow
    linarith only [ht, he, hlow]
  linarith only [totientMoment_split_le hP (1 / 6), original_first_head, hnum]

theorem source_negative_power_le {P e : ℝ} (hP : 10000000000 ≤ P) (he : e ≤ -4 / 5) :
    P ^ e ≤ 0.00000001 := by
  have hp : 0 < P := by linarith
  calc
    _ ≤ P ^ (-4 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) he
    _ ≤ (10000000000 : ℝ) ^ (-4 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hP (by norm_num)
    _ = _ := by
      rw [show (10000000000 : ℝ) = (10 : ℝ) ^ (10 : ℕ) by norm_num,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num

theorem source_high_sixth_moment_no_RS {P : ℝ} (hP : 10000000000 ≤ P) :
    totientMoment P (7 / 6) / P ≤ 0.000001 := by
  have hp : 0 < P := by linarith
  have h := unweighted_high_prefix_real (by norm_num : (1 : ℝ) < 7 / 6)
    (by norm_num) (show 1 ≤ P by linarith)
  have hm : totientMoment P (7 / 6) ≤ 10.3 * (1 + P ^ (1 / 6 : ℝ) / (1 / 6)) := by
    exact (sum_le_sum (fun q _ => totient_weight_le_unweighted q (7 / 6))).trans
      (by convert! h using 1; norm_num)
  have hdiv : 1 / P ≤ 1 / (10000000000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hP
  have he : P ^ (1 / 6 : ℝ) / P = P ^ (-5 / 6 : ℝ) := by
    rw [show (-5 / 6 : ℝ) = (1 / 6) - 1 by norm_num, Real.rpow_sub hp, Real.rpow_one]
  calc
    _ ≤ (10.3 * (1 + P ^ (1 / 6 : ℝ) / (1 / 6))) / P :=
      div_le_div_of_nonneg_right hm hp.le
    _ = 10.3 * (1 / P) + 61.8 * P ^ (-5 / 6 : ℝ) := by rw [← he]; ring
    _ ≤ 10.3 * (1 / 10000000000) + 61.8 * 0.00000001 :=
      add_le_add (mul_le_mul_of_nonneg_left hdiv (by norm_num))
        (mul_le_mul_of_nonneg_left (source_negative_power_le hP (by norm_num)) (by norm_num))
    _ ≤ _ := by norm_num

theorem I12_no_RS {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    ‖I12 N‖ ≤ 0.1108 * (N : ℝ) ^ 2 := by
  have hP := sourceP_ge_ten_billion hN
  have hm1 := first_moment_no_RS (show 100000 ≤ sourceP N by linarith)
  have hm7 := source_high_sixth_moment_no_RS hP
  have hscalar :
      linearPrefactor * (0.0194 * totientMoment (sourceP N) (1 / 6) +
        (5 * 0.0126 / sourceL N ^ 3) * totientMoment (sourceP N) (7 / 6)) ≤ 0.1108 := by
    have he : (5 * 0.0126 / sourceL N ^ 3) * totientMoment (sourceP N) (7 / 6) =
        0.063 * (totientMoment (sourceP N) (7 / 6) / sourceP N) := by
      unfold sourceP
      ring
    rw [he]
    calc
      _ ≤ linearPrefactor * (0.0194 * 3.286 + 0.063 * 0.000001) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hm1, hm7])
          (by unfold linearPrefactor; positivity)
      _ ≤ 1.7376 * (0.0194 * 3.286 + 0.063 * 0.000001) :=
        mul_le_mul_of_nonneg_right linearPrefactor_le (by norm_num)
      _ ≤ _ := by norm_num
  apply (I12_source417 hN hlow hhigh).trans
  convert! mul_le_mul_of_nonneg_right hscalar (sq_nonneg (N : ℝ)) using 1
  ring

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart
