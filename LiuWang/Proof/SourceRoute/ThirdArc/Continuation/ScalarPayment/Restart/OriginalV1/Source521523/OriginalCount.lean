import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.BaseScalar
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.LowCount
import LiuWang.Proof.DirichletZeroCount.Remainder.SourceFamily

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.DirichletZeroCount.Remainder

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523

theorem low_norm_ge_one (a : ℂ) (ha : a.im = 0) :
    1 ≤ ‖a + (lowHeight : ℂ) * Complex.I‖ := by
  have h : lowHeight ≤ ‖a + (lowHeight : ℂ) * Complex.I‖ := by
    simpa [ha] using Complex.im_le_norm (a + (lowHeight : ℂ) * Complex.I)
  have hh : 1 ≤ lowHeight := by unfold lowHeight; linarith [Real.pi_gt_three]
  exact hh.trans h

theorem source_six_low_main {q : ℕ} (hq : 0 < q) :
    lowHeight / Real.pi *
      Real.log ((q : ℝ) * ‖(3 / 2 : ℂ) + (lowHeight : ℂ) * Complex.I‖ / (2 * Real.pi)) -
      lowHeight / Real.pi + 1 / (2 * Real.pi) * Real.arctan (2 * lowHeight / 3) ≤
        10000 * Real.log q + 75201.5 := by
  have hq0 : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hq).ne'
  have hn0 : ‖(3 / 2 : ℂ) + (lowHeight : ℂ) * Complex.I‖ ≠ 0 := by
    linarith [low_norm_ge_one (3 / 2) (by norm_num)]
  have he :
      lowHeight / Real.pi *
        Real.log ((q : ℝ) * ‖(3 / 2 : ℂ) + (lowHeight : ℂ) * Complex.I‖ / (2 * Real.pi)) -
        lowHeight / Real.pi + 1 / (2 * Real.pi) * Real.arctan (2 * lowHeight / 3) =
      10000 * Real.log q +
        (sourceGammaMain (3 / 2) lowHeight - lowHeight * Real.log Real.pi) / Real.pi := by
    unfold sourceGammaMain
    push_cast
    rw [Real.log_div (mul_ne_zero hq0 hn0) (by positivity),
      Real.log_mul hq0 hn0, Real.log_mul (by norm_num) Real.pi_ne_zero,
      Real.log_div hn0 (by norm_num)]
    rw [show lowHeight / (3 / 2 : ℝ) = 2 * lowHeight / 3 by ring]
    unfold lowHeight
    field_simp [Real.pi_ne_zero]
    ring
  rw [he]
  have h := low_gamma_bound (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num)
  have hd : (sourceGammaMain (3 / 2) lowHeight - lowHeight * Real.log Real.pi) /
      Real.pi ≤ 75201.5 := (div_le_iff₀ Real.pi_pos).mpr (by linarith)
  linarith

theorem source_six_low_bound {q : ℕ} (hq : 0 < q) :
    sourceSixBound q lowHeight ≤ originalCountFactor q := by
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)
  have hheight := lowHeight_shift_log_le
  have hh0 := lowHeight_pos
  have hcoef : 7 * (1 + 3 / Real.pi) ≤ (13.6846 : ℝ) := by
    have hd : 21 / Real.pi ≤ (6.6846 : ℝ) :=
      (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_d6])
    simp only [div_eq_mul_inv] at hd ⊢
    linarith
  have hprod : Real.log ((q : ℝ) * (2 + lowHeight)) ≤ Real.log q + 11 := by
    rw [Real.log_mul (Nat.cast_pos.mpr hq).ne' (by positivity)]
    rw [add_comm 2 lowHeight]
    linarith
  have hln : 0 ≤ Real.log ((q : ℝ) * (2 + lowHeight)) := by
    apply Real.log_nonneg
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [lowHeight_pos]
  have hfee := mul_le_mul hcoef
    (show 0.5 * Real.log ((q : ℝ) * (2 + lowHeight)) + 0.59773 ≤
      0.5 * (Real.log q + 11) + 0.59773 by linarith)
    (by positivity) (by norm_num)
  have hr : 1 / (4 * ‖(1 / 2 : ℂ) + (lowHeight : ℂ) * Complex.I‖) ≤ (1 / 4 : ℝ) :=
    (div_le_iff₀ (by nlinarith [low_norm_ge_one (1 / 2) (by norm_num)])).mpr
      (by nlinarith [low_norm_ge_one (1 / 2) (by norm_num)])
  have hnorm : 1 ≤ ‖(0.5 : ℂ) + (lowHeight : ℂ) * Complex.I‖ *
      ‖(2 : ℂ) + (lowHeight : ℂ) * Complex.I‖ :=
    one_le_mul_of_one_le_of_one_le (low_norm_ge_one 0.5 (by norm_num)) (low_norm_ge_one 2 (by norm_num))
  have hrec : 1.5 / (‖(0.5 : ℂ) + (lowHeight : ℂ) * Complex.I‖ *
      ‖(2 : ℂ) + (lowHeight : ℂ) * Complex.I‖) ≤ (1.5 : ℝ) :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hpi : 4 / Real.pi ≤ (4 / 3 : ℝ) :=
    (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  have ht := mul_le_mul hpi (show 0.6105 + 1.5 /
      (‖(0.5 : ℂ) + (lowHeight : ℂ) * Complex.I‖ *
        ‖(2 : ℂ) + (lowHeight : ℂ) * Complex.I‖) + 1.5 / 4 ≤
      (0.6105 + 1.5 + 1.5 / 4 : ℝ) by linarith)
    (by positivity) (by norm_num)
  have hm := source_six_low_main hq
  unfold sourceSixBound originalCountFactor
  linarith only [hm, hr, hfee, ht]

theorem source_five_low_bound : sourceFiveBound lowHeight ≤ (76180 : ℝ) := by
  have hh0 := lowHeight_pos
  have he :
      lowHeight / Real.pi * Real.log (Real.sqrt ((5 / 4 : ℝ) ^ 2 + (lowHeight / 2) ^ 2)) +
      3 / (2 * Real.pi) * Real.arctan (2 * lowHeight / 5) -
      (1 + Real.log Real.pi) / Real.pi * lowHeight =
      (sourceGammaMain (5 / 2) lowHeight - lowHeight * Real.log Real.pi) / Real.pi := by
    rw [sourceFive_norm_identity]
    unfold sourceGammaMain
    rw [show lowHeight / (5 / 2 : ℝ) = 2 * lowHeight / 5 by ring]
    field_simp [Real.pi_ne_zero]
    ring
  have hm : (sourceGammaMain (5 / 2) lowHeight - lowHeight * Real.log Real.pi) /
      Real.pi ≤ 75201.5 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [low_gamma_bound (by norm_num : (0 : ℝ) < 5 / 2) (by norm_num)]
  have hs : 5 ≤ Real.sqrt (25 + 4 * lowHeight ^ 2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [sq_nonneg lowHeight]
  have hr : 1 / (2 * Real.sqrt (25 + 4 * lowHeight ^ 2)) ≤ (1 / 10 : ℝ) :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hd : 0.25 / (0.0625 + lowHeight ^ 2) ≤ (4 : ℝ) :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith [sq_nonneg lowHeight])
  have hc : 10.5 * (2.25 + Real.pi) / Real.pi ≤ (19 : ℝ) :=
    (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  have hl : Real.log (2 + lowHeight) ≤ 11 := by simpa only [add_comm] using lowHeight_shift_log_le
  have hfee := mul_le_mul hc (show 0.5 * Real.log (2 + lowHeight) +
      0.25 / (0.0625 + lowHeight ^ 2) + 2.6459 ≤ (0.5 * 11 + 4 + 2.6459 : ℝ) by linarith)
    (by have hh := Real.log_nonneg (by linarith [lowHeight_pos] : 1 ≤ 2 + lowHeight); positivity)
    (by norm_num)
  have hn : 1 / ‖(1 : ℂ) + (lowHeight : ℂ) * Complex.I‖ ≤ (1 : ℝ) :=
    (div_le_iff₀ (by nlinarith [low_norm_ge_one 1 (by norm_num)])).mpr
      (by simpa using low_norm_ge_one 1 (by norm_num))
  have hy : 1 / lowHeight ≤ (1 : ℝ) :=
    (div_le_iff₀ lowHeight_pos).mpr (by unfold lowHeight; linarith [Real.pi_gt_three])
  have hp : 3 / Real.pi ≤ (1 : ℝ) :=
    (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  have htail := mul_le_mul hp (show 0.6105 + 1 /
      ‖(1 : ℂ) + (lowHeight : ℂ) * Complex.I‖ + 1 / lowHeight + 1.5 / 4 ≤
      (0.6105 + 1 + 1 + 1.5 / 4 : ℝ) by linarith) (by positivity) (by norm_num)
  unfold sourceFiveBound
  rw [he]
  linarith only [hm, hr, hfee, htail]

theorem original_count_character {q : ℕ} [NeZero q] (chi : Character q)
    {alpha : ℝ} (ha : 1 / 2 ≤ alpha) :
    (count chi alpha lowHeight : ℝ) ≤ originalCountFactor q := by
  by_cases hc : chi = 1
  · subst chi
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast (NeZero.one_le : 1 ≤ q))
    exact ((count_principal_le_sourceFive q (by linarith) lowHeight_pos).trans
      source_five_low_bound).trans (by unfold originalCountFactor; linarith)
  · exact (count_nonprincipal_le_sourceSix_modulus hc (by linarith) lowHeight_pos.le).trans
      (source_six_low_bound (NeZero.pos q))

theorem original_count_family (q : ℕ) [NeZero q] {alpha : ℝ} (ha : 1 / 2 ≤ alpha) :
    (familyCount q alpha lowHeight : ℝ) ≤ q.totient * originalCountFactor q := by
  have hc : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => original_count_character chi ha)
  simpa only [familyCount, Nat.cast_sum, Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul] using h

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523
