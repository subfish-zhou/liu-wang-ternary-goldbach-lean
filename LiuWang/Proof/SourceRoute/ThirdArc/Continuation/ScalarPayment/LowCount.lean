import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.StripScalar
import LiuWang.Proof.DirichletZeroCount.Remainder.UniformFamily

/-! A stronger frozen ordinary-count mother specialized to the full low-height family. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.DirichletZeroCount.Remainder

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment

theorem log_5001_le : Real.log (5001 : ℝ) ≤ 8.52 := by
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 8
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.52) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := mul_le_mul he ht (by norm_num) (by positivity)
  rw [← Real.exp_nat_mul, ← Real.exp_add] at h
  norm_num at h
  linarith

theorem lowHeight_shift_log_le : Real.log (lowHeight + 2) ≤ 11 := by
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
    (by linarith [Real.exp_one_gt_d9] : (2.7 : ℝ) ≤ Real.exp 1) 11
  rw [← Real.exp_nat_mul] at he
  norm_num at he
  apply (Real.log_le_iff_le_exp (by linarith [lowHeight_pos])).mpr
  unfold lowHeight
  nlinarith [Real.pi_lt_four]

theorem low_gamma_bound {a : ℝ} (ha : 0 < a) (ha4 : a ≤ 4) :
    sourceGammaMain a lowHeight - lowHeight * Real.log Real.pi ≤
      75200 * Real.pi + (3 / 2) * Real.pi := by
  have hnorm : ‖(a : ℂ) + (lowHeight : ℂ) * Complex.I‖ ≤ lowHeight + 4 := by
    calc
      _ ≤ ‖(a : ℂ)‖ + ‖(lowHeight : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = a + lowHeight := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos lowHeight_pos]
      _ ≤ _ := by linarith
  have hpos : 0 < ‖(a : ℂ) + (lowHeight : ℂ) * Complex.I‖ := by
    have h := Complex.re_le_norm ((a : ℂ) + (lowHeight : ℂ) * Complex.I)
    norm_num at h
    linarith
  have hratio : ‖(a : ℂ) + (lowHeight : ℂ) * Complex.I‖ / (2 * Real.pi) ≤ 5001 := by
    apply (div_le_iff₀ (by positivity)).mpr
    unfold lowHeight at hnorm ⊢
    nlinarith [Real.pi_gt_three]
  have hl := (Real.log_le_log (div_pos hpos (by positivity)) hratio).trans log_5001_le
  have hid : Real.log (‖(a : ℂ) + (lowHeight : ℂ) * Complex.I‖ / 2) - Real.log Real.pi =
      Real.log (‖(a : ℂ) + (lowHeight : ℂ) * Complex.I‖ / (2 * Real.pi)) := by
    rw [Real.log_div hpos.ne' (by norm_num), Real.log_div hpos.ne' (by positivity),
      Real.log_mul (by norm_num) Real.pi_ne_zero]
    ring
  have hat : (a - 1) * Real.arctan (lowHeight / a) ≤ (3 / 2) * Real.pi := by
    have hp := Real.arctan_nonneg.mpr (div_nonneg lowHeight_pos.le ha.le)
    have hu := (Real.arctan_lt_pi_div_two (lowHeight / a)).le
    by_cases ha1 : a ≤ 1
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hp).trans (by positivity)
    · have h := mul_le_mul_of_nonneg_left hu (by linarith : 0 ≤ a - 1)
      nlinarith [Real.pi_pos]
  have hmul := mul_le_mul_of_nonneg_left hl lowHeight_pos.le
  rw [← hid] at hmul
  unfold sourceGammaMain
  unfold lowHeight at hmul hat ⊢
  nlinarith

theorem low_uniform_horizontal {q : ℕ} (hq : 0 < q) :
    2 * uniformHorizontalFee q lowHeight ≤ Real.pi * (4 * Real.log q + 100) := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hh := lowHeight_shift_log_le
  have hp := Real.pi_gt_three
  have hmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ 5 * Real.pi / 2 + 4 by positivity)
  have hcouple := mul_nonneg (show 0 ≤ (3 / 2) * Real.pi - 4 by linarith) hlog
  unfold uniformHorizontalFee
  rw [abs_of_pos lowHeight_pos]
  nlinarith

theorem low_uniform_nonprincipal {q : ℕ} (hq : 0 < q) {a : ℝ}
    (ha : 0 < a) (ha4 : a ≤ 4) :
    uniformCountBound q a lowHeight ≤ 10004 * Real.log q + 76100 := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hg := low_gamma_bound ha ha4
  have hh := low_uniform_horizontal hq
  unfold uniformCountBound
  apply (div_le_iff₀ Real.pi_pos).mpr
  rw [Real.log_div hqR.ne' Real.pi_ne_zero]
  unfold lowHeight at hg hh ⊢
  nlinarith [Real.pi_pos]

theorem low_uniform_principal : uniformXiCountBound lowHeight ≤ 76100 := by
  have hg := low_gamma_bound (by norm_num : (0 : ℝ) < 4) le_rfl
  have hh := lowHeight_shift_log_le
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 5 * Real.pi / 2 + 4 by positivity)
  unfold uniformXiCountBound uniformXiFee
  rw [abs_of_pos lowHeight_pos]
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_gt_three]

theorem low_count_character {q : ℕ} [NeZero q] (chi : Character q)
    {alpha : ℝ} (ha : 0 ≤ alpha) :
    (count chi alpha lowHeight : ℝ) ≤ 10004 * Real.log q + 76100 := by
  by_cases hc : chi = 1
  · subst chi
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ q))
    exact ((principal_count_alpha_le_uniform q ha lowHeight_pos.le).trans low_uniform_principal).trans
      (by linarith)
  · apply (count_nonprincipal_uniform_modulus hc ha lowHeight_pos.le).trans
    apply low_uniform_nonprincipal (NeZero.pos q) (parityShift_pos chi)
    unfold parityShift
    split_ifs <;> norm_num

theorem low_count_family (q : ℕ) [NeZero q] {alpha : ℝ} (ha : 0 ≤ alpha) :
    (familyCount q alpha lowHeight : ℝ) ≤ q.totient * (10004 * Real.log q + 76100) := by
  have hc : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => low_count_character chi ha)
  simpa only [familyCount, Nat.cast_sum, Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul] using h

theorem low_count_family_source (q : ℕ) [NeZero q] {alpha : ℝ} (ha : 0 ≤ alpha) :
    (familyCount q alpha lowHeight : ℝ) ≤ q.totient * (10006.8423 * Real.log q + 76180) := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ q))
  exact (low_count_family q ha).trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment
