import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.LowCount
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.DensityLogs

/-! A uniform actual ordinary-L family count for the middle and high height windows. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.DirichletZeroCount.Remainder

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

theorem ordinary_height_logs {y : ℝ} (hy : lowHeight ≤ y) :
    30000 ≤ y ∧ 10 ≤ Real.log y ∧ Real.log (y + 2) ≤ Real.log y + 1 := by
  have hy0 := lowHeight_pos.trans_le hy
  have hybig : 30000 ≤ y := by unfold lowHeight at hy; nlinarith [Real.pi_gt_three]
  have hlog := lowHeight_log_bounds.1.trans (Real.log_le_log lowHeight_pos hy)
  refine ⟨hybig, hlog, ?_⟩
  have h := Real.log_le_log (by linarith : 0 < y + 2) (show y + 2 ≤ y * 2 by linarith)
  rw [Real.log_mul hy0.ne' (by norm_num)] at h
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  linarith

theorem ordinary_gamma_bound {a y : ℝ} (ha : 0 < a) (ha4 : a ≤ 4)
    (hy : lowHeight ≤ y) :
    sourceGammaMain a y - y * Real.log Real.pi ≤ y * Real.log y - y + (3 / 2) * Real.pi := by
  have hy0 := lowHeight_pos.trans_le hy
  have hybig := (ordinary_height_logs hy).1
  have hn : ‖(a : ℂ) + (y : ℂ) * Complex.I‖ ≤ y + 4 := by
    calc
      _ ≤ ‖(a : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = a + y := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hy0]
      _ ≤ _ := by linarith
  have hn0 : 0 < ‖(a : ℂ) + (y : ℂ) * Complex.I‖ := by
    have h := Complex.re_le_norm ((a : ℂ) + (y : ℂ) * Complex.I)
    norm_num at h
    linarith
  have hr : ‖(a : ℂ) + (y : ℂ) * Complex.I‖ / (2 * Real.pi) ≤ y := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hl := Real.log_le_log (div_pos hn0 (by positivity)) hr
  rw [Real.log_div hn0.ne' (by positivity), Real.log_mul (by norm_num) Real.pi_ne_zero] at hl
  have hl := mul_le_mul_of_nonneg_left hl hy0.le
  have har : (a - 1) * Real.arctan (y / a) ≤ (3 / 2) * Real.pi := by
    have hp := Real.arctan_nonneg.mpr (div_nonneg hy0.le ha.le)
    have hu := (Real.arctan_lt_pi_div_two (y / a)).le
    by_cases ha1 : a ≤ 1
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hp).trans (by positivity)
    · have hh := mul_le_mul_of_nonneg_left hu (by linarith : 0 ≤ a - 1)
      nlinarith [Real.pi_pos]
  unfold sourceGammaMain
  rw [Real.log_div hn0.ne' (by norm_num)]
  nlinarith

theorem ordinary_horizontal_bound {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : lowHeight ≤ y) :
    2 * uniformHorizontalFee q y ≤ Real.pi * (4 * (Real.log q + Real.log y) + 30) := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hh := ordinary_height_logs hy
  have hm := mul_le_mul_of_nonneg_left hh.2.2 (show 0 ≤ 5 * Real.pi / 2 + 4 by positivity)
  have hu := mul_nonneg (show 0 ≤ (3 / 2) * Real.pi - 4 by linarith [Real.pi_gt_three])
    (show 0 ≤ Real.log q + Real.log y + 5 by linarith [hh.2.1])
  unfold uniformHorizontalFee
  rw [abs_of_pos (lowHeight_pos.trans_le hy)]
  nlinarith [Real.pi_gt_three]

theorem ordinary_scalar_absorption {y u : ℝ} (hy : 30000 ≤ y) (hu : 10 ≤ u) :
    y * u + Real.pi * (4 * u + 33) ≤ Real.pi * y * u / 3 := by
  have hyp : 0 ≤ y * u := by positivity
  have hpi : (3.12 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have h1 := mul_le_mul_of_nonneg_right hpi hyp
  have h2 := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (show 0 ≤ 4 * u + 33 by linarith)
  have h3 := mul_le_mul_of_nonneg_right hy (show 0 ≤ u by linarith)
  nlinarith only [h1, h2, h3, hu]

theorem ordinary_uniform_nonprincipal {q : ℕ} (hq : 0 < q) {a y : ℝ}
    (ha : 0 < a) (ha4 : a ≤ 4) (hy : lowHeight ≤ y) :
    uniformCountBound q a y ≤ (y / 3) * Real.log ((q : ℝ) * y) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hqlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hh := ordinary_height_logs hy
  have hg := ordinary_gamma_bound ha ha4 hy
  have hf := ordinary_horizontal_bound hq hy
  have habs := ordinary_scalar_absorption hh.1 (show 10 ≤ Real.log q + Real.log y by linarith [hh.2.1])
  unfold uniformCountBound
  apply (div_le_iff₀ Real.pi_pos).mpr
  rw [Real.log_div hq0.ne' Real.pi_ne_zero,
    Real.log_mul hq0.ne' (lowHeight_pos.trans_le hy).ne']
  nlinarith [Real.pi_pos]

theorem ordinary_uniform_principal {y : ℝ} (hy : lowHeight ≤ y) :
    uniformXiCountBound y ≤ (y / 3) * Real.log y := by
  have hh := ordinary_height_logs hy
  have hg := ordinary_gamma_bound (by norm_num : (0 : ℝ) < 4) le_rfl hy
  have hm := mul_le_mul_of_nonneg_left hh.2.2 (show 0 ≤ 5 * Real.pi / 2 + 4 by positivity)
  have hu := mul_nonneg (show 0 ≤ (3 / 2) * Real.pi - 4 by linarith [Real.pi_gt_three])
    (show 0 ≤ Real.log y + 6 by linarith [hh.2.1])
  have habs := ordinary_scalar_absorption hh.1 hh.2.1
  unfold uniformXiCountBound uniformXiFee
  rw [abs_of_pos (lowHeight_pos.trans_le hy)]
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_gt_three]

theorem ordinary_count_character {q : ℕ} [NeZero q] (chi : Character q)
    {alpha y : ℝ} (ha : 0 ≤ alpha) (hy : lowHeight ≤ y) :
    (count chi alpha y : ℝ) ≤ (y / 3) * Real.log ((q : ℝ) * y) := by
  by_cases hc : chi = 1
  · subst chi
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    have hqlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg
      (by exact_mod_cast (NeZero.one_le : 1 ≤ q))
    have h := (principal_count_alpha_le_uniform q ha (lowHeight_pos.trans_le hy).le).trans
      (ordinary_uniform_principal hy)
    rw [Real.log_mul hq0.ne' (lowHeight_pos.trans_le hy).ne']
    have hp : 0 ≤ y * Real.log (q : ℝ) := mul_nonneg (lowHeight_pos.trans_le hy).le hqlog
    nlinarith
  · apply (count_nonprincipal_uniform_modulus hc ha (lowHeight_pos.trans_le hy).le).trans
    apply ordinary_uniform_nonprincipal (NeZero.pos q) (parityShift_pos chi) ?_ hy
    unfold parityShift
    split_ifs <;> norm_num

theorem ordinary_count_family (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : lowHeight ≤ y) :
    (familyCount q alpha y : ℝ) ≤ q.totient * (y / 3) * Real.log ((q : ℝ) * y) := by
  have hc : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => ordinary_count_character chi ha hy)
  simpa only [familyCount, Nat.cast_sum, Finset.sum_const, Finset.card_univ, hc,
    nsmul_eq_mul, mul_assoc] using h

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
