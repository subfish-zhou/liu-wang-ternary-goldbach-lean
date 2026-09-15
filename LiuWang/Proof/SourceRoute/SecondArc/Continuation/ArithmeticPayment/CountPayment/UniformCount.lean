import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.ActualInner

set_option autoImplicit false
noncomputable section
open Complex
open scoped BigOperators
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.DirichletZeroCount.Remainder

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment

def countEnvelope (q : ℕ) (y : ℝ) : ℝ :=
  (y / 3 + 4) * Real.log ((q : ℝ) * y) + 30

theorem norm_gamma_le_twice {a y : ℝ} (ha : 0 ≤ a) (ha4 : a ≤ 4) (hy : 3.36 ≤ y) :
    ‖(a : ℂ) + (y : ℂ) * I‖ ≤ 2 * y := by
  apply (sq_le_sq₀ (norm_nonneg _) (by linarith : 0 ≤ 2 * y)).mp
  rw [← normSq_eq_norm_sq, normSq_apply]
  norm_num
  nlinarith [sq_nonneg (y - 3.36)]

theorem log_height_shift {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : 3.36 ≤ y) :
    0 ≤ Real.log ((q : ℝ) * y) ∧
      Real.log q + Real.log (y + 2) ≤ Real.log ((q : ℝ) * y) + 1 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by positivity
  have hy0 : 0 < y := by linarith
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < (y + 2) / y)
  rw [Real.log_div (by positivity) hy0.ne'] at hlog
  have hd : (y + 2) / y ≤ 2 := (div_le_iff₀ hy0).mpr (by linarith)
  rw [Real.log_mul hq0.ne' hy0.ne']
  exact ⟨add_nonneg (Real.log_nonneg hq1) (Real.log_nonneg (by linarith)), by linarith⟩

theorem horizontal_fee_envelope {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : 3.36 ≤ y) :
    2 * uniformHorizontalFee q y ≤ Real.pi * (4 * Real.log ((q : ℝ) * y) + 25) := by
  have hl := log_height_shift hq hy
  have hm := mul_le_mul_of_nonneg_left hl.2
    (by positivity : 0 ≤ 5 * Real.pi / 2 + 4)
  have hz := mul_nonneg (by linarith [Real.pi_gt_three] : 0 ≤ 3 * Real.pi / 2 - 4) hl.1
  unfold uniformHorizontalFee
  rw [abs_of_pos (by linarith : 0 < y)]
  nlinarith [Real.pi_gt_three]

theorem xi_fee_envelope {y : ℝ} (hy : 3.36 ≤ y) :
    2 * uniformXiFee y ≤ Real.pi * (4 * Real.log y + 25) := by
  have hl := log_height_shift (q := 1) (by norm_num) hy
  norm_num at hl
  have hm := mul_le_mul_of_nonneg_left hl.2
    (by positivity : 0 ≤ 5 * Real.pi / 2 + 4)
  have hz := mul_nonneg (by linarith [Real.pi_gt_three] : 0 ≤ 3 * Real.pi / 2 - 4) hl.1
  unfold uniformXiFee
  rw [abs_of_pos (by linarith : 0 < y)]
  nlinarith [Real.pi_gt_three]

theorem nonprincipal_uniform_envelope {q : ℕ} (hq : 0 < q) (chi : Character q)
    {y : ℝ} (hy : 3.36 ≤ y) :
    uniformCountBound q (parityShift chi) y ≤ countEnvelope q y := by
  have hy0 : 0 < y := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hn0 : 0 < ‖(3 / 2 : ℂ) + (y : ℂ) * I‖ :=
    lt_of_lt_of_le (by norm_num) (re_le_norm _)
  have hn := norm_gamma_le_twice (a := 3 / 2) (by norm_num) (by norm_num) hy
  push_cast at hn
  have hlog : Real.log ((q : ℝ) * ‖(3 / 2 : ℂ) + (y : ℂ) * I‖ / (2 * Real.pi)) ≤
      Real.log ((q : ℝ) * y) := by
    apply Real.log_le_log (by positivity)
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    have hm := mul_le_mul_of_nonneg_left hn hq0.le
    nlinarith [mul_nonneg (mul_nonneg hq0.le hy0.le)
      (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi - 1)]
  have hmain : sixMain q y ≤ y * Real.log ((q : ℝ) * y) + Real.pi / 4 := by
    unfold sixMain
    nlinarith [mul_le_mul_of_nonneg_left hlog hy0.le,
      Real.arctan_lt_pi_div_two (2 * y / 3)]
  have hh := uniformCountBound_le_sixMain hq chi hy0.le
  have hf := horizontal_fee_envelope hq hy
  have hl := (log_height_shift hq hy).1
  have hb : y * Real.log ((q : ℝ) * y) ≤
      Real.pi * (y / 3 * Real.log ((q : ℝ) * y)) := by
    nlinarith [mul_nonneg (mul_nonneg hy0.le hl)
      (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi - 3)]
  apply hh.trans
  apply (div_le_iff₀ Real.pi_pos).mpr
  unfold countEnvelope
  nlinarith [Real.pi_pos]

theorem principal_uniform_envelope {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : 3.36 ≤ y) :
    uniformXiCountBound y ≤ countEnvelope q y := by
  have hy0 : 0 < y := by linarith
  have hn0 : 0 < ‖((4 : ℝ) : ℂ) + (y : ℂ) * I‖ :=
    lt_of_lt_of_le (by norm_num) (re_le_norm _)
  have hn := norm_gamma_le_twice (a := 4) (by norm_num) (by norm_num) hy
  have hlog : Real.log (‖((4 : ℝ) : ℂ) + (y : ℂ) * I‖ / 2) ≤ Real.log y :=
    Real.log_le_log (by positivity) (by linarith)
  have hgamma : sourceGammaMain 4 y ≤ y * Real.log y + 3 * Real.pi / 2 := by
    unfold sourceGammaMain
    nlinarith [mul_le_mul_of_nonneg_left hlog hy0.le, Real.arctan_lt_pi_div_two (y / 4)]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq := Real.log_le_log hy0 (le_mul_of_one_le_left hy0.le hq1)
  have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hpi := Real.log_nonneg (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)
  have hb : y * Real.log y ≤ Real.pi * (y / 3 * Real.log y) := by
    nlinarith [mul_nonneg (mul_nonneg hy0.le hl)
      (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi - 3)]
  have hf := xi_fee_envelope hy
  have hcoef : (y / 3 + 4) * Real.log y ≤ (y / 3 + 4) * Real.log ((q : ℝ) * y) :=
    mul_le_mul_of_nonneg_left hlq (by positivity)
  unfold uniformXiCountBound countEnvelope
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith [mul_nonneg hy0.le hpi, mul_le_mul_of_nonneg_left hcoef Real.pi_pos.le,
    Real.pi_pos]

theorem familyCount_le_envelope (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 3.36 ≤ y) :
    (familyCount q alpha y : ℝ) ≤ (q.totient : ℝ) * countEnvelope q y := by
  have hq := NeZero.pos q
  have hc (chi : Character q) : (count chi alpha y : ℝ) ≤ countEnvelope q y := by
    by_cases hchi : chi = 1
    · subst chi
      exact (principal_count_alpha_le_uniform q ha (by linarith)).trans
        (principal_uniform_envelope hq hy)
    · exact (count_nonprincipal_uniform_modulus hchi ha (by linarith)).trans
        (nonprincipal_uniform_envelope hq chi hy)
  have hcard : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  calc
    _ ≤ ∑ _chi : Character q, countEnvelope q y := by
      simpa only [familyCount, Nat.cast_sum] using
        Finset.sum_le_sum (fun chi (_ : chi ∈ (Finset.univ : Finset (Character q))) => hc chi)
    _ = _ := by simp [hcard]

theorem actual_inner_le_envelope {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : 3.36 ≤ y) :
    (∫ alpha in (59 / 60 : ℝ)..stripLower q y,
      alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      (q.totient : ℝ) * countEnvelope q y *
        Real.exp (-0.478 * Real.log (0.001 * (N : ℝ)) / Real.log ((q : ℝ) * y)) := by
  have hc := familyCount_le_envelope q (alpha := 0) le_rfl hy
  exact actual_inner_le_count_bound hN ((Nat.cast_nonneg _).trans hc)
    (fun alpha ha => familyCount_le_envelope q (by linarith) hy)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
