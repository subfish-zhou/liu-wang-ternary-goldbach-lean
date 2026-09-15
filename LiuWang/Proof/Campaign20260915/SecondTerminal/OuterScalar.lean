import LiuWang.Proof.Campaign20260915.SecondTerminal.LowArc

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

theorem original_nu_sqrt_scaling {L : ℝ} (hL : 3100 ≤ L) :
    sourceNu (L ^ (3 : ℕ)) ≤ scaling L * sourceNu ((3100 : ℝ) ^ (3 : ℕ)) := by
  let t := scaling L
  let b := Real.log (Real.log ((3100 : ℝ) ^ (3 : ℕ)))
  let c := Real.log (Real.log (L ^ (3 : ℕ)))
  have ht : 1 ≤ t := (scaling_bounds hL).1
  have ht0 : 0 < t := by linarith
  have hbase : L = 3100 * t ^ (2 : ℕ) := (scaling_bounds hL).2
  have hb : 3 ≤ b := (source_loglog_bounds (L := (3100 : ℝ)) le_rfl).1
  have hlog : 6 ≤ Real.log ((3100 : ℝ) ^ (3 : ℕ)) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_3100_bounds.1]
  have hbc : b ≤ c := by
    apply Real.log_le_log (by linarith)
    exact Real.log_le_log (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 3)
  have he : Real.log (L ^ (3 : ℕ)) =
      Real.log ((3100 : ℝ) ^ (3 : ℕ)) + 6 * Real.log t := by
    rw [hbase]
    simp only [Real.log_pow, Real.log_mul (by norm_num : (3100 : ℝ) ≠ 0)
      (pow_ne_zero 2 ht0.ne'), Nat.cast_ofNat]
    ring
  have hlogs : Real.log (L ^ (3 : ℕ)) ≤ t * Real.log ((3100 : ℝ) ^ (3 : ℕ)) := by
    rw [he]
    nlinarith [Real.log_le_sub_one_of_pos ht0,
      mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hlog)]
  have hc : c ≤ b + Real.log t := by
    have hp : 0 < Real.log (L ^ (3 : ℕ)) := by
      rw [he]
      nlinarith [Real.log_nonneg ht]
    have hh := Real.log_le_log hp hlogs
    rw [Real.log_mul ht0.ne' (by linarith : Real.log ((3100 : ℝ) ^ (3 : ℕ)) ≠ 0)] at hh
    exact hh.trans_eq (add_comm _ _)
  have hct : c ≤ t * b := by
    nlinarith [Real.log_le_sub_one_of_pos ht0,
      mul_nonneg (sub_nonneg.mpr ht) (by linarith : 0 ≤ b - 1)]
  have hn := FixedIntegral.sourceNu_upper_of_intervals
    (le_refl (Real.exp Real.eulerMascheroniConstant)) (by linarith : 0 < b) hbc hct
  have hd : (2.50637 : ℝ) / b ≤ t * (2.50637 / b) :=
    le_mul_of_one_le_left (by positivity) ht
  change sourceNu (L ^ (3 : ℕ)) ≤
    t * (Real.exp Real.eulerMascheroniConstant * b + 2.50637 / b)
  nlinarith only [hn, hd]

theorem original_nu_sqrt_bound {L : ℝ} (hL : 3100 ≤ L) :
    sourceNu (L ^ (3 : ℕ)) ≤ 0.11598 * Real.sqrt L := by
  have ht := (scaling_bounds hL).1
  have hb : sourceNu ((3100 : ℝ) ^ (3 : ℕ)) ≤ 6.457 :=
    Fixed032281.sourceNu_fixed_upper.trans (by norm_num)
  have hs : (55.677 : ℝ) ≤ Real.sqrt 3100 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.sqrt L = Real.sqrt 3100 * scaling L := by
    unfold scaling
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3100)]
    congr 1
    ring
  calc
    _ ≤ scaling L * 6.457 :=
      (original_nu_sqrt_scaling hL).trans (mul_le_mul_of_nonneg_left hb (by linarith))
    _ ≤ scaling L * (0.11598 * Real.sqrt 3100) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hs]) (by linarith)
    _ = _ := by rw [he]; ring

theorem original_sqrt_cube {L : ℝ} (hL : 0 ≤ L) :
    Real.sqrt (L ^ (3 : ℕ)) = L * Real.sqrt L := by
  rw [show L ^ (3 : ℕ) = L ^ (2 : ℕ) * L by ring, Real.sqrt_mul (sq_nonneg L),
    Real.sqrt_sq hL]

def originalOuterScalar (L : ℝ) : ℝ :=
  (10 / (3.36 * L ^ (2 : ℕ))) * sourceNu (L ^ (3 : ℕ)) +
    4.3368 / L ^ (5 : ℕ) +
    max (0.0194 * Real.sqrt 2)
      ((10 / (3.36 * Real.sqrt L)) * sourceNu (L ^ (3 : ℕ)) + 8.2e-10 * Real.sqrt 2) +
    (5 * 0.0126 * sourceNu (L ^ (3 : ℕ))) / (L * Real.sqrt L)

theorem original_outer_scalar {L : ℝ} (hL : 3100 ≤ L) :
    originalOuterScalar L ≤ 0.3452 := by
  have hL0 : 0 < L := by linarith
  have hs0 := Real.sqrt_pos.mpr hL0
  have hs : (55 : ℝ) ≤ Real.sqrt L :=
    (Real.le_sqrt (by norm_num) hL0.le).mpr (by linarith)
  have h2 : Real.sqrt (2 : ℝ) ≤ 1.415 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn := original_nu_sqrt_bound hL
  have hg : (3100 : ℝ) * 55 ≤ L * Real.sqrt L := mul_le_mul hL hs (by norm_num) hL0.le
  have hp : (10 / (3.36 * L ^ (2 : ℕ))) * sourceNu (L ^ (3 : ℕ)) ≤ 0.0000021 := by
    calc
      _ ≤ (10 / (3.36 * L ^ (2 : ℕ))) * (0.11598 * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = (10 * 0.11598 / 3.36) / (L * Real.sqrt L) := by
        field_simp
        rw [Real.sq_sqrt hL0.le]
      _ ≤ (10 * 0.11598 / 3.36) / (3100 * 55) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hg
      _ ≤ _ := by norm_num
  have he : (4.3368 : ℝ) / L ^ (5 : ℕ) ≤ 0.0000001 := by
    apply (div_le_iff₀ (pow_pos hL0 5)).mpr
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 5
    norm_num at hh
    linarith
  have hh : (5 * 0.0126 * sourceNu (L ^ (3 : ℕ))) / (L * Real.sqrt L) ≤ 0.0000024 := by
    calc
      _ ≤ (5 * 0.0126 * (0.11598 * Real.sqrt L)) / (L * Real.sqrt L) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) (by positivity)
      _ = (5 * 0.0126 * 0.11598) / L := by field_simp
      _ ≤ (5 * 0.0126 * 0.11598) / 3100 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
      _ ≤ _ := by norm_num
  have hl : max (0.0194 * Real.sqrt 2)
      ((10 / (3.36 * Real.sqrt L)) * sourceNu (L ^ (3 : ℕ)) + 8.2e-10 * Real.sqrt 2) ≤
        0.34519 := by
    apply max_le
    · nlinarith only [h2]
    · have hb := add_le_add
        (mul_le_mul_of_nonneg_left hn (show 0 ≤ 10 / (3.36 * Real.sqrt L) by positivity))
        (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 8.2e-10))
      have hc : (10 / (3.36 * Real.sqrt L)) * (0.11598 * Real.sqrt L) =
          10 * 0.11598 / 3.36 := by field_simp
      rw [hc] at hb
      linarith only [hb]
  unfold originalOuterScalar
  linarith only [hp, he, hh, hl]

theorem original_outer_payment {L X : ℝ} (hL : 3100 ≤ L) (hX : 0 ≤ X) :
    (10 * X / (3.36 * L ^ (3 : ℕ))) * sourceNu (L ^ (3 : ℕ)) +
      4.3368 * X / L ^ (6 : ℕ) +
      max (0.0194 * Real.sqrt 2 * X / L)
        ((10 * X / (3.36 * Real.sqrt (L ^ (3 : ℕ)))) * sourceNu (L ^ (3 : ℕ)) +
          8.2e-10 * Real.sqrt 2 * X / L) +
      (5 * 0.0126 * sourceNu (L ^ (3 : ℕ))) * X /
        (L ^ (2 : ℕ) * Real.sqrt L) ≤ 0.3452 * X / L := by
  have hL0 : 0 < L := by linarith
  have hs0 := Real.sqrt_pos.mpr hL0
  have hx : 0 ≤ X / L := div_nonneg hX hL0.le
  have he1 : 0.0194 * Real.sqrt 2 * X / L = (0.0194 * Real.sqrt 2) * (X / L) := by ring
  have he2 :
      (10 * X / (3.36 * Real.sqrt (L ^ (3 : ℕ)))) * sourceNu (L ^ (3 : ℕ)) +
        8.2e-10 * Real.sqrt 2 * X / L =
      ((10 / (3.36 * Real.sqrt L)) * sourceNu (L ^ (3 : ℕ)) +
        8.2e-10 * Real.sqrt 2) * (X / L) := by
    rw [original_sqrt_cube hL0.le]
    field_simp
  rw [he1, he2, ← max_mul_of_nonneg _ _ hx]
  have hp := mul_le_mul_of_nonneg_right (original_outer_scalar hL) hx
  unfold originalOuterScalar at hp
  convert hp using 1 <;> first | rfl | field_simp

#print axioms original_outer_payment

end LiuWang.Proof.Campaign20260915.SecondTerminal
