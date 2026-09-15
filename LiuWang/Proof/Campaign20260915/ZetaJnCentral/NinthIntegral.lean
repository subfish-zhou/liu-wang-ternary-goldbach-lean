import LiuWang.Proof.Campaign20260915.ZetaJnCentral.NinthRadius

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem exp_neg_le_fourth {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 24 / x ^ 4 := by
  have h := Real.pow_div_factorial_le_exp x hx.le 4
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at h
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (pow_pos hx 4)]
  linarith

def ninthOuterConstant (sigma : ℝ) : ℝ :=
  1008 * (29 / Real.pi) ^ 5 * Real.exp (|sigma - 1| * Real.log (5 / 2)) * rsSaddleScale ^ 6

def ninthJnConstant (sigma : ℝ) : ℝ :=
  21 * Real.exp (|sigma - 1| * Real.log (5 / 2) + 5 / 6) *
    rsSaddleScale ^ 6 * gaussianMomentBudget 8 + ninthOuterConstant sigma

theorem ninth_outer_integrals (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (he : 2 ≤ eta) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (ninthCutoff eta)..(eta / 2), rsJnIntegrand sigma eta m 9 y‖ +
      ‖∫ y : ℝ in (-eta / 2)..(-ninthCutoff eta), rsJnIntegrand sigma eta m 9 y‖ ≤
        ninthOuterConstant sigma / eta ^ 3 := by
  have he0 : 0 < eta := by linarith
  have hp := ninthRadius_data he
  have hd : 0 < ninthCutoff eta := by linarith [hp.2.2.1]
  have hden := exterior_denominator_half hp.2.2.1
  have hden0 := exterior_denominator_pos hd
  have hC : rsJnOuterConstant sigma (ninthCutoff eta) 9 ≤
      42 * Real.exp (|sigma - 1| * Real.log (5 / 2)) * (20 / 21 : ℝ) ^ 9 := by
    unfold rsJnOuterConstant
    rw [div_le_iff₀ hden0]
    have h := mul_le_mul_of_nonneg_left hden
      (by positivity : 0 ≤ 42 * Real.exp (|sigma - 1| * Real.log (5 / 2)) * (20 / 21 : ℝ) ^ 9)
    nlinarith
  have htail : Real.exp (-Real.pi / 29 * ninthCutoff eta ^ 2) ≤
      24 / ((Real.pi / 29) * ninthCutoff eta ^ 2) ^ 4 := by
    simpa only [neg_mul, neg_div] using exp_neg_le_fourth
      (by positivity : 0 < (Real.pi / 29) * ninthCutoff eta ^ 2)
  have ho := (jn_middle_integrals sigma he0 hd hp.2.2.2.1 le_rfl hm0 hm1 9).2.2
  simp only [neg_div] at ho ⊢
  apply ho.trans
  calc
    _ ≤ (42 * Real.exp (|sigma - 1| * Real.log (5 / 2)) * (20 / 21 : ℝ) ^ 9) *
        (29 / (Real.pi * ninthCutoff eta)) *
          (24 / ((Real.pi / 29) * ninthCutoff eta ^ 2) ^ 4) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hC (by positivity)) ?_
        (Real.exp_pos _).le (by positivity)
      simpa only [neg_div] using htail
    _ = 1008 * (29 / Real.pi) ^ 5 * Real.exp (|sigma - 1| * Real.log (5 / 2)) *
        (20 / 21 : ℝ) ^ 9 / ninthCutoff eta ^ 9 := by
      field_simp
      ring
    _ = _ := by
      rw [ninthCutoff_ninth he0]
      unfold ninthOuterConstant
      have hs := rsSaddleScale_pos.ne'
      field_simp

theorem jn_nine_source_order (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (he : 2 ≤ eta) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta m 9 y‖ ≤
      ninthJnConstant sigma / eta ^ 3 := by
  have he0 : 0 < eta := by linarith
  have hp := ninthRadius_data he
  have hd : 0 < ninthCutoff eta := by linarith [hp.2.2.1]
  have hc := jn_central_gaussian_integral sigma he0 hp.1 hp.2.1 hd.le hp.2.2.2.2.le hm0 hm1 8
  norm_num only [Nat.reduceAdd] at hc
  rw [ninthCentralConstant sigma he0] at hc
  have ho := ninth_outer_integrals sigma he hm0 hm1
  rw [show 9 = 8 + 1 by rfl,
    jn_local_split sigma he0 hd.le hp.2.2.2.1 hm0 hm1 8, norm_neg]
  apply norm_add₃_le.trans
  have hsum := add_le_add hc ho
  unfold ninthJnConstant
  simp only [neg_div, Nat.reduceAdd] at hsum ⊢
  linear_combination hsum

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
