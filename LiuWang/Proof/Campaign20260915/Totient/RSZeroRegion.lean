import LiuWang.Proof.Campaign20260915.Totient.RSPolynomial
import LiuWang.Proof.ChebyshevBound.HighHeight.HeightNumerics

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.Totient

def rsR : ℝ := 515 / (Real.sqrt 546 - Real.sqrt 322) ^ 2

def rsA : ℝ := Real.exp (999 / 100)

theorem rsR_pos : 0 < rsR := by
  have hd : 0 < Real.sqrt 546 - Real.sqrt 322 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 322)
      (by norm_num : (322 : ℝ) < 546)
    linarith
  exact div_pos (by norm_num) (sq_pos_of_pos hd)

theorem rsA_ge_thousand : 1000 ≤ rsA := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 54) exp_four_ge_fifty_four 2
  have he : Real.exp 4 ^ 2 = Real.exp 8 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he] at h
  have hm : Real.exp 8 ≤ rsA := Real.exp_le_exp.mpr (by norm_num)
  linarith

theorem rs_zero_gap (p : RiemannXiDivisorZeroIndex)
    (ht : rsA ≤ |(riemannXiDivisorZeroValue p).im|) :
    1 / (rsR * Real.log |(riemannXiDivisorZeroValue p).im|) <
      1 - (riemannXiDivisorZeroValue p).re := by
  let L := Real.log |(riemannXiDivisorZeroValue p).im|
  let a := Real.sqrt (322 : ℝ)
  let b := Real.sqrt (546 : ℝ)
  let d := b - a
  have ha2 : a ^ 2 = 322 := Real.sq_sqrt (by norm_num)
  have hb2 : b ^ 2 = 546 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by norm_num)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by norm_num)
  have hd0 : 0 < d := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 322)
      (by norm_num : (322 : ℝ) < 546)
    dsimp [d, a, b]
    linarith
  have ha18 : a ≤ 18 := by nlinarith
  have hb24 : b ≤ 24 := by nlinarith
  have ha17 : 17 ≤ a := by nlinarith
  have had : a * d ≤ 120 := by
    dsimp [d]
    have h := mul_le_mul_of_nonneg_left hb24 ha0.le
    nlinarith
  have hL : 999 / 100 ≤ L := by
    apply (Real.le_log_iff_exp_le (by linarith [rsA_ge_thousand.trans ht])).mpr
    exact ht
  have hL0 : 0 < L := by linarith
  let δ := a * d / (515 * L)
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδhi : δ ≤ 1 / 40 := by
    apply (div_le_iff₀ (by positivity : 0 < 515 * L)).mpr
    nlinarith
  have hcore := rs_zero_core p (rsA_ge_thousand.trans ht)
    (σ := 1 + δ) (by linarith) (by linarith)
  have hid : 1 / (rsR * L) = d ^ 2 / (515 * L) := by
    dsimp [rsR, d, a, b]
    field_simp
  have heq : 546 / (δ + d ^ 2 / (515 * L)) = 322 / δ + 515 * L := by
    dsimp [δ]
    have had0 : a * d ≠ 0 := mul_ne_zero ha0.ne' hd0.ne'
    have hsum : a * d + d ^ 2 = b * d := by dsimp [d]; ring
    field_simp [hL0.ne', ha0.ne', hd0.ne', hsum, hb0.ne']
    nlinarith [ha2, hb2]
  have hden : 0 < 1 + δ - (riemannXiDivisorZeroValue p).re := by
    have h := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
    linarith
  by_contra! hg
  change 1 - (riemannXiDivisorZeroValue p).re ≤ 1 / (rsR * L) at hg
  rw [hid] at hg
  have hle : 546 / (δ + d ^ 2 / (515 * L)) ≤
      546 / (1 + δ - (riemannXiDivisorZeroValue p).re) :=
    div_le_div_of_nonneg_left (by norm_num) hden (by linarith)
  rw [heq] at hle
  change 546 / (1 + δ - (riemannXiDivisorZeroValue p).re) <
    322 / (1 + δ - 1) + 515 * L at hcore
  rw [show 1 + δ - 1 = δ by ring] at hcore
  linarith

#print axioms rs_zero_gap

end LiuWang.Proof.Campaign20260915.Totient
