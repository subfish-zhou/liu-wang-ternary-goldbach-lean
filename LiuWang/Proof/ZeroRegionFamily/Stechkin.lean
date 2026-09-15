import LiuWang.Proof.ZeroRegionFamily.ComplexKernel

/-! # 真实Stechkin差分的Euler正性与保全部有号零点核的恒等式 -/

set_option autoImplicit false
noncomputable section

open Complex
open ArithmeticFunction hiding log
open BombieriVinogradov.SiegelWalfisz
open scoped LSeries.notation

namespace LiuWang.Proof.ZeroRegionFamily

def stechkinSigma (sigma : ℝ) : ℝ := (1+Real.sqrt (1+4*sigma^2))/2

def stechkinK : ℝ := 1/Real.sqrt 5

theorem stechkinSigma_ge {sigma : ℝ} (hs : 1 < sigma) : sigma ≤ stechkinSigma sigma := by
  have hsqrt := Real.sq_sqrt (show 0 ≤ 1+4*sigma^2 by positivity)
  have hp := Real.sqrt_nonneg (1+4*sigma^2)
  dsimp [stechkinSigma]
  nlinarith

theorem stechkinK_mem : stechkinK ∈ Set.Icc (0 : ℝ) 1 := by
  have hp : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  constructor
  · exact le_of_lt (one_div_pos.2 hp)
  · dsimp [stechkinK]
    rw [div_le_one hp]
    nlinarith

theorem eulerWeight_antitone {q : ℕ} (chi : DirichletCharacter ℂ q)
    {sigma sigma1 : ℝ} (hs : sigma ≤ sigma1) (t : ℝ) (n : ℕ) :
    zeroFreeEulerWeight chi sigma1 t n ≤ zeroFreeEulerWeight chi sigma t n := by
  classical
  by_cases hn : n=0
  · simp [zeroFreeEulerWeight, hn]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have hf : (n : ℝ)^(sigma-sigma1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have he : zeroFreeEulerWeight chi sigma1 t n =
      (n : ℝ)^(sigma-sigma1)*zeroFreeEulerWeight chi sigma t n := by
    unfold zeroFreeEulerWeight
    split_ifs with hunit
    · simp only [hn] at *
      have hh : (n : ℝ)^(sigma-sigma1)*(n : ℝ)^(-sigma) = (n : ℝ)^(-sigma1) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
      calc
        _ = Λ n * ((n : ℝ)^(sigma-sigma1)*(n : ℝ)^(-sigma)) *
            (3+4*(chi n*(n : ℂ)^(-(Complex.I*t)))+
              (chi n*(n : ℂ)^(-(Complex.I*t)))^2).re := by rw [hh]
        _ = _ := by ring
    · simp
  rw [he]
  simpa using mul_le_mul_of_nonneg_right hf (zeroFreeEulerWeight_nonneg chi sigma t n)

theorem eulerWeight_hasSum {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    HasSum (zeroFreeEulerWeight chi sigma t)
      (3*(-logDeriv (1 : DirichletCharacter ℂ q).LFunction sigma).re+
       4*(-logDeriv chi.LFunction ((sigma : ℂ)+Complex.I*t)).re+
       (-logDeriv (chi^2).LFunction ((sigma : ℂ)+2*Complex.I*t)).re) := by
  have h0 : 1 < (sigma : ℂ).re := hs
  have h1 : 1 < ((sigma : ℂ)+Complex.I*t).re := by simpa [Complex.mul_re] using hs
  have h2 : 1 < ((sigma : ℂ)+2*Complex.I*t).re := by simpa [Complex.mul_re] using hs
  have hsum := (((hasSum_re
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
      (1 : DirichletCharacter ℂ q) h0).LSeriesHasSum).mul_left 3).add
    ((hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
      chi h1).LSeriesHasSum).mul_left 4)).add
    (hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
      (chi^2) h2).LSeriesHasSum)
  simp only [logDeriv, Pi.div_apply, ← neg_div]
  rw [neg_logDeriv_LFunction_eq_twist_vonMangoldt _ h0,
    neg_logDeriv_LFunction_eq_twist_vonMangoldt _ h1,
    neg_logDeriv_LFunction_eq_twist_vonMangoldt _ h2]
  simpa only [logDerivativeEulerTerms_eq_weight] using hsum

def dampedLogDeriv {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (sigma sigma1 k t : ℝ) : ℝ :=
  -(logDeriv chi.LFunction ((sigma : ℂ)+Complex.I*t)).re+
    k*(logDeriv chi.LFunction ((sigma1 : ℂ)+Complex.I*t)).re

theorem damped_combination_nonneg {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma sigma1 k : ℝ}
    (hs : 1 < sigma) (hss : sigma ≤ sigma1) (hk : k ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    0 ≤ 3*dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma sigma1 k 0+
      4*dampedLogDeriv chi sigma sigma1 k t+
      dampedLogDeriv (chi^2) sigma sigma1 k (2*t) := by
  have hsum := (eulerWeight_hasSum chi hs t).sub
    ((eulerWeight_hasSum chi (hs.trans_le hss) t).mul_left k)
  have hnon : 0 ≤ ∑' n, (zeroFreeEulerWeight chi sigma t n-
      k*zeroFreeEulerWeight chi sigma1 t n) := by
    apply tsum_nonneg
    intro n
    have hw := eulerWeight_antitone chi hss t n
    have hk1 := mul_le_mul_of_nonneg_right hk.2 (zeroFreeEulerWeight_nonneg chi sigma1 t n)
    linarith
  rw [hsum.tsum_eq] at hnon
  simp only [dampedLogDeriv, Complex.ofReal_zero, mul_zero, add_zero,
    Complex.neg_re, Complex.ofReal_mul] at *
  push_cast
  convert hnon using 1
  ring

theorem stechkin_combination_nonneg {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    0 ≤ 3*dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma (stechkinSigma sigma) stechkinK 0+
      4*dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t+
      dampedLogDeriv (chi^2) sigma (stechkinSigma sigma) stechkinK (2*t) :=
  damped_combination_nonneg chi hs (stechkinSigma_ge hs) stechkinK_mem t

theorem damped_kernel_identity {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {sigma sigma1 : ℝ} (hs : 1 < sigma) (hs1 : 1 < sigma1) (k t : ℝ) :
    dampedLogDeriv chi sigma sigma1 k t+
      (∑' p : SymmetricCompletedZeroIndex chi,
        ((1/((sigma : ℂ)+Complex.I*t-Complex.Hadamard.divisorZeroIndex₀_val p)).re-
        k*(1/((sigma1 : ℂ)+Complex.I*t-Complex.Hadamard.divisorZeroIndex₀_val p)).re)) =
      (1-k)*Real.log q/2+
      (logDeriv chi.gammaFactor ((sigma : ℂ)+Complex.I*t)).re-
      k*(logDeriv chi.gammaFactor ((sigma1 : ℂ)+Complex.I*t)).re := by
  have h0 : 1 < ((sigma : ℂ)+Complex.I*t).re := by simpa [Complex.mul_re] using hs
  have h1 : 1 < ((sigma1 : ℂ)+Complex.I*t).re := by simpa [Complex.mul_re] using hs1
  have hsum0 := summable_symmetricCompletedLFunction_zeroKernel_re hc hp h0
  have hsum1 := summable_symmetricCompletedLFunction_zeroKernel_re hc hp h1
  rw [hsum0.tsum_sub (hsum1.mul_left k), tsum_mul_left]
  have hi0 := primitive_kernel_identity hc hp h0
  have hi1 := primitive_kernel_identity hc hp h1
  dsimp [dampedLogDeriv]
  linear_combination hi0-k*hi1

end LiuWang.Proof.ZeroRegionFamily
