import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Euler

set_option autoImplicit false
noncomputable section

open Complex
open ArithmeticFunction hiding log
open scoped LSeries.notation
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.ZeroRegionFamily.RealClosure

namespace LiuWang.Proof.SourceRoute.Exception.Restart

def realTerm {q : ℕ} (chi : DirichletCharacter ℂ q) (sigma : ℝ) (n : ℕ) : ℝ :=
  (LSeries.term (↗chi * ↗Λ) (sigma : ℂ) n).re

theorem realTerm_eq {q : ℕ} (chi : DirichletCharacter ℂ q)
    (sigma : ℝ) {n : ℕ} (hn : n ≠ 0) :
    realTerm chi sigma n = (Λ n / (n : ℝ) ^ sigma) * (chi n).re := by
  have he : ((Λ n / (n : ℝ) ^ sigma : ℝ) : ℂ) =
      (Λ n : ℂ) / (n : ℂ) ^ (sigma : ℂ) := by
    rw [ofReal_div, ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast]
  unfold realTerm
  rw [LSeries.term_of_ne_zero hn, Pi.mul_apply]
  rw [show chi n * (Λ n : ℂ) / (n : ℂ) ^ (sigma : ℂ) =
    (Λ n : ℂ) / (n : ℂ) ^ (sigma : ℂ) * chi n by ring, ← he]
  simp

theorem realTerm_hasSum {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) :
    HasSum (realTerm chi sigma) (-(logDeriv chi.LFunction (sigma : ℂ)).re) := by
  have he : harmonicTerm chi sigma 0 1 = realTerm chi sigma := by
    funext n
    simp [harmonicTerm, realTerm]
  have h := harmonicTerm_hasSum chi hs 0 1
  rw [he] at h
  simpa using h

def fourWeight {q r : ℕ} (chi : DirichletCharacter ℂ q)
    (psi : DirichletCharacter ℂ r) (sigma : ℝ) (n : ℕ) : ℝ :=
  realTerm (1 : DirichletCharacter ℂ 1) sigma n + realTerm chi sigma n +
    realTerm psi sigma n + realTerm (pairCharacter chi psi) sigma n

theorem fourWeight_eq {q r : ℕ} (chi : DirichletCharacter ℂ q)
    (psi : DirichletCharacter ℂ r) (sigma : ℝ) {n : ℕ} (hn : n ≠ 0) :
    fourWeight chi psi sigma n = (Λ n / (n : ℝ) ^ sigma) *
      (1 + chi n + psi n + pairCharacter chi psi n : ℂ).re := by
  have h1 : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _]
    simp
  simp only [fourWeight, realTerm_eq _ _ hn, h1, Complex.one_re, Complex.add_re]
  ring

theorem fourWeight_nonneg {q r : ℕ} (chi : DirichletCharacter ℂ q)
    (psi : DirichletCharacter ℂ r) (hc : chi ^ 2 = 1) (hp : psi ^ 2 = 1)
    (sigma : ℝ) (n : ℕ) : 0 ≤ fourWeight chi psi sigma n :=
  fourFactor_logDerivativeTerm_nonneg chi psi hc hp sigma n

theorem fourWeight_antitone {q r : ℕ} (chi : DirichletCharacter ℂ q)
    (psi : DirichletCharacter ℂ r) (hc : chi ^ 2 = 1) (hp : psi ^ 2 = 1)
    {sigma tau : ℝ} (hst : sigma ≤ tau) (n : ℕ) :
    fourWeight chi psi tau n ≤ fourWeight chi psi sigma n := by
  by_cases hn : n = 0
  · simp [fourWeight, realTerm, hn]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hpow := Real.rpow_le_rpow_of_exponent_le hn1 hst
  have hweight := div_le_div_of_nonneg_left (vonMangoldt_nonneg (n := n))
    (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) sigma) hpow
  have hcoeff : 0 ≤ (1 + chi n + psi n + pairCharacter chi psi n : ℂ).re :=
    (RCLike.le_iff_re_im.mp (fourFactorEulerCoefficient_nonneg chi psi hc hp n)).1
  rw [fourWeight_eq chi psi tau hn, fourWeight_eq chi psi sigma hn]
  exact mul_le_mul_of_nonneg_right hweight hcoeff

theorem four_factor_stechkin_nonneg {q r : ℕ} [NeZero q] [NeZero r] [NeZero (q * r)]
    (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    (hc : chi ^ 2 = 1) (hp : psi ^ 2 = 1) {sigma : ℝ} (hs : 1 < sigma) :
    0 ≤ dampedLogDeriv (1 : DirichletCharacter ℂ 1) sigma (stechkinSigma sigma) stechkinK 0 +
      dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK 0 +
      dampedLogDeriv psi sigma (stechkinSigma sigma) stechkinK 0 +
      dampedLogDeriv (pairCharacter chi psi) sigma (stechkinSigma sigma) stechkinK 0 := by
  have hadd {s : ℝ} (h : 1 < s) :=
    (((realTerm_hasSum (1 : DirichletCharacter ℂ 1) h).add
      (realTerm_hasSum chi h)).add (realTerm_hasSum psi h)).add
      (realTerm_hasSum (pairCharacter chi psi) h)
  have hsum := (hadd hs).sub ((hadd (hs.trans_le (stechkinSigma_ge hs))).mul_left stechkinK)
  have hn : 0 ≤ ∑' n, (fourWeight chi psi sigma n -
      stechkinK * fourWeight chi psi (stechkinSigma sigma) n) := by
    apply tsum_nonneg
    intro n
    have ha := fourWeight_antitone chi psi hc hp (stechkinSigma_ge hs) n
    have hk := mul_le_mul_of_nonneg_right stechkinK_mem.2
      (fourWeight_nonneg chi psi hc hp (stechkinSigma sigma) n)
    linarith
  simp only [fourWeight] at hn
  rw [hsum.tsum_eq] at hn
  simp only [dampedLogDeriv, Complex.ofReal_zero, mul_zero, add_zero] at *
  linarith

end LiuWang.Proof.SourceRoute.Exception.Restart
