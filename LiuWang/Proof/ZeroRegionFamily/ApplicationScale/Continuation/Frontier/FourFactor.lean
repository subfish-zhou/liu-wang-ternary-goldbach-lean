import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Consumer

/-! # 四因子实际Euler权重的Stechkin差分正性 -/

set_option autoImplicit false
noncomputable section

open Complex
open ArithmeticFunction hiding log
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer
open LiuWang.Proof.ZeroRegionFamily.RealClosure

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

theorem harmonic_real_term {q : ℕ} (chi : DirichletCharacter ℂ q)
    (sigma : ℝ) (n : ℕ) :
    harmonicTerm chi sigma 0 1 n = (chi n).re*((Λ n : ℝ)/(n : ℝ)^sigma) := by
  by_cases hn : n=0
  · simp [hn, harmonicTerm]
  have ha : (((Λ n : ℝ)/(n : ℝ)^sigma : ℝ) : ℂ) =
      (Λ n : ℂ)/(n : ℂ)^(sigma : ℂ) := by
    rw [ofReal_div, ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast]
  simp only [harmonicTerm, pow_one, mul_zero, Complex.ofReal_zero, add_zero,
    LSeries.term_of_ne_zero hn, Pi.mul_apply]
  rw [show chi n*(Λ n : ℂ)/(n : ℂ)^(sigma : ℂ)=
    chi n*(((Λ n : ℝ)/(n : ℝ)^sigma : ℝ) : ℂ) by rw [ha]; ring]
  simp

def fourWeight {q r : ℕ} (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    (sigma : ℝ) (n : ℕ) : ℝ :=
  harmonicTerm (1 : DirichletCharacter ℂ 1) sigma 0 1 n+
    harmonicTerm chi sigma 0 1 n+harmonicTerm psi sigma 0 1 n+
      harmonicTerm (pairCharacter chi psi) sigma 0 1 n

theorem fourWeight_eq {q r : ℕ} (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    (sigma : ℝ) (n : ℕ) :
    fourWeight chi psi sigma n =
      (1+chi n+psi n+pairCharacter chi psi n).re*((Λ n : ℝ)/(n : ℝ)^sigma) := by
  have hone : (1 : DirichletCharacter ℂ 1) n=1 := by
    have hn : (n : ZMod 1)=1 := Subsingleton.elim _ _
    rw [hn]
    simp
  simp only [fourWeight, harmonic_real_term, hone, Complex.add_re, Complex.one_re]
  ring

theorem fourWeight_nonneg {q r : ℕ} (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    (hc : chi^2=1) (hp : psi^2=1) (sigma : ℝ) (n : ℕ) :
    0 ≤ fourWeight chi psi sigma n := by
  rw [fourWeight_eq]
  exact mul_nonneg
    (RCLike.le_iff_re_im.mp (fourFactorEulerCoefficient_nonneg chi psi hc hp n)).1
    (div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) sigma))

theorem fourWeight_antitone {q r : ℕ} (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    (hc : chi^2=1) (hp : psi^2=1) {sigma sigma1 : ℝ} (hs : sigma ≤ sigma1) (n : ℕ) :
    fourWeight chi psi sigma1 n ≤ fourWeight chi psi sigma n := by
  by_cases hn : n=0
  · simp [fourWeight_eq, hn]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hh := Real.rpow_le_rpow_of_exponent_le hn1 hs
  have hf := div_le_div_of_nonneg_left (show 0 ≤ Λ n from vonMangoldt_nonneg)
    (Real.rpow_pos_of_pos hn0 sigma) hh
  rw [fourWeight_eq, fourWeight_eq]
  exact mul_le_mul_of_nonneg_left hf
    (RCLike.le_iff_re_im.mp (fourFactorEulerCoefficient_nonneg chi psi hc hp n)).1

theorem four_factor_damped_nonneg {q r : ℕ} [NeZero q] [NeZero r] [NeZero (q*r)]
    (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    (hc : chi^2=1) (hp : psi^2=1) {sigma sigma1 k : ℝ}
    (hs : 1 < sigma) (hss : sigma ≤ sigma1) (hk : k ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ dampedLogDeriv (1 : DirichletCharacter ℂ 1) sigma sigma1 k 0+
      dampedLogDeriv chi sigma sigma1 k 0+dampedLogDeriv psi sigma sigma1 k 0+
        dampedLogDeriv (pairCharacter chi psi) sigma sigma1 k 0 := by
  have hsum {s : ℝ} (h : 1 < s) :=
    (((harmonicTerm_hasSum (1 : DirichletCharacter ℂ 1) h 0 1).add
      (harmonicTerm_hasSum chi h 0 1)).add (harmonicTerm_hasSum psi h 0 1)).add
      (harmonicTerm_hasSum (pairCharacter chi psi) h 0 1)
  have hh := (hsum hs).sub ((hsum (hs.trans_le hss)).mul_left k)
  have hn : 0 ≤ ∑' n, (fourWeight chi psi sigma n-k*fourWeight chi psi sigma1 n) := by
    apply tsum_nonneg
    intro n
    have hanti := fourWeight_antitone chi psi hc hp hss n
    have hmul := mul_le_mul_of_nonneg_right hk.2 (fourWeight_nonneg chi psi hc hp sigma1 n)
    linarith
  change 0 ≤ ∑' n, ((_+_+_+_)-k*(_+_+_+_)) at hn
  rw [hh.tsum_eq] at hn
  simp only [pow_one, mul_zero, Complex.ofReal_zero, add_zero, Complex.neg_re] at hn
  simp only [dampedLogDeriv, Complex.ofReal_zero, mul_zero, add_zero]
  linarith

theorem four_factor_stechkin_nonneg {q r : ℕ} [NeZero q] [NeZero r] [NeZero (q*r)]
    (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    (hc : chi^2=1) (hp : psi^2=1) {sigma : ℝ} (hs : 1 < sigma) :
    0 ≤ dampedLogDeriv (1 : DirichletCharacter ℂ 1) sigma (stechkinSigma sigma) stechkinK 0+
      dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK 0+
        dampedLogDeriv psi sigma (stechkinSigma sigma) stechkinK 0+
          dampedLogDeriv (pairCharacter chi psi) sigma (stechkinSigma sigma) stechkinK 0 :=
  four_factor_damped_nonneg chi psi hc hp hs (stechkinSigma_ge hs) stechkinK_mem

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier
