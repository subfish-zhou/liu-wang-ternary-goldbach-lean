import LiuWang.Proof.ZeroRegionFamily.RealClosure.Consumer

/-! # 非负四次多项式的全部字符幂实际Stechkin Euler正性 -/

set_option autoImplicit false
noncomputable section

open Complex
open ArithmeticFunction hiding log
open BombieriVinogradov.SiegelWalfisz
open scoped LSeries.notation Classical

namespace LiuWang.Proof.ZeroRegionFamily.RealClosure

theorem quartic_unit_nonneg {z : ℂ} (hz : ‖z‖=1) :
    0 ≤ (14379+24480*z+14900*z^2+6000*z^3+1250*z^4).re := by
  have hy : z.im^2=1-z.re^2 := by
    have hh := Complex.normSq_eq_norm_sq z
    rw [hz] at hh
    simp only [Complex.normSq_apply] at hh
    nlinarith
  have he : (14379+24480*z+14900*z^2+6000*z^3+1250*z^4).re =
      10000*(z.re+9/10)^2*(z.re+3/10)^2 := by
    norm_num [pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re]
    ring_nf
    rw [show z.im^4=(z.im^2)^2 by ring, hy]
    ring
  rw [he]
  positivity

def harmonicTerm {q : ℕ} (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (k n : ℕ) : ℝ :=
  (LSeries.term (↗(chi^k)*↗Λ) ((sigma : ℂ)+I*((k : ℝ)*t : ℝ)) n).re

theorem harmonicTerm_unit {q n : ℕ} (chi : DirichletCharacter ℂ q)
    (hn : n ≠ 0) (hu : IsUnit (n : ZMod q)) (sigma t : ℝ) (k : ℕ) :
    harmonicTerm chi sigma t k n =
      ((((Λ n*(n : ℝ)^(-sigma) : ℝ) : ℂ))*
        (chi n*(n : ℂ)^(-(I*(t : ℂ))))^k).re := by
  have hp : (chi^k) n=(chi n)^k := by
    cases k with
    | zero => simp [MulChar.one_apply hu]
    | succ k => exact chi.pow_apply' (Nat.succ_ne_zero k) _
  unfold harmonicTerm
  rw [LSeries.term_of_ne_zero hn, Pi.mul_apply, hp, div_eq_mul_inv, ← cpow_neg,
    natCast_cpow_neg_add_I_mul hn]
  have he : -(I*((k : ℝ)*t : ℝ))=(k : ℂ)*(-(I*(t : ℂ))) := by push_cast; ring
  rw [he, cpow_nat_mul]
  push_cast
  congr 1
  rw [mul_pow]
  ring

def quarticWeight {q : ℕ} (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (n : ℕ) : ℝ :=
  14379*harmonicTerm chi sigma t 0 n+24480*harmonicTerm chi sigma t 1 n+
    14900*harmonicTerm chi sigma t 2 n+6000*harmonicTerm chi sigma t 3 n+
      1250*harmonicTerm chi sigma t 4 n

theorem quarticWeight_eq {q : ℕ} (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (n : ℕ) :
    quarticWeight chi sigma t n =
      if n=0 ∨ ¬IsUnit (n : ZMod q) then 0 else
        Λ n*(n : ℝ)^(-sigma)*
          (14379+24480*(chi n*(n : ℂ)^(-(I*(t : ℂ))))+
            14900*(chi n*(n : ℂ)^(-(I*(t : ℂ))))^2+
            6000*(chi n*(n : ℂ)^(-(I*(t : ℂ))))^3+
            1250*(chi n*(n : ℂ)^(-(I*(t : ℂ))))^4).re := by
  classical
  by_cases hn : n=0
  · subst n
    simp [quarticWeight, harmonicTerm]
  by_cases hu : IsUnit (n : ZMod q)
  · simp only [hn, hu, not_true_eq_false, or_self, if_false]
    unfold quarticWeight
    simp only [harmonicTerm_unit chi hn hu, pow_zero, pow_one]
    norm_num [Complex.mul_re, Complex.add_re]
    ring
  · have hv (k : ℕ) : (chi^k) n=0 := MulChar.map_nonunit _ hu
    have h0 := hv 0
    have h1 := hv 1
    simp only [pow_zero, pow_one] at h0 h1
    simp [quarticWeight, harmonicTerm, LSeries.term_of_ne_zero hn, hv, h0, h1, hu]

theorem quarticWeight_nonneg {q : ℕ} (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (n : ℕ) :
    0 ≤ quarticWeight chi sigma t n := by
  classical
  rw [quarticWeight_eq]
  split_ifs with h
  · exact le_rfl
  · have hn : n ≠ 0 := fun he => h (Or.inl he)
    have hu : IsUnit (n : ZMod q) := by tauto
    have hz : ‖chi n*(n : ℂ)^(-(I*(t : ℂ)))‖=1 := by
      rw [norm_mul, ← hu.unit_spec, DirichletCharacter.unit_norm_eq_one chi hu.unit, one_mul,
        ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
          (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      norm_num [Complex.mul_re]
    exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (quartic_unit_nonneg hz)

theorem quarticWeight_antitone {q : ℕ} (chi : DirichletCharacter ℂ q)
    {sigma sigma1 : ℝ} (hs : sigma ≤ sigma1) (t : ℝ) (n : ℕ) :
    quarticWeight chi sigma1 t n ≤ quarticWeight chi sigma t n := by
  classical
  by_cases hn : n=0
  · simp [quarticWeight_eq, hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have he : quarticWeight chi sigma1 t n =
      (n : ℝ)^(sigma-sigma1)*quarticWeight chi sigma t n := by
    rw [quarticWeight_eq, quarticWeight_eq]
    split_ifs
    · ring
    · have hh : (n : ℝ)^(sigma-sigma1)*(n : ℝ)^(-sigma)=(n : ℝ)^(-sigma1) := by
        rw [← Real.rpow_add hn0]
        congr 1
        ring
      rw [show ∀ a b c d : ℝ, a*(b*c*d)=b*(a*c)*d by intros; ring, hh]
  rw [he]
  exact (mul_le_mul_of_nonneg_right
    (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))
    (quarticWeight_nonneg chi sigma t n)).trans_eq (one_mul _)

theorem harmonicTerm_hasSum {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) (k : ℕ) :
    HasSum (harmonicTerm chi sigma t k)
      (-(logDeriv (chi^k).LFunction ((sigma : ℂ)+I*((k : ℝ)*t : ℝ)))).re := by
  have hreal : 1 < ((sigma : ℂ)+I*((k : ℝ)*t : ℝ)).re := by simpa using hs
  have hh := hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (chi^k) hreal).LSeriesHasSum
  change HasSum (harmonicTerm chi sigma t k) _ at hh
  simpa only [logDeriv, Pi.div_apply, ← neg_div,
    neg_logDeriv_LFunction_eq_twist_vonMangoldt _ hreal] using hh

theorem quartic_stechkin_nonneg {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    0 ≤ 14379*dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma (stechkinSigma sigma) stechkinK 0+
      24480*dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t+
      14900*dampedLogDeriv (chi^2) sigma (stechkinSigma sigma) stechkinK (2*t)+
      6000*dampedLogDeriv (chi^3) sigma (stechkinSigma sigma) stechkinK (3*t)+
      1250*dampedLogDeriv (chi^4) sigma (stechkinSigma sigma) stechkinK (4*t) := by
  have hadd {s : ℝ} (h : 1 < s) :=
    ((((harmonicTerm_hasSum chi h t 0).mul_left 14379).add
      ((harmonicTerm_hasSum chi h t 1).mul_left 24480)).add
      ((harmonicTerm_hasSum chi h t 2).mul_left 14900)).add
      ((harmonicTerm_hasSum chi h t 3).mul_left 6000) |>.add
      ((harmonicTerm_hasSum chi h t 4).mul_left 1250)
  have hsum := (hadd hs).sub ((hadd (hs.trans_le (stechkinSigma_ge hs))).mul_left stechkinK)
  have hn : 0 ≤ ∑' n, (quarticWeight chi sigma t n-
      stechkinK*quarticWeight chi (stechkinSigma sigma) t n) := by
    apply tsum_nonneg
    intro n
    have hanti := quarticWeight_antitone chi (stechkinSigma_ge hs) t n
    have hk := mul_le_mul_of_nonneg_right stechkinK_mem.2
      (quarticWeight_nonneg chi (stechkinSigma sigma) t n)
    linarith
  simp only [quarticWeight] at hn
  rw [hsum.tsum_eq] at hn
  simp only [dampedLogDeriv, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    zero_mul, one_mul, Complex.ofReal_zero, mul_zero, add_zero, pow_zero, pow_one,
    Complex.neg_re] at *
  linarith

end LiuWang.Proof.ZeroRegionFamily.RealClosure
