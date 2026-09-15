import LiuWang.Proof.LocalAnalyticBounds.DigammaRemainder
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeries
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Explicit reference-line bounds

The digamma series gives a real-part bound with logarithmic coefficient one.
The von Mangoldt series gives a deliberately coarse numerical bound of six
at real part two. These elementary estimates leave enough room to recover
the source local-count budget at `T >= 2000^15`; no external decimal
digamma estimate is assumed.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace LiuWang.Proof.LocalAnalyticBounds

theorem digamma_re_le_log_add_two {z : Complex} (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2) :
    (Complex.digamma z).re ≤ Real.log (|z.im| + 2) + 2 := by
  let N : Nat := ⌈|z.im|⌉₊ + 1
  have hN : 1 ≤ N := Nat.le_add_left 1 _
  have hNpos : (0 : Real) < N := by exact_mod_cast (by omega : 0 < N)
  have hNlo : |z.im| + 1 ≤ (N : Real) := by
    dsimp [N]
    push_cast
    linarith [Nat.le_ceil |z.im|]
  have hNhi : (N : Real) ≤ |z.im| + 2 := by
    dsimp [N]
    push_cast
    linarith [Nat.ceil_lt_add_one (abs_nonneg z.im)]
  have hzNorm : ‖z - 1‖ ≤ (N : Real) := by
    have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero, abs_of_nonneg (sub_nonneg.mpr hlo)] at h
    linarith
  have herror : ‖z - 1‖ / (1 * (N : Real)) ≤ 1 := by
    simpa using (div_le_one hNpos).mpr hzNorm
  have hhead : (digammaApprox z N).re ≤
      -(Real.eulerMascheroniConstant) + ((harmonic N : Rat) : Real) := by
    simp only [digammaApprox, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.re_sum]
    apply add_le_add le_rfl
    rw [← Complex.sum_inv_natCast_add_one_real]
    apply Finset.sum_le_sum
    intro n _
    have hpos : 0 ≤ ((z + n)⁻¹).re := by
      rw [Complex.inv_re]
      apply div_nonneg
      · simp only [Complex.add_re, Complex.natCast_re]
        linarith [Nat.cast_nonneg (α := Real) n]
      · exact Complex.normSq_nonneg _
    have heq : (((n : Complex) + 1)⁻¹).re = ((n : Real) + 1)⁻¹ := by
      simp only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
        ← Complex.ofReal_inv, Complex.ofReal_re]
    rw [Complex.sub_re, heq]
    linarith
  have hgamma : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have happrox := (digamma_re_mem_approx_interval (by norm_num : (0 : Real) < 1)
    le_rfl hlo hN).2
  have hlog := Real.log_le_log hNpos hNhi
  have hharm := harmonic_le_one_add_log N
  linarith

private theorem gamma_re_bound_of_formula {s z : Complex}
    {q : Nat} {chi : DirichletCharacter Complex q}
    (hFormula : logDeriv chi.gammaFactor s =
      -(Real.log Real.pi : Complex) / 2 + (1 / 2 : Complex) * Complex.digamma z)
    (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2) (him : |z.im| ≤ |s.im|) :
    (logDeriv chi.gammaFactor s).re ≤ Real.log (|s.im| + 2) / 2 + 1 := by
  have hd := digamma_re_le_log_add_two hlo hhi
  have hl := Real.log_le_log (by positivity : 0 < |z.im| + 2) (by linarith : |z.im| + 2 ≤ |s.im| + 2)
  have hp : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  rw [hFormula]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re,
    Complex.mul_re]
  norm_num
  linarith

theorem logDeriv_gammaFactor_re_le_on_two {q : Nat} (chi : DirichletCharacter Complex q)
    {s : Complex} (hs : s.re = 2) :
    (logDeriv chi.gammaFactor s).re ≤ Real.log (|s.im| + 2) / 2 + 1 := by
  have hspos : 0 < s.re := by linarith
  rcases chi.even_or_odd with he | ho
  · apply gamma_re_bound_of_formula
      (BombieriVinogradov.SiegelWalfisz.logDeriv_gammaFactor_of_even he hspos)
    · norm_num [Complex.div_ofNat_re, hs]
    · norm_num [Complex.div_ofNat_re, hs]
    · rw [Complex.div_ofNat_im, abs_div]
      norm_num
  · apply gamma_re_bound_of_formula
      (BombieriVinogradov.SiegelWalfisz.logDeriv_gammaFactor_of_odd ho hspos)
    · norm_num [Complex.div_ofNat_re, hs]
    · norm_num [Complex.div_ofNat_re, hs]
    · simp only [Complex.div_ofNat_im, Complex.add_im, Complex.one_im, add_zero,
        abs_div]
      norm_num

theorem norm_neg_logDeriv_zeta_two_le_six :
    ‖-deriv riemannZeta (2 : Complex) / riemannZeta (2 : Complex)‖ ≤ 6 := by
  have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (2 : Complex)) (by norm_num)
  have hid := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (2 : Complex)) (by norm_num)
  have hp : Summable (fun n : Nat => (n : Real) ^ (-(3 / 2 : Real))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hterm : ∀ n : Nat,
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : Complex)) 2 n‖ ≤
        2 * (n : Real) ^ (-(3 / 2 : Real)) := by
    intro n
    have heq := BombieriVinogradov.SiegelWalfisz.norm_LSeriesTerm_vonMangoldt_eq
      (c := 2) n
    norm_num at heq
    rw [heq]
    by_cases hn : n = 0
    · subst n
      norm_num
    have hnpos : (0 : Real) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hlog := Real.log_natCast_le_rpow_div n (by norm_num : (0 : Real) < 1 / 2)
    have hlam : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
      ArithmeticFunction.vonMangoldt_le_log
    rw [← Real.rpow_natCast]
    calc
      ArithmeticFunction.vonMangoldt n / (n : Real) ^ (2 : Real) ≤
          ((n : Real) ^ (1 / 2 : Real) / (1 / 2)) / (n : Real) ^ (2 : Real) :=
        div_le_div_of_nonneg_right (hlam.trans hlog) (by positivity)
      _ = 2 * (n : Real) ^ (-(3 / 2 : Real)) := by
        calc
          _ = 2 * ((n : Real) ^ (1 / 2 : Real) / (n : Real) ^ (2 : Real)) := by ring
          _ = _ := by rw [← Real.rpow_sub hnpos]; norm_num
  rw [← hid]
  change ‖∑' n, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : Complex)) 2 n‖ ≤ 6
  calc
    _ ≤ ∑' n, ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : Complex)) 2 n‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : Nat, 2 * (n : Real) ^ (-(3 / 2 : Real)) :=
      hs.norm.tsum_le_tsum hterm (hp.mul_left 2)
    _ = 2 * ∑' n : Nat, (n : Real) ^ (-(3 / 2 : Real)) := tsum_mul_left
    _ ≤ 6 := by
      have h := AnalyticNumberTheory.LargeSieve.tsum_nat_rpow_neg_le
        (3 / 2 : Real) (by norm_num)
      norm_num at h
      linarith

end LiuWang.Proof.LocalAnalyticBounds
