import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivative

/-!
# Finite certificates for the archimedean logarithmic derivative

The convergent digamma series gives an explicit error after any positive
number of terms. This is a numerical-certification prefix for the gamma
terms in companion Lemmas 2.4--2.5 and Section 4, not a claim of their
decimal bounds or of a Stirling expansion.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LiuWang.Proof.LocalAnalyticBounds

def digammaApprox (z : Complex) (N : Nat) : Complex :=
  -(Real.eulerMascheroniConstant : Complex) +
    ∑ n ∈ Finset.range N, (((n : Complex) + 1)⁻¹ - (z + n)⁻¹)

private theorem norm_digamma_term_le {a : Real} (ha : 0 < a) (ha1 : a ≤ 1)
    {z : Complex} (hz : a ≤ z.re) (n : Nat) :
    ‖((n : Complex) + 1)⁻¹ - (z + n)⁻¹‖ ≤
      ‖z - 1‖ / (a * ((n : Real) + 1) ^ 2) := by
  have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
  have hpos : 0 < (z + n).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hne : z + n ≠ 0 := by
    intro h
    simp [h] at hpos
  have hnorm : a * ((n : Real) + 1) ≤ ‖z + n‖ := by
    have h := Complex.re_le_norm (z + n)
    simp only [Complex.add_re, Complex.natCast_re] at h
    nlinarith
  rw [Complex.inv_add_one_sub_inv_eq hne, norm_mul, norm_inv, norm_mul,
    Complex.norm_natCast_add_one, ← div_eq_mul_inv]
  calc
    ‖z - 1‖ / (((n : Real) + 1) * ‖z + n‖) ≤
        ‖z - 1‖ / (((n : Real) + 1) * (a * ((n : Real) + 1))) := by
      gcongr
    _ = ‖z - 1‖ / (a * ((n : Real) + 1) ^ 2) := by ring_nf

theorem norm_digamma_sub_approx_le {a : Real} (ha : 0 < a) (ha1 : a ≤ 1)
    {z : Complex} (hz : a ≤ z.re) {N : Nat} (hN : 1 ≤ N) :
    ‖Complex.digamma z - digammaApprox z N‖ ≤ ‖z - 1‖ / (a * N) := by
  have hpoles : ∀ n : Nat, z ≠ -(n : Complex) := by
    intro n h
    have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
    have hr := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    linarith
  let f : Nat → Complex := fun n => ((n : Complex) + 1)⁻¹ - (z + n)⁻¹
  have hsum : HasSum f (Complex.digamma z + Real.eulerMascheroniConstant) := by
    simpa [f, one_div, add_comm] using Complex.hasSum_digamma hpoles
  have hmajor : Summable (fun n : Nat => ‖z - 1‖ / (a * ((n : Real) + 1) ^ 2)) := by
    refine (Complex.summable_one_div_natCast_add_one_sq.mul_left
      (‖z - 1‖ / a)).congr fun n => ?_
    rw [mul_one_div, div_div]
  have hnorm : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_digamma_term_le ha ha1 hz n) hmajor
  have htailNorm : Summable (fun n => ‖f (n + N)‖) :=
    (summable_nat_add_iff N).mpr hnorm
  have htailMajor : Summable
      (fun n : Nat => ‖z - 1‖ / (a * (((n + N : Nat) : Real) + 1) ^ 2)) :=
    (summable_nat_add_iff N).mpr hmajor
  have hsplit := hsum.summable.sum_add_tsum_nat_add N
  have heq : Complex.digamma z - digammaApprox z N = ∑' n, f (n + N) := by
    rw [hsum.tsum_eq] at hsplit
    dsimp [digammaApprox]
    change Complex.digamma z -
      (-(Real.eulerMascheroniConstant : Complex) + ∑ n ∈ Finset.range N, f n) = _
    linear_combination -hsplit
  rw [heq]
  calc
    ‖∑' n, f (n + N)‖ ≤ ∑' n, ‖f (n + N)‖ :=
      norm_tsum_le_tsum_norm htailNorm
    _ ≤ ∑' n : Nat, ‖z - 1‖ / (a * (((n + N : Nat) : Real) + 1) ^ 2) :=
      htailNorm.tsum_le_tsum
        (fun n => norm_digamma_term_le ha ha1 hz (n + N)) htailMajor
    _ = (‖z - 1‖ / a) * ∑' n : Nat, 1 / (((n + N : Nat) : Real) + 1) ^ 2 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [mul_one_div, div_div]
    _ ≤ (‖z - 1‖ / a) * (N : Real)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (Complex.tsum_one_div_natCast_add_add_one_sq_le hN) (by positivity)
    _ = ‖z - 1‖ / (a * N) := by ring

theorem digamma_re_mem_approx_interval {a : Real} (ha : 0 < a) (ha1 : a ≤ 1)
    {z : Complex} (hz : a ≤ z.re) {N : Nat} (hN : 1 ≤ N) :
    (Complex.digamma z).re ∈
      Set.Icc ((digammaApprox z N).re - ‖z - 1‖ / (a * N))
        ((digammaApprox z N).re + ‖z - 1‖ / (a * N)) := by
  have h := (Complex.abs_re_le_norm (Complex.digamma z - digammaApprox z N)).trans
    (norm_digamma_sub_approx_le ha ha1 hz hN)
  rw [Complex.sub_re, abs_le] at h
  constructor <;> linarith [h.1, h.2]

def gammaFactorApprox (z : Complex) (N : Nat) : Complex :=
  -(Real.log Real.pi : Complex) / 2 + (1 / 2 : Complex) * digammaApprox z N

private theorem norm_half_digamma_error {a : Real} (ha : 0 < a) (ha1 : a ≤ 1)
    {z : Complex} (hz : a ≤ z.re) {N : Nat} (hN : 1 ≤ N) :
    ‖(1 / 2 : Complex) * (Complex.digamma z - digammaApprox z N)‖ ≤
      ‖z - 1‖ / (2 * a * N) := by
  rw [norm_mul]
  norm_num
  have h := norm_digamma_sub_approx_le ha ha1 hz hN
  calc
    (1 / 2 : Real) * ‖Complex.digamma z - digammaApprox z N‖ ≤
        (1 / 2) * (‖z - 1‖ / (a * N)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = ‖z - 1‖ / (2 * a * N) := by ring

theorem norm_logDeriv_gammaFactor_sub_approx_even_le
    {q : Nat} {chi : DirichletCharacter Complex q}
    (hEven : DirichletCharacter.Even chi)
    {a : Real} (ha : 0 < a) (ha1 : a ≤ 1)
    {s : Complex} (hs : a ≤ (s / 2).re) {N : Nat} (hN : 1 ≤ N) :
    ‖logDeriv chi.gammaFactor s - gammaFactorApprox (s / 2) N‖ ≤
      ‖s / 2 - 1‖ / (2 * a * N) := by
  have hspos : 0 < s.re := by
    rw [Complex.div_ofNat_re] at hs
    linarith
  rw [BombieriVinogradov.SiegelWalfisz.logDeriv_gammaFactor_of_even hEven hspos]
  convert norm_half_digamma_error ha ha1 hs hN using 1
  congr 1
  dsimp [gammaFactorApprox]
  ring

theorem norm_logDeriv_gammaFactor_sub_approx_odd_le
    {q : Nat} {chi : DirichletCharacter Complex q}
    (hOdd : DirichletCharacter.Odd chi)
    {a : Real} (ha : 0 < a) (ha1 : a ≤ 1)
    {s : Complex} (hspos : 0 < s.re) (hs : a ≤ ((s + 1) / 2).re)
    {N : Nat} (hN : 1 ≤ N) :
    ‖logDeriv chi.gammaFactor s - gammaFactorApprox ((s + 1) / 2) N‖ ≤
      ‖(s + 1) / 2 - 1‖ / (2 * a * N) := by
  rw [BombieriVinogradov.SiegelWalfisz.logDeriv_gammaFactor_of_odd hOdd hspos]
  convert norm_half_digamma_error ha ha1 hs hN using 1
  congr 1
  dsimp [gammaFactorApprox]
  ring

end LiuWang.Proof.LocalAnalyticBounds
