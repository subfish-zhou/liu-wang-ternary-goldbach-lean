import LiuWang.Proof.Campaign20260915.Totient.ZeroDecay
import LiuWang.Proof.ChebyshevBound.IntegratedFormula.Difference

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ChebyshevBound.IntegratedFormula

namespace LiuWang.Proof.Campaign20260915.Totient

theorem integratedPsi_difference_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    integratedPsi y - integratedPsi x ≤ (y - x) * Chebyshev.psi y := by
  have hy : 0 ≤ y := hx.trans hxy
  have hsub : Ioc 0 ⌊x⌋₊ ⊆ Ioc 0 ⌊y⌋₊ :=
    Ioc_subset_Ioc le_rfl (Nat.floor_le_floor hxy)
  have hid : integratedPsi x =
      ∑ n ∈ Ioc 0 ⌊y⌋₊, if n ≤ ⌊x⌋₊ then
        ArithmeticFunction.vonMangoldt n * (x - n) else 0 := by
    rw [← Finset.sum_filter]
    unfold integratedPsi
    congr 1
    ext n
    simp only [mem_filter, mem_Ioc]
    have := Nat.floor_le_floor hxy
    omega
  rw [hid]
  unfold integratedPsi Chebyshev.psi
  rw [← sum_sub_distrib, mul_sum]
  apply sum_le_sum
  intro n hn
  split_ifs with hnx
  · apply le_of_eq
    ring
  · have hxn : x < (n : ℝ) := (Nat.floor_lt hx).mp (by omega)
    have hnonneg := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    nlinarith

private theorem exp100_ge_million : (1000000 : ℝ) ≤ Real.exp 100 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 100) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem log_large_of_tail {x : ℝ} (hx : 2 * Real.exp 100 ≤ Real.log x) :
    (1000000 : ℝ) ≤ Real.log x := by
  linarith [exp100_ge_million]

private theorem twenty_log_pow_six_le {x : ℝ} (hx0 : 0 < x)
    (hx : 2 * Real.exp 100 ≤ Real.log x) :
    20 * Real.log x ^ 6 ≤ x := by
  have hL := log_large_of_tail hx
  have h : Real.log x ^ 8 / 40320 ≤ Real.exp (Real.log x) := by
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ Real.log x) 9)
    have hs := Finset.single_le_sum (f := fun i : ℕ =>
      Real.log x ^ i / (Nat.factorial i : ℝ))
      (fun i (_ : i ∈ Finset.range 9) => by positivity)
      (by norm_num : 8 ∈ Finset.range 9)
    norm_num at hs
    exact hs
  rw [Real.exp_log hx0] at h
  have hsq : (1000000 : ℝ) ^ 2 ≤ Real.log x ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hL 2
  have hp := mul_le_mul_of_nonneg_right hsq (pow_nonneg (by linarith : 0 ≤ Real.log x) 6)
  nlinarith only [h, hp, pow_nonneg (by linarith : 0 ≤ Real.log x) 6]

private theorem neighbor_log {x t : ℝ} (hx0 : 0 < x)
    (hx : 2 * Real.exp 100 ≤ Real.log x) (ht : x / 2 ≤ t) :
    Real.log x / 2 ≤ Real.log t ∧ Real.exp 100 ≤ Real.log t := by
  have hlog := Real.log_le_log (by positivity : 0 < x / 2) ht
  rw [Real.log_div hx0.ne' (by norm_num)] at hlog
  have hL := log_large_of_tail hx
  constructor <;> linarith [Real.log_two_lt_d9]

private theorem neighbor_zero_sum {x t : ℝ} (hx0 : 0 < x)
    (hx : 2 * Real.exp 100 ≤ Real.log x) (ht : x / 2 ≤ t) (ht' : t ≤ 2 * x) :
    ‖∑' p, integratedZeroTerm t p‖ ≤ 256 * x ^ 2 / Real.log x ^ 6 := by
  have ht0 : 0 < t := by linarith
  have hL := log_large_of_tail hx
  have hn := neighbor_log hx0 hx ht
  apply (integratedZeroSum_norm_le_log_sixth ht0 hn.2).trans
  calc
    _ ≤ (2 * x) ^ 2 / (Real.log x / 2) ^ 6 := by
      apply div_le_div₀ (by positivity) (pow_le_pow_left₀ ht0.le ht' 2)
        (by positivity) (pow_le_pow_left₀ (by linarith) hn.1 6)
    _ = _ := by ring

private theorem neighbor_integrated_error {x a b : ℝ} (hx0 : 0 < x)
    (hx : 2 * Real.exp 100 ≤ Real.log x)
    (ha : x / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * x) :
    |integratedPsi b - integratedPsi a - (b ^ 2 - a ^ 2) / 2| ≤
      512 * x ^ 2 / Real.log x ^ 6 + 20 * x := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hla := (neighbor_log hx0 hx ha).2
  have hlb := (neighbor_log hx0 hx (ha.trans hab)).2
  have ha1 : 1 < a := (Real.log_pos_iff ha0.le).mp ((Real.exp_pos 100).trans_le hla)
  have hb1 : 1 < b := ha1.trans_le hab
  have hlogpi : |Real.log (2 * Real.pi)| ≤ 3 := by
    rw [abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have h := Real.log_le_log (by positivity : 0 < 2 * Real.pi)
      (by linarith [Real.pi_lt_four] : 2 * Real.pi ≤ 8)
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_two_lt_d9]
  have he := integratedPsi_difference_formula ha1 hb1
    (by linarith [exp100_ge_million]) (by linarith [exp100_ge_million])
  have hid :
      ((integratedPsi b - integratedPsi a - (b ^ 2 - a ^ 2) / 2 : ℝ) : ℂ) =
        -((Real.log (2 * Real.pi) * (b - a) : ℝ) : ℂ) -
          ((∑' p, integratedZeroTerm b p) - ∑' p, integratedZeroTerm a p) +
          (gammaCorrection b - gammaCorrection a) := by
    rw [Complex.ofReal_sub, he]
    push_cast
    ring
  have hh := congrArg norm hid
  rw [Complex.norm_real, Real.norm_eq_abs] at hh
  rw [hh]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) (norm_sub_le _ _)).trans
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sub_nonneg.mpr hab)]
  have hz := (norm_sub_le _ _).trans
    (add_le_add (neighbor_zero_sum hx0 hx (ha.trans hab) hb)
      (neighbor_zero_sum hx0 hx ha (hab.trans hb)))
  have hg := add_le_add (gammaCorrection_norm_le hb1.le) (gammaCorrection_norm_le ha1.le)
  have hl := mul_le_mul_of_nonneg_right hlogpi (sub_nonneg.mpr hab)
  have hz' : ‖(∑' p, integratedZeroTerm b p) - ∑' p, integratedZeroTerm a p‖ ≤
      512 * x ^ 2 / Real.log x ^ 6 := by
    exact hz.trans_eq (by ring)
  linarith

theorem psi_error_le_log_cube {x : ℝ} (hx0 : 0 < x)
    (hx : 2 * Real.exp 100 ≤ Real.log x) :
    |Chebyshev.psi x - x| ≤ 514 * x / Real.log x ^ 3 := by
  let L := Real.log x
  let h := x / L ^ 3
  have hL : 1000000 ≤ L := log_large_of_tail hx
  have hL0 : 0 < L := by linarith
  have hh0 : 0 < h := by dsimp [h]; positivity
  have hL3 : 2 ≤ L ^ 3 := by nlinarith [sq_nonneg (L - 1)]
  have hh : h ≤ x / 2 := by
    dsimp [h]
    exact div_le_div_of_nonneg_left hx0.le (by norm_num) hL3
  have hup := neighbor_integrated_error hx0 hx (a := x) (b := x + h)
    (by linarith) (by linarith) (by linarith)
  have hlo := neighbor_integrated_error hx0 hx (a := x - h) (b := x)
    (by linarith) (by linarith) (by linarith)
  have hpsiup := integratedPsi_difference_ge hx0.le (show x ≤ x + h by linarith)
  have hpsilo := integratedPsi_difference_le (show 0 ≤ x - h by linarith)
    (show x - h ≤ x by linarith)
  have hsmall := twenty_log_pow_six_le hx0 hx
  change 20 * L ^ 6 ≤ x at hsmall
  have hbudget : h ^ 2 / 2 + (512 * x ^ 2 / L ^ 6 + 20 * x) ≤
      h * (514 * x / L ^ 3) := by
    dsimp [h]
    apply (mul_le_mul_iff_right₀ (pow_pos hL0 6)).mp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hsmall hx0.le]
  rw [abs_le] at hup hlo ⊢
  constructor
  · apply (mul_le_mul_iff_right₀ hh0).mp
    nlinarith only [hlo.1, hpsilo, hbudget]
  · apply (mul_le_mul_iff_right₀ hh0).mp
    nlinarith only [hup.2, hpsiup, hbudget]

theorem prime_power_error_le_log_cube {x : ℝ} (hx0 : 0 < x)
    (hx : 2 * Real.exp 100 ≤ Real.log x) :
    |Chebyshev.psi x - Chebyshev.theta x| ≤ x / Real.log x ^ 3 := by
  have hL := log_large_of_tail hx
  have hL0 : 0 < Real.log x := by linarith
  have hx1 : 1 ≤ x := (Real.log_pos_iff hx0.le).mp hL0 |>.le
  have hs : 2 * Real.log x ^ 4 ≤ Real.sqrt x := by
    have hterm : (Real.log x / 2) ^ 10 / 3628800 ≤ Real.exp (Real.log x / 2) := by
      apply le_trans _ (Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ Real.log x / 2) 11)
      have h := Finset.single_le_sum (f := fun i : ℕ =>
        (Real.log x / 2) ^ i / (Nat.factorial i : ℝ))
        (fun i (_ : i ∈ Finset.range 11) => by positivity)
        (by norm_num : 10 ∈ Finset.range 11)
      norm_num at h
      exact h
    rw [Real.exp_half, Real.exp_log hx0] at hterm
    have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num) hL 6) (pow_nonneg hL0.le 4)
    nlinarith only [hterm, hp, pow_nonneg hL0.le 4]
  apply (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1).trans
  apply (le_div_iff₀ (pow_pos hL0 3)).mpr
  have h := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg x)
  rw [Real.mul_self_sqrt hx0.le] at h
  nlinarith only [h]

theorem theta_error_le_log_cube {x : ℝ} (hx0 : 0 < x)
    (hx : 2 * Real.exp 100 ≤ Real.log x) :
    |Chebyshev.theta x - x| ≤ 515 * x / Real.log x ^ 3 := by
  have h := abs_add_le (Chebyshev.theta x - Chebyshev.psi x) (Chebyshev.psi x - x)
  rw [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] at h
  have he : Chebyshev.theta x - Chebyshev.psi x + (Chebyshev.psi x - x) =
      Chebyshev.theta x - x := by ring
  rw [he] at h
  exact (h.trans (add_le_add (prime_power_error_le_log_cube hx0 hx)
    (psi_error_le_log_cube hx0 hx))).trans_eq (by ring)

#print axioms integratedPsi_difference_le
#print axioms log_large_of_tail
#print axioms psi_error_le_log_cube
#print axioms prime_power_error_le_log_cube
#print axioms theta_error_le_log_cube

end LiuWang.Proof.Campaign20260915.Totient
