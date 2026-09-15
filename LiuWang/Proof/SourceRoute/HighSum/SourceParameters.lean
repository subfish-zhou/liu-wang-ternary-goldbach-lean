import LiuWang.Proof.SourceRoute.HighSum.DensityIntegral

/-! # The full original parameter domain for the (2.24) integral -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum

theorem original_product_ge {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    (100000000000 : ℝ) ≤ (q : ℝ) * y := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hL := Parameters.sourceL_ge_3100 hN
  have hp : (3100 : ℝ) ^ (3 : ℕ) ≤ sourceL N ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hL _
  have hh : 3.36 * sourceL N ^ (3 : ℕ) ≤ (q : ℝ) * y := by
    have h := (div_le_iff₀ hq).mp hy
    simpa only [sourceP, mul_comm] using h
  nlinarith

theorem original_log_product_ge_ten {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    10 ≤ Real.log ((q : ℝ) * y) := by
  have hp := original_product_ge hN hy
  apply (Real.le_log_iff_exp_le (by linarith)).mpr
  have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 10
  rw [← Real.exp_nat_mul] at he
  norm_num at he
  linarith

theorem original_density_rate_pos {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : 0 < y) (hyT : y ≤ sourceT N) :
    0 < sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) := by
  have hL := Parameters.sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hlogq : Real.log q ≤ 3 * Real.log (sourceL N) := by
    simpa only [sourceP, Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hq0 hq
  have hlogy : Real.log y ≤ 15 * Real.log (sourceL N) := by
    simpa only [sourceT, Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hy hyT
  rw [Real.log_mul (pow_pos hq0 _).ne' (pow_pos hy _).ne',
    Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith [log_le_original_linear hL]

theorem original_alpha_cutoff_mem {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    1 - 0.478 / Real.log ((q : ℝ) * y) ∈ Set.Icc (19 / 20 : ℝ) 1 := by
  have hs := original_log_product_ge_ten hN hy
  have hs0 : 0 < Real.log ((q : ℝ) * y) := by linarith
  have hd : (0.478 : ℝ) / Real.log ((q : ℝ) * y) ≤ 1 / 20 :=
    (div_le_iff₀ hs0).mpr (by linarith)
  have hd0 : 0 ≤ (0.478 : ℝ) / Real.log ((q : ℝ) * y) := by positivity
  constructor <;> linarith

theorem log_density_ratio {N q : ℕ} [NeZero q] (hN : 0 < N)
    {y : ℝ} (hy : 0 < y) :
    Real.log ((N : ℝ) / ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))) =
      sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  exact Real.log_div (Nat.cast_pos.mpr hN).ne' (by positivity)

theorem original_source24_formula {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) (hyT : y ≤ sourceT N) :
    (∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
      layerKernel N alpha * Applications.sourceSevenBound q alpha y) ≤
      (17102 + 254231 / Real.log ((q : ℝ) * y)) *
        Real.log ((q : ℝ) * y) ^ (6 : ℕ) * sourceL N /
          Real.log ((N : ℝ) / ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))) *
        ((N : ℝ) / ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))) ^
          (-0.478 / Real.log ((q : ℝ) * y)) +
      16541 * Real.log y ^ (6 : ℕ) *
        (N : ℝ) ^ (-0.478 / Real.log ((q : ℝ) * y)) := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hn0 : (0 : ℝ) < N := Nat.cast_pos.mpr hn
  have hn1 : 1 < (N : ℝ) :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 3100)).trans_le hN
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hy0 : 0 < y := by
    have hp := original_product_ge hN hy
    exact (mul_pos_iff_of_pos_left hq0).mp (by linarith : 0 < (q : ℝ) * y)
  have hs := original_log_product_ge_ten hN hy
  have hd := original_density_rate_pos hN hq hy0 hyT
  have hh := sourceSeven_integral_le_source24 hn1 hy0 (by linarith) hd
    (original_alpha_cutoff_mem hN hy).1
  rw [Real.rpow_def_of_pos (div_pos hn0 (by positivity)),
    Real.rpow_def_of_pos hn0, log_density_ratio hn hy0]
  have he (t : ℝ) : t * (-0.478 / Real.log ((q : ℝ) * y)) =
      -0.478 * t / Real.log ((q : ℝ) * y) := by ring
  simpa only [he, sourceL] using hh

end LiuWang.Proof.SourceRoute.HighSum
