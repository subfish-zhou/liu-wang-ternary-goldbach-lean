import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.RealLogIntegrals
import BombieriVinogradov.Helpers.DirichletCharacter.LogRpowIntegrable
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

def logPowerTerm (x : ℝ) : ℝ := Real.log x * x ^ (-3 / 2 : ℝ)

theorem norm_zeta_real_eq_rpow_sum {s : ℝ} (hs : 1 < s) :
    ‖riemannZeta (s : ℂ)‖ = ∑' n : ℕ, (n : ℝ) ^ (-s) := by
  rw [norm_zeta_real_eq_tsum_norm hs]
  apply tsum_congr
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow (by linarith : -s ≠ 0)]
  · simp [hn, Real.rpow_neg (Nat.cast_nonneg n), one_div]

theorem norm_logMul_term (s : ℝ) (n : ℕ) :
    ‖LSeries.term (LSeries.logMul 1) (s : ℂ) n‖ =
      Real.log n * (n : ℝ) ^ (-s) := by
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, LSeries.logMul, ← Complex.natCast_log,
      Real.norm_of_nonneg (Real.log_natCast_nonneg n),
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem logPowerTerm_summable : Summable (fun n : ℕ => logPowerTerm n) := by
  have h := (LSeriesSummable_logMul_of_lt_re (f := (1 : ℕ → ℂ)) (s := (3 / 2 : ℝ))
    (by
      rw [LSeries.abscissaOfAbsConv_one]
      exact_mod_cast (show (1 : ℝ) < 3 / 2 by norm_num))).norm
  simpa only [norm_logMul_term, logPowerTerm, neg_div] using! h

theorem neg_logDeriv_real_le_series_ratio {s : ℝ} (hs : 1 < s) :
    -(logDeriv riemannZeta (s : ℂ)).re ≤
      (∑' n : ℕ, Real.log n * (n : ℝ) ^ (-s)) /
        (∑' n : ℕ, (n : ℝ) ^ (-s)) := by
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  have hder : deriv (LSeries 1) (s : ℂ) = deriv riemannZeta (s : ℂ) := by
    apply Filter.EventuallyEq.deriv_eq
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hsC,
        fun _ => LSeries_one_eq_riemannZeta⟩
  have hconv : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < (s : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hsC
  have hi : -logDeriv riemannZeta (s : ℂ) =
      LSeries (LSeries.logMul 1) (s : ℂ) / riemannZeta (s : ℂ) := by
    rw [logDeriv_apply, ← hder, LSeries_deriv hconv]
    ring
  have hsum := (LSeriesSummable_logMul_of_lt_re hconv).norm
  have hbound := norm_tsum_le_tsum_norm hsum
  simp only [norm_logMul_term] at hbound
  rw [← norm_zeta_real_eq_rpow_sum hs]
  calc
    _ = (-logDeriv riemannZeta (s : ℂ)).re := by simp
    _ ≤ ‖-logDeriv riemannZeta (s : ℂ)‖ := re_le_norm _
    _ = ‖LSeries (LSeries.logMul 1) (s : ℂ)‖ / ‖riemannZeta (s : ℂ)‖ := by
      rw [hi, norm_div]
    _ ≤ _ := div_le_div_of_nonneg_right hbound (norm_nonneg _)

theorem logPowerTerm_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt logPowerTerm
      ((1 - 3 / 2 * Real.log x) * x ^ (-3 / 2 : ℝ) / x) x := by
  have h := (Real.hasDerivAt_log hx.ne').mul
    (Real.hasDerivAt_rpow_const (p := (-3 / 2 : ℝ)) (Or.inl hx.ne'))
  convert! h using 1
  rw [Real.rpow_sub_one hx.ne']
  ring

theorem logPowerTerm_antitone : AntitoneOn logPowerTerm (Set.Ici 4) := by
  have hd (x : ℝ) (hx : x ∈ Set.Ici (4 : ℝ)) :=
    logPowerTerm_hasDerivAt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hx)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 4)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  have hx4 : 4 ≤ x := interior_subset hx
  have hl : 2 * Real.log 2 ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx4
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rwa [he] at h
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.log_two_gt_d9])
      (Real.rpow_nonneg (by linarith) _)
  · linarith

theorem logPowerTailPrimitive_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (2 * Real.log y + 4) * y ^ (-1 / 2 : ℝ))
      (-logPowerTerm x) x := by
  have h := (((Real.hasDerivAt_log hx.ne').const_mul 2).add_const 4).mul
    (Real.hasDerivAt_rpow_const (p := (-1 / 2 : ℝ)) (Or.inl hx.ne'))
  convert! h using 1
  unfold logPowerTerm
  rw [show (-3 / 2 : ℝ) = -1 / 2 - 1 by norm_num, Real.rpow_sub_one hx.ne']
  ring

theorem logPowerTailPrimitive_tendsto :
    Tendsto (fun x : ℝ => (2 * Real.log x + 4) * x ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
  have hl : Tendsto (fun x : ℝ => Real.log x * x ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [Real.rpow_neg hx.le, div_eq_mul_inv]
  have hp := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have h := (hl.const_mul 2).add (hp.const_mul 4)
  convert! h using 1
  · funext x
    ring
  · norm_num

theorem logPowerTerm_integrable {a : ℝ} (ha : 1 ≤ a) :
    IntegrableOn logPowerTerm (Set.Ioi a) := by
  have h := BombieriVinogradov.integrableOn_log_mul_rpow_neg_add_one
    (by norm_num : (0 : ℝ) < 1 / 2)
  have h' : IntegrableOn logPowerTerm (Set.Ioi 1) := by
    change IntegrableOn (fun t : ℝ => Real.log t * t ^ (-3 / 2 : ℝ)) (Set.Ioi 1)
    convert! h using 1
    norm_num
  exact h'.mono_set (Set.Ioi_subset_Ioi ha)

theorem integral_logPowerTerm {a : ℝ} (ha : 1 ≤ a) :
    (∫ x in Set.Ioi a, logPowerTerm x) =
      (2 * Real.log a + 4) * a ^ (-1 / 2 : ℝ) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x hx => logPowerTailPrimitive_hasDerivAt
      (lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ha) hx))
    (logPowerTerm_integrable ha).neg logPowerTailPrimitive_tendsto
  rw [integral_neg] at h
  linarith

theorem logPowerTerm_sum_upper {N : ℕ} (hN : 4 ≤ N) :
    (∑' n : ℕ, logPowerTerm n) ≤
      (∑ n ∈ Finset.range (N + 1), logPowerTerm n) +
        (2 * Real.log N + 4) * (N : ℝ) ^ (-1 / 2 : ℝ) := by
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have ha := logPowerTerm_antitone.mono (Set.Ici_subset_Ici.mpr hNreal)
  have hi := logPowerTerm_integrable (by linarith : (1 : ℝ) ≤ N)
  have hb := ha.tsum_comp_add_le_integral N hi (fun x hx => by
    change (N : ℝ) < x at hx
    apply mul_nonneg (Real.log_nonneg (by linarith : 1 ≤ x))
    exact Real.rpow_nonneg (by linarith) _)
  rw [integral_logPowerTerm (by linarith : (1 : ℝ) ≤ N)] at hb
  have he := logPowerTerm_summable.sum_add_tsum_nat_add (N + 1)
  simp only [← Nat.add_assoc] at he
  linarith

theorem rpow_three_halves_sum_lower {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range N, (n : ℝ) ^ (-3 / 2 : ℝ)) +
        2 * (N : ℝ) ^ (-1 / 2 : ℝ) ≤
      ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have ha : AntitoneOn (fun x : ℝ => x ^ (-3 / 2 : ℝ)) (Set.Ici (N : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (hNpos.trans_le hx) hxy (by norm_num)
  have hs := Real.summable_nat_rpow.mpr (by norm_num : (-3 / 2 : ℝ) < -1)
  have h := ha.integral_le_tsum_comp_add N hs
    (fun _ hx => Real.rpow_nonneg (le_of_lt (hNpos.trans hx)) _)
  have hi : (∫ x in Set.Ioi (N : ℝ), x ^ (-3 / 2 : ℝ)) =
      2 * (N : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) hNpos]
    norm_num
    ring
  rw [hi] at h
  have he := hs.sum_add_tsum_nat_add N
  linarith

#print axioms neg_logDeriv_real_le_series_ratio
#print axioms logPowerTerm_sum_upper
#print axioms rpow_three_halves_sum_lower

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
