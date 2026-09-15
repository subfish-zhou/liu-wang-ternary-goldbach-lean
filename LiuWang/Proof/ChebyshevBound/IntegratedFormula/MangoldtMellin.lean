import LiuWang.Proof.ChebyshevBound.IntegratedFormula.ZeroMellin

/-! # 实际 Λ 三角核级数、积分 psi 有限和与 Mellin 变换。 -/

set_option autoImplicit false
noncomputable section

open Complex Set MeasureTheory ArithmeticFunction Finset
open LiuWang.Proof.ChebyshevBound.HighHeight
open scoped LSeries.notation

namespace LiuWang.Proof.ChebyshevBound.IntegratedFormula

def mangoldtTriangle (n : ℕ) (u : ℝ) : ℂ := (Λ n : ℂ) * triangle ((n : ℝ) * u)

theorem hasMellin_mangoldtTriangle (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (mangoldtTriangle n) s (LSeries.term (↗Λ) s n / (s * (s + 1))) := by
  by_cases hn : n = 0
  · subst n
    simp [mangoldtTriangle, HasMellin, MellinConvergent, mellin]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hm := hasMellin_triangle hs
  have hc : MellinConvergent (fun u => triangle ((n : ℝ) * u)) s :=
    (MellinConvergent.comp_mul_left hn0).2 hm.1
  refine ⟨hc.const_smul (Λ n : ℂ), ?_⟩
  change mellin (fun u => (Λ n : ℂ) • triangle ((n : ℝ) * u)) s = _
  rw [mellin_const_smul, mellin_comp_mul_left _ _ hn0, hm.2,
    smul_eq_mul, smul_eq_mul, LSeries.term_of_ne_zero hn, Complex.cpow_neg]
  push_cast
  ring

theorem triangle_norm_le_one {u : ℝ} (hu : 0 < u) : ‖triangle u‖ ≤ 1 := by
  rw [triangle_of_pos hu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (by linarith)

theorem mangoldtTriangle_norm_le (n : ℕ) {u : ℝ} (hu : 0 < u) :
    ‖mangoldtTriangle n u‖ ≤ ‖LSeries.term (↗Λ) (2 : ℂ) n‖ * ‖powerCut (-2) u‖ := by
  by_cases hn : n = 0
  · subst n; simp [mangoldtTriangle]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hnu : 0 < (n : ℝ) * u := mul_pos hn0 hu
  by_cases h : (n : ℝ) * u ≤ 1
  · have hu1 : u ≤ 1 := by nlinarith
    have hmem : u ∈ Set.Ioc 0 1 := ⟨hu, hu1⟩
    have hg : ‖powerCut (-2) u‖ = (u ^ 2)⁻¹ := by
      simp [powerCut, hmem, Complex.norm_cpow_eq_rpow_re_of_pos hu]
    have hw : ‖LSeries.term (↗Λ) (2 : ℂ) n‖ = Λ n / (n : ℝ) ^ 2 := by
      simp [hn, abs_of_nonneg vonMangoldt_nonneg]
    rw [hg, hw]
    have hscale : (1 : ℝ) ≤ ((n : ℝ) ^ 2 * u ^ 2)⁻¹ := by
      apply (one_le_inv₀ (by positivity)).2
      nlinarith [sq_nonneg ((n : ℝ) * u - 1)]
    have hnorm : ‖mangoldtTriangle n u‖ ≤ Λ n := by
      rw [mangoldtTriangle, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_of_le_one_right vonMangoldt_nonneg (triangle_norm_le_one hnu)
    calc
      _ ≤ Λ n := hnorm
      _ ≤ Λ n * ((n : ℝ) ^ 2 * u ^ 2)⁻¹ :=
        le_mul_of_one_le_right vonMangoldt_nonneg hscale
      _ = _ := by ring
  · have hzero : triangle ((n : ℝ) * u) = 0 := by
      rw [triangle_of_pos hnu]
      simp [max_eq_left (by linarith : 1 - (n : ℝ) * u ≤ 0)]
    rw [mangoldtTriangle, hzero, mul_zero, norm_zero]
    positivity

theorem mangoldtTriangle_summable {u : ℝ} (hu : 0 < u) :
    Summable (fun n => mangoldtTriangle n u) :=
  (((LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm).mul_right
    ‖powerCut (-2) u‖).of_norm_bounded (fun n => mangoldtTriangle_norm_le n hu)

theorem hasMellin_mangoldtSum {s : ℂ} (hs : 2 < s.re) :
    HasMellin (fun u => ∑' n, mangoldtTriangle n u) s
      ((-deriv riemannZeta s / riemannZeta s) / (s * (s + 1))) := by
  have h := hasMellin_tsum_dominated
    (fun n => hasMellin_mangoldtTriangle n (by linarith : 0 < s.re))
    (hasMellin_powerCut (-2) (s := s) (by simp; linarith)).1
    (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
    (fun n _ hu => mangoldtTriangle_norm_le n hu)
  rw [tsum_div_const] at h
  have heq : (∑' n, LSeries.term (↗Λ) s n) = -deriv riemannZeta s / riemannZeta s :=
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by linarith)
  rwa [heq] at h

theorem mangoldtSum_at_inverse {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * (∑' n, mangoldtTriangle n x⁻¹) = (integratedPsi x : ℂ) := by
  have hnzero (n : ℕ) (hn : n ∉ Finset.Ioc 0 ⌊x⌋₊) : mangoldtTriangle n x⁻¹ = 0 := by
    by_cases hn0 : n = 0
    · subst n; simp [mangoldtTriangle]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hnx : x < (n : ℝ) := by
      apply (Nat.floor_lt hx.le).1
      have := not_and.mp (fun h => hn (mem_Ioc.mpr h))
      omega
    rw [mangoldtTriangle, triangle_of_pos (mul_pos hnpos (inv_pos.mpr hx))]
    have hlt : 1 < (n : ℝ) * x⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (one_lt_div hx).2 hnx
    simp [max_eq_left (by linarith : 1 - (n : ℝ) * x⁻¹ ≤ 0)]
  rw [tsum_eq_sum hnzero, mul_sum]
  simp only [integratedPsi, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_natCast]
  apply sum_congr rfl
  intro n hn
  have hn' := mem_Ioc.mp hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn'.1
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).1 hn'.2
  have hnu : (n : ℝ) * x⁻¹ ≤ 1 := by rw [← div_eq_mul_inv]; exact (div_le_one hx).2 hnx
  rw [mangoldtTriangle, triangle_of_pos (mul_pos hnpos (inv_pos.mpr hx)),
    max_eq_right (by linarith : 0 ≤ 1 - (n : ℝ) * x⁻¹)]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']

end LiuWang.Proof.ChebyshevBound.IntegratedFormula
