import LiuWang.Proof.ChebyshevBound.IntegratedFormula.MangoldtMellin

/-! # Γ 修正及 ζ 极点主项的实际 Mellin 原像。 -/

set_option autoImplicit false
noncomputable section

open Complex Set MeasureTheory
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.ChebyshevBound.IntegratedFormula

def gammaMellinTerm (n : ℕ) (u : ℝ) : ℂ :=
  (powerCut 1 u - powerCut (2 * (n + 1)) u) /
    (2 * (n + 1) * (2 * (n + 1) - 1))

theorem hasMellin_gammaMellinTerm (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (gammaMellinTerm n) s
      ((1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + (s / 2 + 1))) / (2 * (s * (s + 1)))) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 := hasMellin_powerCut 1 (s := s) (by simp; linarith)
  have h2 := hasMellin_powerCut (2 * (n + 1)) (s := s) (by
    simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
      Complex.add_im, Complex.natCast_im, Complex.one_im]
    norm_num
    linarith)
  have hd := hasMellin_sub h1.1 h2.1
  refine ⟨hd.1.div_const _, ?_⟩
  unfold gammaMellinTerm
  rw [mellin_div_const, hd.2, h1.2, h2.2]
  have hne (z : ℂ) (hz : 0 < z.re) : z ≠ 0 := by intro he; simp [he] at hz
  have hsn : s + 2 * ((n : ℂ) + 1) ≠ 0 := hne _ (by simp; linarith)
  have hs0 : s ≠ 0 := hne _ (by linarith)
  have hs1 : s + 1 ≠ 0 := hne _ (by simp; linarith)
  have hn1 : (n : ℂ) + 1 ≠ 0 := hne _ (by simp; linarith)
  have hn2 : 2 * ((n : ℂ) + 1) - 1 ≠ 0 := hne _ (by simp; linarith)
  rw [show (n : ℂ) + (s / 2 + 1) = (s + 2 * ((n : ℂ) + 1)) / 2 by ring]
  field_simp
  ring

theorem gammaMellinTerm_norm_le (n : ℕ) {u : ℝ} (hu : 0 < u) :
    ‖gammaMellinTerm n u‖ ≤ (1 / ((n : ℝ) + 1) ^ 2) * ‖powerCut 0 u‖ := by
  by_cases hu1 : u ≤ 1
  · have hmem : u ∈ Ioc 0 1 := ⟨hu, hu1⟩
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm : 0 < (n : ℝ) + 1 := by positivity
    have hmn : 0 < 2 * ((n : ℝ) + 1) - 1 := by linarith
    have hd : 0 < 2 * ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) - 1) := by positivity
    have hnorm : ‖(u : ℂ) ^ (2 * ((n : ℂ) + 1))‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
      apply Real.rpow_le_one hu.le hu1
      simp
      positivity
    have hnum : ‖(u : ℂ) - (u : ℂ) ^ (2 * ((n : ℂ) + 1))‖ ≤ 2 := by
      have h := norm_sub_le (u : ℂ) ((u : ℂ) ^ (2 * ((n : ℂ) + 1)))
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu] at h
      linarith
    have hden : ‖2 * ((n : ℂ) + 1) * (2 * ((n : ℂ) + 1) - 1)‖ =
        2 * ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) - 1) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_ofNat,
        ← Complex.ofReal_add, ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    simp only [gammaMellinTerm, powerCut, indicator_of_mem hmem, Complex.cpow_one,
      Complex.cpow_zero, norm_one, mul_one, norm_div, hden]
    calc
      _ ≤ 2 / (2 * ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) - 1)) :=
        div_le_div_of_nonneg_right hnum hd.le
      _ ≤ _ := by
        apply (div_le_div_iff₀ hd (sq_pos_of_pos hm)).2
        nlinarith
  · have hn : u ∉ Ioc 0 1 := fun h => hu1 h.2
    simp [gammaMellinTerm, powerCut, hn]

theorem gammaMellin_weights_summable : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))

theorem gammaMellinTerm_summable {u : ℝ} (hu : 0 < u) :
    Summable (fun n => gammaMellinTerm n u) :=
  (gammaMellin_weights_summable.mul_right ‖powerCut 0 u‖).of_norm_bounded
    (fun n => gammaMellinTerm_norm_le n hu)

theorem hasMellin_gammaSum {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u => ∑' n, gammaMellinTerm n u) s
      ((digamma (s / 2 + 1) + Real.eulerMascheroniConstant) / (2 * (s * (s + 1)))) := by
  have h := hasMellin_tsum_dominated (fun n => hasMellin_gammaMellinTerm n hs)
    (hasMellin_powerCut 0 (s := s) (by simp; linarith)).1
    gammaMellin_weights_summable (fun n _ hu => gammaMellinTerm_norm_le n hu)
  have hpoles : ∀ n : ℕ, s / 2 + 1 ≠ -(n : ℂ) := by
    intro n he
    have hr := congrArg Complex.re he
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp at hr
    linarith
  have hg := (Complex.hasSum_digamma hpoles).div_const (2 * (s * (s + 1)))
  rw [hg.tsum_eq] at h
  exact h

def poleMellin (u : ℝ) : ℂ := (powerCut (-1) u - 2 * powerCut 0 u + powerCut 1 u) / 2

theorem hasMellin_poleMellin {s : ℂ} (hs : 1 < s.re) :
    HasMellin poleMellin s ((1 / (s - 1)) / (s * (s + 1))) := by
  have hm := hasMellin_powerCut (-1) (s := s) (by simp; linarith)
  have h0 := hasMellin_powerCut 0 (s := s) (by simp; linarith)
  have h1 := hasMellin_powerCut 1 (s := s) (by simp; linarith)
  have htwo := hasMellin_const_smul h0.1 (2 : ℂ)
  have hsub := hasMellin_sub hm.1 htwo.1
  have hadd := hasMellin_add hsub.1 h1.1
  refine ⟨hadd.1.div_const _, ?_⟩
  change mellin (fun u => (powerCut (-1) u - (2 : ℂ) • powerCut 0 u + powerCut 1 u) / 2) s = _
  rw [mellin_div_const, hadd.2, hsub.2, htwo.2, hm.2, h0.2, h1.2, smul_eq_mul]
  have hne (z : ℂ) (hz : 0 < z.re) : z ≠ 0 := by intro he; simp [he] at hz
  have hs0 : s ≠ 0 := hne _ (by linarith)
  have hs1 : s + 1 ≠ 0 := hne _ (by simp; linarith)
  have hsm : s - 1 ≠ 0 := hne _ (by simp; linarith)
  simp only [add_zero, ← sub_eq_add_neg]
  field_simp
  ring

end LiuWang.Proof.ChebyshevBound.IntegratedFormula
