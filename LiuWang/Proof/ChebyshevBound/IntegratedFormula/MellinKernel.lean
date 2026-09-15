import LiuWang.Proof.ChebyshevBound.HighHeight.IntegratedPsi
import Mathlib.Analysis.MellinInversion

/-!
# 二次 Perron 核的 Mellin 原像

零点项带 x=1 的常数校正，因此不拆开不可绝对求和的 1/rho 项。
-/

set_option autoImplicit false
noncomputable section

open Complex Set MeasureTheory
open LiuWang.Proof.ChebyshevBound.HighHeight
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ChebyshevBound.IntegratedFormula

def powerCut (a : ℂ) : ℝ → ℂ := (Ioc 0 1).indicator (fun u => (u : ℂ) ^ a)

theorem hasMellin_powerCut (a : ℂ) {s : ℂ} (hs : 0 < s.re + a.re) :
    HasMellin (powerCut a) s (1 / (s + a)) :=
  hasMellin_cpow_Ioc a hs

def triangle (u : ℝ) : ℂ := powerCut 0 u - powerCut 1 u

theorem triangle_of_pos {u : ℝ} (hu : 0 < u) :
    triangle u = (max 0 (1 - u) : ℝ) := by
  by_cases h : u ≤ 1
  · simp [triangle, powerCut, hu, h]
  · simp [triangle, powerCut, h, max_eq_left (by linarith : 1 - u ≤ 0)]

theorem hasMellin_triangle {s : ℂ} (hs : 0 < s.re) :
    HasMellin triangle s (1 / (s * (s + 1))) := by
  have h0 := hasMellin_powerCut 0 (s := s) (by simpa using hs)
  have h1 := hasMellin_powerCut 1 (s := s) (by simp; linarith)
  have h := hasMellin_sub h0.1 h1.1
  rw [h0.2, h1.2] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hs1 : s + 1 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith
  simp only [add_zero]
  field_simp
  ring

theorem continuousAt_triangle {u : ℝ} (hu : 0 < u) : ContinuousAt triangle u := by
  have hcont : ContinuousAt (fun u : ℝ => ((max 0 (1 - u) : ℝ) : ℂ)) u := by fun_prop
  apply hcont.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu] with v hv
  exact triangle_of_pos hv

def zeroMellinTerm (p : RiemannXiDivisorZeroIndex) (u : ℝ) : ℂ :=
  (powerCut (-riemannXiDivisorZeroValue p) u - powerCut 1 u) /
    (riemannXiDivisorZeroValue p * (riemannXiDivisorZeroValue p + 1))

theorem hasMellin_zeroMellinTerm (p : RiemannXiDivisorZeroIndex)
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (zeroMellinTerm p) s (xiTerm s p / (s * (s + 1))) := by
  let ρ := riemannXiDivisorZeroValue p
  have hr := riemannXiDivisorZeroValue_re_mem_Ioo p
  have h0 := hasMellin_powerCut (-ρ) (s := s) (by
    simp only [Complex.neg_re]; dsimp [ρ]; linarith [hr.2])
  have h1 := hasMellin_powerCut 1 (s := s) (by simp; linarith)
  have hsub := hasMellin_sub h0.1 h1.1
  refine ⟨hsub.1.div_const _, ?_⟩
  unfold zeroMellinTerm
  rw [mellin_div_const, hsub.2, h0.2, h1.2]
  have hρ : ρ ≠ 0 := by
    intro he
    have hr0 : 0 < ρ.re := hr.1
    simp [he] at hr0
  have hρ1 : ρ + 1 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp at h
    have : 0 < ρ.re := hr.1
    linarith
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hs1 : s + 1 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp at h
    linarith
  have hsr : s - ρ ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp at h
    have : ρ.re < 1 := hr.2
    linarith
  change (1 / (s + -ρ) - 1 / (s + 1)) / (ρ * (ρ + 1)) =
    (1 / (s - ρ) + 1 / ρ) / (s * (s + 1))
  rw [← sub_eq_add_neg]
  field_simp
  ring

theorem zeroMellinTerm_at_inverse {x : ℝ} (hx : 1 ≤ x)
    (p : RiemannXiDivisorZeroIndex) :
    zeroMellinTerm p x⁻¹ =
      (integratedZeroTerm x p - integratedZeroTerm 1 p) / (x : ℂ) := by
  have hx0 : 0 < x := by linarith
  have hu : x⁻¹ ∈ Ioc 0 1 := ⟨inv_pos.mpr hx0, inv_le_one_of_one_le₀ hx⟩
  have hne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  simp only [zeroMellinTerm, powerCut, indicator_of_mem hu, integratedZeroTerm,
    Complex.ofReal_one, one_cpow, Complex.cpow_one, Complex.ofReal_inv]
  rw [Complex.inv_cpow_ofReal_nonneg hx0.le, Complex.cpow_neg, inv_inv,
    Complex.cpow_add _ _ hne, Complex.cpow_one]
  field_simp

end LiuWang.Proof.ChebyshevBound.IntegratedFormula
