import LiuWang.Proof.Campaign20260915.RosserCount.BacklundEnvelope
import LiuWang.Proof.Campaign20260915.RosserCount.RosserPhase
import LiuWang.Proof.DirichletZeroCount.Argument.Variation

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.DirichletZeroCount

def backlundLog (T x : ℝ) : ℂ :=
  Complex.log (riemannZeta (horizontalAt T 2)) -
    HIntegral (logDeriv riemannZeta) x 2 T

theorem backlundLog_continuousOn {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    ContinuousOn (backlundLog T) (Set.Icc (1 / 2 : ℝ) 2) := by
  have hi := zeta_logDeriv_horizontal_integrable (a := 1 / 2) (b := 2) hT.ne'
    (fun x hx => zeta_horizontal_regular hT hr (by
      rw [Set.uIcc_of_le (by norm_num)] at hx
      exact hx.1))
  have hc := intervalIntegral.continuousOn_primitive_interval' hi
    (show (2 : ℝ) ∈ Set.uIcc (1 / 2 : ℝ) 2 from Set.right_mem_uIcc)
  have hh := (continuousOn_const (c := Complex.log (riemannZeta (horizontalAt T 2)))).add hc
  rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hh
  convert! hh using 1
  funext x
  unfold backlundLog HIntegral
  dsimp only [Pi.add_apply, horizontalAt]
  rw [intervalIntegral.integral_symm 2 x]
  ring

theorem exp_backlundLog {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
    Complex.exp (backlundLog T x) = riemannZeta (horizontalAt T x) := by
  have ha (u : ℝ) : AnalyticAt ℂ riemannZeta (horizontalAt T u) := by
    apply LiuWang.Proof.PrincipalPsi.analytic_zeta_of_ne_one
    intro he
    have hh : T = 0 := by simpa [horizontalAt] using congrArg Complex.im he
    exact hT.ne' hh
  have hd (u : ℝ) :
      HasDerivAt (fun v => riemannZeta (horizontalAt T v))
        (deriv riemannZeta (horizontalAt T u)) u := by
    simpa [horizontalAt, Function.comp_def, smul_eq_mul] using
      (ha u).differentiableAt.hasDerivAt.scomp u
        ((Complex.ofRealCLM.hasDerivAt (x := u)).add_const ((T : ℂ) * I))
  have hc : Continuous (fun u => deriv riemannZeta (horizontalAt T u)) :=
    continuous_iff_continuousAt.mpr fun u =>
      (ha u).deriv.continuousAt.comp (f := horizontalAt T) (by unfold horizontalAt; fun_prop)
  have hz : ∀ u ∈ Set.uIcc x 2, riemannZeta (horizontalAt T u) ≠ 0 := by
    intro u hu
    rw [Set.uIcc_of_le hx.2] at hu
    exact zeta_horizontal_regular hT hr (hx.1.trans hu.1)
  have he := Argument.exp_integral_logarithmic_derivative hd hc hz
  change Complex.exp (HIntegral (logDeriv riemannZeta) x 2 T) *
    riemannZeta (horizontalAt T x) = riemannZeta (horizontalAt T 2) at he
  rw [backlundLog, Complex.exp_sub,
    Complex.exp_log (zeta_horizontal_regular hT hr (by norm_num : (1 / 2 : ℝ) ≤ 2)),
    ← he]
  field_simp

theorem backlundAux_real_line (T x : ℝ) (n : ℕ) :
    backlundAux T n ((x - 5 / 4 : ℝ) : ℂ) =
      ((riemannZeta (horizontalAt T x) ^ n).re : ℂ) := by
  have hp : ((x - 5 / 4 : ℝ) : ℂ) + 5 / 4 + (T : ℂ) * I = horizontalAt T x := by
    unfold horizontalAt
    push_cast
    ring
  have hm : ((x - 5 / 4 : ℝ) : ℂ) + 5 / 4 - (T : ℂ) * I =
      conj (horizontalAt T x) := by
    simp only [horizontalAt, map_add, map_mul, conj_ofReal, conj_I]
    push_cast
    ring
  rw [backlundAux, hp, hm, riemannZeta_conj, ← map_pow]
  apply Complex.ext <;> simp [-map_pow]

theorem backlundAux_phase_formula {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) (n : ℕ) :
    backlundAux T n ((x - 5 / 4 : ℝ) : ℂ) =
      ((Real.exp ((n : ℝ) * (backlundLog T x).re) *
        Real.cos ((n : ℝ) * (backlundLog T x).im) : ℝ) : ℂ) := by
  rw [backlundAux_real_line, ← exp_backlundLog hT hr hx, ← Complex.exp_nat_mul]
  simp only [Complex.exp_re, mul_re, mul_im, natCast_re, natCast_im,
    zero_mul, sub_zero, add_zero]

theorem backlundAux_zero_iff_phase {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) (n : ℕ) :
    backlundAux T n ((x - 5 / 4 : ℝ) : ℂ) = 0 ↔
      ∃ k : ℤ, (n : ℝ) * (backlundLog T x).im = (2 * (k : ℝ) + 1) * Real.pi / 2 := by
  rw [backlundAux_phase_formula hT hr hx n]
  simp only [ofReal_eq_zero, mul_eq_zero, Real.exp_ne_zero, false_or, Real.cos_eq_zero_iff]

theorem positiveCount_error_backlundLog {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    Real.pi * ((positiveCount T : ℝ) - rosserMain T) =
      rosserGammaRemainder T + (backlundLog T (1 / 2)).im :=
  positiveCount_error_horizontal_phase hT hr

theorem backlund_phase_level_has_root {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    (n : ℕ) (k : ℤ)
    (hk : (2 * (k : ℝ) + 1) * Real.pi / 2 ∈
      Set.uIcc ((n : ℝ) * (backlundLog T (1 / 2)).im)
        ((n : ℝ) * (backlundLog T (5 / 4)).im)) :
    ∃ x ∈ Set.Icc (1 / 2 : ℝ) (5 / 4),
      backlundAux T n ((x - 5 / 4 : ℝ) : ℂ) = 0 ∧
        (n : ℝ) * (backlundLog T x).im = (2 * (k : ℝ) + 1) * Real.pi / 2 := by
  have hc : ContinuousOn (fun x => (n : ℝ) * (backlundLog T x).im)
      (Set.uIcc (1 / 2 : ℝ) (5 / 4)) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply continuousOn_const.mul
    exact Complex.continuous_im.comp_continuousOn
      ((backlundLog_continuousOn hT hr).mono (by
        intro x hx
        exact ⟨hx.1, hx.2.trans (by norm_num)⟩))
  obtain ⟨x, hx, he⟩ := intermediate_value_uIcc hc hk
  rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)] at hx
  exact ⟨x, hx,
    (backlundAux_zero_iff_phase hT hr ⟨hx.1, hx.2.trans (by norm_num)⟩ n).mpr ⟨k, he⟩,
    he⟩

#print axioms backlundLog_continuousOn
#print axioms exp_backlundLog
#print axioms backlundAux_real_line
#print axioms backlundAux_phase_formula
#print axioms backlundAux_zero_iff_phase
#print axioms positiveCount_error_backlundLog
#print axioms backlund_phase_level_has_root

end LiuWang.Proof.Campaign20260915.RosserCount
