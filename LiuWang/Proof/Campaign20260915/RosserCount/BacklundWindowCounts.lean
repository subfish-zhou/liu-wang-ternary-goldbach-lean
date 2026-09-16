import LiuWang.Proof.Campaign20260915.RosserCount.BacklundGammaDifference
import LiuWang.Proof.Campaign20260915.RosserCount.BacklundVariation

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex Metric MeasureTheory MeromorphicOn

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

theorem backlundLog_continuousOn_reflected {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    ContinuousOn (backlundLog T) (Set.Icc (-1 / 4 : ℝ) 2) := by
  have hi := zeta_logDeriv_horizontal_integrable (a := -1 / 4) (b := 2) hT.ne'
    (fun x hx => zeta_horizontal_regular_above_minus_two hT hr (by
      rw [Set.uIcc_of_le (by norm_num)] at hx
      linarith [hx.1]))
  have hc := intervalIntegral.continuousOn_primitive_interval' hi
    (show (2 : ℝ) ∈ Set.uIcc (-1 / 4 : ℝ) 2 from Set.right_mem_uIcc)
  have hh := (continuousOn_const (c := Complex.log (riemannZeta (horizontalAt T 2)))).add hc
  rw [Set.uIcc_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 2)] at hh
  convert! hh using 1
  funext x
  unfold backlundLog HIntegral
  dsimp only [Pi.add_apply, horizontalAt]
  rw [intervalIntegral.integral_symm 2 x]
  ring

theorem exp_backlundLog_reflected {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 / 4 : ℝ) 2) :
    Complex.exp (backlundLog T x) = riemannZeta (horizontalAt T x) := by
  have ha (u : ℝ) : AnalyticAt ℂ riemannZeta (horizontalAt T u) := by
    apply LiuWang.Proof.PrincipalPsi.analytic_zeta_of_ne_one
    intro he
    exact hT.ne' (by simpa [horizontalAt] using congrArg Complex.im he)
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
    exact zeta_horizontal_regular_above_minus_two hT hr (by linarith [hx.1, hu.1])
  have he := Argument.exp_integral_logarithmic_derivative hd hc hz
  change Complex.exp (HIntegral (logDeriv riemannZeta) x 2 T) *
    riemannZeta (horizontalAt T x) = riemannZeta (horizontalAt T 2) at he
  rw [backlundLog, Complex.exp_sub,
    Complex.exp_log (zeta_horizontal_regular hT hr (by norm_num : (1 / 2 : ℝ) ≤ 2)),
    ← he]
  field_simp

theorem backlundAux_phase_formula_reflected {T : ℝ} (hT : 0 < T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 / 4 : ℝ) 2) (n : ℕ) :
    backlundAux T n ((x - 5 / 4 : ℝ) : ℂ) =
      ((Real.exp ((n : ℝ) * (backlundLog T x).re) *
        Real.cos ((n : ℝ) * (backlundLog T x).im) : ℝ) : ℂ) := by
  rw [backlundAux_real_line, ← exp_backlundLog_reflected hT hr hx, ← Complex.exp_nat_mul]
  simp only [Complex.exp_re, mul_re, mul_im, natCast_re, natCast_im,
    zero_mul, sub_zero, add_zero]

def backlundDiskSupport (T : ℝ) (n : ℕ) : Finset ℂ :=
  ((divisor (backlundAux T n) (closedBall 0 (33 / 25 : ℝ))).finiteSupport
    (isCompact_closedBall (0 : ℂ) (33 / 25 : ℝ))).toFinset

def backlundWindowSupport (T : ℝ) (n : ℕ) (a b : ℝ) : Finset ℂ :=
  (backlundDiskSupport T n).filter
    (fun z => z.im = 0 ∧ z.re ∈ Set.Icc (a - 5 / 4) (b - 5 / 4))

theorem backlundAux_disk_divisor_pos_of_zero {T : ℝ} (hT : rsA ≤ T) {n : ℕ}
    (hn : backlundAux T n 0 ≠ 0) {z : ℂ}
    (hz : z ∈ closedBall 0 (33 / 25 : ℝ)) (hzero : backlundAux T n z = 0) :
    0 < divisor (backlundAux T n) (closedBall 0 (33 / 25 : ℝ)) z := by
  have ha := backlundAux_analyticOnNhd hT n
  have h0 : (0 : ℂ) ∈ closedBall 0 (33 / 25 : ℝ) := by norm_num
  have hfinite := ha.analyticOrderAt_ne_top_of_isPreconnected
    (convex_closedBall (0 : ℂ) (33 / 25 : ℝ)).isPreconnected h0 hz
    (by rw [(ha 0 h0).analyticOrderAt_eq_zero.mpr hn]; simp)
  have hnat : 0 < analyticOrderNatAt (backlundAux T n) z := by
    apply Nat.pos_of_ne_zero
    intro he
    have ho : analyticOrderAt (backlundAux T n) z = 0 := by
      rw [← Nat.cast_analyticOrderNatAt hfinite, he, Nat.cast_zero]
    exact ((ha z hz).analyticOrderAt_eq_zero.mp ho) hzero
  rw [ha.divisor_apply hz, ← Nat.cast_analyticOrderNatAt hfinite]
  simpa using (show (0 : ℤ) < (analyticOrderNatAt (backlundAux T n) z : ℤ) by
    exact_mod_cast hnat)

theorem backlund_window_phase_variation {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {n : ℕ} (hn : backlundAux T n 0 ≠ 0)
    {a b : ℝ} (ha : -7 / 100 ≤ a) (hab : a ≤ b) (hb : b ≤ 5 / 4) :
    (n : ℝ) * |(backlundLog T b).im - (backlundLog T a).im| ≤
      ((backlundWindowSupport T n a b).card + 1 : ℝ) * Real.pi := by
  classical
  have hpos : 0 < T := by linarith [rsA_ge_thousand]
  let A : ℝ → ℝ := fun t => (n : ℝ) * (backlundLog T (t + 5 / 4)).im
  have hc : ContinuousOn A (Set.Icc (a - 5 / 4) (b - 5 / 4)) := by
    apply continuousOn_const.mul
    apply Complex.continuous_im.comp_continuousOn
    apply (backlundLog_continuousOn_reflected hpos hr).comp (by fun_prop)
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hS : ∀ t ∈ Set.Icc (a - 5 / 4) (b - 5 / 4), Real.cos (A t) = 0 →
      (t : ℂ) ∈ backlundWindowSupport T n a b := by
    intro t ht hc0
    change Real.cos ((n : ℝ) * (backlundLog T (t + 5 / 4)).im) = 0 at hc0
    have hx : t + 5 / 4 ∈ Set.Icc (-1 / 4 : ℝ) 2 := by
      constructor <;> linarith [ht.1, ht.2]
    have he := backlundAux_phase_formula_reflected hpos hr hx n
    have hz : backlundAux T n (t : ℂ) = 0 := by
      simpa only [add_sub_cancel_right, hc0, mul_zero, ofReal_zero] using he
    have hball : (t : ℂ) ∈ closedBall 0 (33 / 25 : ℝ) := by
      simp only [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos (by linarith [ht.2] : t ≤ 0)]
      linarith [ht.1]
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · apply ((divisor (backlundAux T n) (closedBall 0 (33 / 25 : ℝ))).finiteSupport
        (isCompact_closedBall ..)).mem_toFinset.mpr
      exact (backlundAux_disk_divisor_pos_of_zero hT hn hball hz).ne'
    · simpa only [ofReal_im, ofReal_re, true_and] using ht
  have hv := argument_variation_le (by linarith : a - 5 / 4 ≤ b - 5 / 4) hc
    (backlundWindowSupport T n a b) hS
  have he : A (b - 5 / 4) - A (a - 5 / 4) =
      (n : ℝ) * ((backlundLog T b).im - (backlundLog T a).im) := by
    dsimp [A]
    rw [sub_add_cancel, sub_add_cancel]
    ring
  rwa [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at hv

theorem backlund_reflected_window_count_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {n : ℕ} (hn : backlundAux T n 0 ≠ 0) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (57 / 100)) :
    (n : ℝ) * |(backlundLog T (5 / 4)).im - (backlundLog T (1 / 2)).im| ≤
      ((backlundWindowSupport T n (1 / 2 + u) (5 / 4)).card +
        (backlundWindowSupport T n (1 / 2 - u) (1 / 2)).card + 2 : ℝ) * Real.pi +
          4 * (n : ℝ) / T := by
  have hpos : 0 < T := by linarith [rsA_ge_thousand]
  have hR := backlund_window_phase_variation hT hr hn
    (by linarith [hu.1] : -7 / 100 ≤ 1 / 2 + u)
    (by linarith [hu.2] : 1 / 2 + u ≤ 5 / 4) le_rfl
  have hL := backlund_window_phase_variation hT hr hn
    (by linarith [hu.2] : -7 / 100 ≤ 1 / 2 - u)
    (by linarith [hu.1] : 1 / 2 - u ≤ 1 / 2) (by norm_num)
  have he := backlundLog_reflection_defect_lt_four_div
    (by linarith [rsA_ge_thousand] : 1 ≤ T) hr
    (show u ∈ Set.Icc (0 : ℝ) (3 / 4) from ⟨hu.1, by linarith [hu.2]⟩)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsum :
      (backlundLog T (5 / 4)).im - (backlundLog T (1 / 2)).im =
      ((backlundLog T (5 / 4)).im - (backlundLog T (1 / 2 + u)).im) +
      ((backlundLog T (1 / 2)).im - (backlundLog T (1 / 2 - u)).im) +
      (((backlundLog T (1 / 2 + u)).im - (backlundLog T (1 / 2)).im) +
      ((backlundLog T (1 / 2 - u)).im - (backlundLog T (1 / 2)).im)) := by ring
  have htri := abs_add_le
    (((backlundLog T (5 / 4)).im - (backlundLog T (1 / 2 + u)).im) +
      ((backlundLog T (1 / 2)).im - (backlundLog T (1 / 2 - u)).im))
    (((backlundLog T (1 / 2 + u)).im - (backlundLog T (1 / 2)).im) +
      ((backlundLog T (1 / 2 - u)).im - (backlundLog T (1 / 2)).im))
  rw [← hsum] at htri
  have htri2 := abs_add_le
    ((backlundLog T (5 / 4)).im - (backlundLog T (1 / 2 + u)).im)
    ((backlundLog T (1 / 2)).im - (backlundLog T (1 / 2 - u)).im)
  have hscaled := mul_le_mul_of_nonneg_left
    (htri.trans (add_le_add htri2 le_rfl)) hn0
  have herr := mul_le_mul_of_nonneg_left he.le hn0
  have hnorm : (n : ℝ) * (4 / T) = 4 * (n : ℝ) / T := by ring
  rw [hnorm] at herr
  nlinarith only [hscaled, herr, hR, hL]

#print axioms backlundLog_continuousOn_reflected
#print axioms exp_backlundLog_reflected
#print axioms backlundAux_phase_formula_reflected
#print axioms backlundAux_disk_divisor_pos_of_zero
#print axioms backlund_window_phase_variation
#print axioms backlund_reflected_window_count_bound

end LiuWang.Proof.Campaign20260915.RosserCount
