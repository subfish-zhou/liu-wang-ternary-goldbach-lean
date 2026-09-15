import LiuWang.Proof.ZeroRegionFamily.Stechkin
import Mathlib.Analysis.SumIntegralComparisons

/-! # 基准线Re z=1的真实digamma对数界 -/

set_option autoImplicit false
noncomputable section

open Complex Finset Filter MeasureTheory
open scoped Topology

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

def referenceTerm (y x : ℝ) : ℝ := y^2/(x*(x^2+y^2))

theorem referenceTerm_antitone (y : ℝ) :
    AntitoneOn (referenceTerm y) (Set.Ici 1) := by
  intro a ha b hb hab
  change 1 ≤ a at ha
  change 1 ≤ b at hb
  have haa : 0 ≤ a := by linarith
  have hbb : 0 ≤ b := by linarith
  dsimp [referenceTerm]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  gcongr

theorem referenceTerm_integral (y : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in (1 : ℝ)..b, referenceTerm y x) =
      Real.log b-Real.log (b^2+y^2)/2+Real.log (1+y^2)/2 := by
  have hd (x : ℝ) (hx : x ∈ Set.uIcc (1 : ℝ) b) :
      HasDerivAt (fun u : ℝ => Real.log u-Real.log (u^2+y^2)/2) (referenceTerm y x) x := by
    have hx1 : 1 ≤ x := (Set.uIcc_of_le hb ▸ hx).1
    have hx0 : x ≠ 0 := by linarith
    have hxy : x^2+y^2 ≠ 0 := ne_of_gt (by positivity)
    have h := (Real.hasDerivAt_log hx0).sub
      (((hasDerivAt_pow 2 x).add_const (y^2)).log hxy |>.div_const 2)
    apply h.congr_deriv
    simp only [referenceTerm]
    field_simp
    ring
  have hi : IntervalIntegrable (referenceTerm y) volume 1 b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div
      (continuousOn_id.mul ((continuousOn_id.pow 2).add continuousOn_const))
    intro x hx
    have hx1 : 1 ≤ x := (Set.uIcc_of_le hb ▸ hx).1
    have hxpos : 0 < x := by linarith
    exact mul_ne_zero hxpos.ne' (ne_of_gt (add_pos_of_pos_of_nonneg
      (sq_pos_of_pos hxpos) (sq_nonneg y)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp

theorem reference_sum_le (y : ℝ) (n : ℕ) :
    ∑ j ∈ range n, referenceTerm y ((j : ℝ)+1) ≤
      y^2/(1+y^2)+Real.log (1+y^2)/2 := by
  cases n with
  | zero =>
    simp only [sum_range_zero]
    exact add_nonneg (by positivity) (div_nonneg
      (Real.log_nonneg (by linarith [sq_nonneg y])) (by norm_num))
  | succ n =>
    rw [sum_range_succ']
    have hanti := (referenceTerm_antitone y).mono
      (show Set.Icc (1 : ℝ) (1+n) ⊆ Set.Ici 1 from fun _ h => h.1)
    have hi := hanti.sum_le_integral
    have he := referenceTerm_integral y (b := 1+n) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hlog : Real.log (1+(n : ℝ))-Real.log ((1+(n : ℝ))^2+y^2)/2 ≤ 0 := by
      have h := Real.log_le_log (show 0 < (1+(n : ℝ))^2 by positivity)
        (show (1+(n : ℝ))^2 ≤ (1+(n : ℝ))^2+y^2 by linarith [sq_nonneg y])
      rw [Real.log_pow] at h
      norm_num at h
      linarith
    rw [he] at hi
    have hid : (∑ x ∈ range n, referenceTerm y ((↑(x+1) : ℝ)+1)) =
        ∑ x ∈ range n, referenceTerm y (1+↑(x+1)) := by
      apply sum_congr rfl
      intro j _
      congr 1
      ring
    rw [hid]
    rw [show referenceTerm y ((↑(0 : ℕ) : ℝ)+1)=y^2/(1+y^2) by norm_num [referenceTerm]]
    linarith

theorem digamma_one_re_bound (y : ℝ) :
    (Complex.digamma (1+Complex.I*y)).re ≤
      -Real.eulerMascheroniConstant+y^2/(1+y^2)+Real.log (1+y^2)/2 := by
  have hp : ∀ n : ℕ, (1+Complex.I*(y : ℂ)) ≠ -(n : ℂ) := by
    intro n hn
    have h := congrArg Complex.re hn
    norm_num [Complex.mul_re] at h
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hh := Complex.hasSum_re (Complex.hasSum_digamma hp)
  have hterm (n : ℕ) :
      (1/((n : ℂ)+1)-1/((n : ℂ)+(1+Complex.I*y))).re =
        referenceTerm y ((n : ℝ)+1) := by
    have hn : 0 < (n : ℝ)+1 := by positivity
    simp [referenceTerm, one_div, Complex.inv_re, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im]
    field_simp
    ring
  simp_rw [hterm] at hh
  have hle := le_of_tendsto hh.tendsto_sum_nat
    (Filter.Eventually.of_forall (reference_sum_le y))
  simp only [Complex.add_re, Complex.ofReal_re] at hle
  linarith

theorem reference_shape_le {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 4) :
    Real.log (1+v)/2+1/(1+v) ≤ 7/6 := by
  by_cases hsmall : v ≤ 1
  · have hl := Real.log_le_sub_one_of_pos (show 0 < 1+v by linarith [hv.1])
    have hinv : 1/(1+v) ≤ 1-v/2 := by
      apply (div_le_iff₀ (by linarith [hv.1])).mpr
      nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hsmall)]
    linarith
  · have hlarge : 1 ≤ v := le_of_not_ge hsmall
    have hl := Real.log_le_sub_one_of_pos (show 0 < (1+v)/4 by linarith)
    rw [Real.log_div (by linarith : 1+v ≠ 0) (by norm_num)] at hl
    have hl4 : Real.log 4 ≤ 7/5 := by
      have h2 := Real.log_two_lt_d9
      rw [show (4 : ℝ)=2^2 by norm_num, Real.log_pow]
      norm_num
      linarith
    have hinv : 1/(1+v) ≤ (7-v)/12 := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith [mul_nonneg (show 0 ≤ v-1 by linarith) (show 0 ≤ 5-v by linarith [hv.2])]
    linarith [hv.2]

theorem digamma_one_re_le_log_max (y : ℝ) :
    (Complex.digamma (1+Complex.I*y)).re ≤ Real.log (max 1 (2*|y|)) := by
  have hb := digamma_one_re_bound y
  have hg := Real.one_half_lt_eulerMascheroniConstant
  by_cases hy : |y| ≤ 1/2
  · have hprod := mul_nonneg (abs_nonneg y) (show 0 ≤ 1/2-|y| by linarith)
    have hy2 : y^2 ≤ 1/4 := by nlinarith [sq_abs y, abs_nonneg y]
    have hl := Real.log_le_sub_one_of_pos (show 0 < 1+y^2 by positivity)
    have hf : y^2/(1+y^2) ≤ 1/4 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    rw [max_eq_left (by linarith), Real.log_one]
    linarith
  · have hyp : 0 < |y| := by linarith
    have hy2 : 0 < y^2 := by nlinarith [sq_abs y]
    have hyne : y ≠ 0 := by intro he; simp [he] at hyp
    have hv : 1/y^2 ∈ Set.Icc (0 : ℝ) 4 := by
      constructor
      · positivity
      · apply (div_le_iff₀ hy2).mpr
        nlinarith [sq_abs y]
    have hh := reference_shape_le hv
    have heq : Real.log (1+y^2)/2 =
        Real.log |y|+Real.log (1+1/y^2)/2 := by
      have h : 1+y^2 = |y|^2*(1+1/y^2) := by rw [sq_abs]; field_simp [hyne]; ring
      rw [h, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      ring
    have hfrac : y^2/(1+y^2)=1/(1+1/y^2) := by field_simp [hyne]; ring
    rw [heq, hfrac] at hb
    rw [max_eq_right (by linarith), Real.log_mul (by norm_num) hyp.ne']
    linarith [ChebyshevBound.HighHeight.log_two_ge_two_thirds]

end LiuWang.Proof.ZeroRegionFamily.Sharp
