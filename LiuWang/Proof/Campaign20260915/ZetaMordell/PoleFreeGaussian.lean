import LiuWang.Proof.Campaign20260915.ZetaMordell.ContourVertical
import LiuWang.Proof.Campaign20260915.ZetaMordell.CorrectionPolynomials

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter Set
open scoped Real Topology

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

def poleFreeRotor : ℂ := (-1 + I) / 4

def poleFreePoint (w : ℂ) : ℂ := 1 / 2 + poleFreeRotor * w

def poleFreeKernel (n : ℕ) (b w : ℂ) : ℂ :=
  (poleFreePoint w - b) ^ n * poleFreeRotor *
    exp (Real.pi * I * (poleFreePoint w ^ 2 - 2 * (poleFreePoint w - b) ^ 2 + 1 / 8)) /
      (exp (2 * Real.pi * I * poleFreePoint w) - 1)

theorem poleFree_denominator_ne_zero {w : ℂ} (hw : |w.im| < 1) :
    exp (2 * Real.pi * I * poleFreePoint w) - 1 ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (sub_eq_zero.mp h)
  have hx : poleFreePoint w = (n : ℂ) := by
    apply mul_left_cancel₀ mordellFrequency_ne_zero
    convert hn using 1
    ring
  have hr := congrArg Complex.re hx
  have hi := congrArg Complex.im hx
  simp [poleFreePoint, poleFreeRotor, mul_re, mul_im] at hr hi
  have hwi := abs_lt.mp hw
  have hnR : (0 : ℝ) < n ∧ (n : ℝ) < 1 := by constructor <;> linarith
  have hnZ : (0 : ℤ) < n ∧ n < 1 := by exact_mod_cast hnR
  omega

theorem poleFreeKernel_analytic (n : ℕ) (b : ℂ) {w : ℂ} (hw : |w.im| < 1) :
    AnalyticAt ℂ (poleFreeKernel n b) w := by
  unfold poleFreeKernel
  apply AnalyticAt.div
  · unfold poleFreePoint
    fun_prop
  · unfold poleFreePoint
    fun_prop
  · exact poleFree_denominator_ne_zero hw

theorem poleFreeKernel_horizontal_continuous (n : ℕ) (b : ℂ) {y : ℝ} (hy : |y| < 1) :
    Continuous (fun t : ℝ => poleFreeKernel n b ((t : ℂ) + y * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (poleFreeKernel_analytic n b (by simpa using hy)).continuousAt.comp (by fun_prop)

theorem poleFree_denominator_tail {T y : ℝ} (hT : 3 ≤ |T|) (hy : |y| ≤ 1) :
    ‖(exp (2 * Real.pi * I * poleFreePoint ((T : ℂ) + y * I)) - 1)⁻¹‖ ≤ 2 := by
  have heq : ‖exp (2 * Real.pi * I * poleFreePoint ((T : ℂ) + y * I))‖ =
      Real.exp (-Real.pi / 2 * (T - y)) := by
    rw [norm_exp]
    congr 1
    simp [poleFreePoint, poleFreeRotor, mul_re, mul_im]
    ring
  have hlow : 1 / 2 ≤ ‖exp (2 * Real.pi * I *
      poleFreePoint ((T : ℂ) + y * I)) - 1‖ := by
    rcases le_abs.mp hT with hp | hn
    · have he : 2 ≤ Real.exp (Real.pi / 2 * (T - y)) := by
        have := Real.add_one_le_exp (Real.pi / 2 * (T - y))
        have := abs_le.mp hy
        nlinarith [Real.two_le_pi]
      have hi : Real.exp (-Real.pi / 2 * (T - y)) ≤ 1 / 2 := by
        rw [show -Real.pi / 2 * (T - y) = -(Real.pi / 2 * (T - y)) by ring, Real.exp_neg]
        exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 2)).mpr
          (by norm_num; exact he)
      have h := norm_sub_norm_le (1 : ℂ)
        (exp (2 * Real.pi * I * poleFreePoint ((T : ℂ) + y * I)))
      rw [norm_one, heq, norm_sub_rev] at h
      linarith
    · have he := Real.add_one_le_exp (-Real.pi / 2 * (T - y))
      have h := norm_sub_norm_le
        (exp (2 * Real.pi * I * poleFreePoint ((T : ℂ) + y * I))) (1 : ℂ)
      rw [heq, norm_one] at h
      have := abs_le.mp hy
      nlinarith [Real.two_le_pi]
  rw [norm_inv]
  exact (inv_le_comm₀ (lt_of_lt_of_le (by norm_num) hlow) (by norm_num : (0 : ℝ) < 2)).mpr
    (by norm_num; exact hlow)

theorem poleFree_gaussian_factor (b w : ℂ) :
    exp (Real.pi * I * (poleFreePoint w ^ 2 - 2 * (poleFreePoint w - b) ^ 2 + 1 / 8)) =
      exp (Real.pi * I * (-1 / 8 + 2 * b - 2 * b ^ 2)) *
        exp (Real.pi * I * (mordellRotor * w) ^ 2 +
          2 * Real.pi * I * (I * (2 * b - 1 / 2)) * (mordellRotor * w)) := by
  rw [← exp_add]
  congr 1
  unfold poleFreePoint poleFreeRotor mordellRotor
  ring_nf
  simp only [I_sq, I_pow_three]
  ring

theorem poleFreeKernel_tail_bound (n : ℕ) (b : ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T y : ℝ, 3 ≤ |T| → |y| ≤ 1 →
      ‖poleFreeKernel n b ((T : ℂ) + y * I)‖ ≤ B * Real.exp (-Real.pi / 32 * T ^ 2) := by
  let a := I * (2 * b - 1 / 2)
  let D := (Real.pi * I * (-1 / 8 + 2 * b - 2 * b ^ 2)).re
  let E := 2 * ‖mordellLinearCoeff a‖ ^ 2 + ‖mordellLinearCoeff a‖ + Real.pi / 8
  refine ⟨(n.factorial : ℝ) * 2 * Real.exp (6 + ‖b‖ + D + E), by positivity, ?_⟩
  intro T y hT hy
  have hr : ‖poleFreeRotor‖ ≤ 1 := by
    have h := norm_add_le (-1 : ℂ) I
    norm_num [poleFreeRotor, norm_div] at h ⊢
    linarith
  have hw : ‖(T : ℂ) + y * I‖ ≤ |T| + 1 := by
    have h := norm_add_le (T : ℂ) ((y : ℂ) * I)
    simp only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs] at h
    linarith
  have hx : ‖poleFreePoint ((T : ℂ) + y * I) - b‖ ≤ |T| + 2 + ‖b‖ := by
    have h1 := norm_add_le (1 / 2 : ℂ) (poleFreeRotor * ((T : ℂ) + y * I))
    have h2 := norm_sub_le (poleFreePoint ((T : ℂ) + y * I)) b
    rw [norm_mul] at h1
    have hm : ‖poleFreeRotor‖ * ‖(T : ℂ) + y * I‖ ≤ |T| + 1 := by
      calc
        _ ≤ 1 * (|T| + 1) := mul_le_mul hr hw (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    norm_num at h1
    unfold poleFreePoint at h2 ⊢
    linarith
  have hp : ‖poleFreePoint ((T : ℂ) + y * I) - b‖ ^ n ≤
      (n.factorial : ℝ) * Real.exp (|T| + 2 + ‖b‖) := by
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have h := (div_le_iff₀ hf).mp
      (Real.pow_div_factorial_le_exp (|T| + 2 + ‖b‖) (by positivity) n)
    exact (pow_le_pow_left₀ (norm_nonneg _) hx n).trans (by nlinarith)
  have hg := mordellRotated_gaussian_bound a (T := T) hy
  have he : |T| - Real.pi / 16 * T ^ 2 ≤ 4 - Real.pi / 32 * T ^ 2 := by
    have h := sq_nonneg (|T| - 8)
    have hpi := mul_nonneg (show 0 ≤ Real.pi - 2 by linarith [Real.two_le_pi]) (sq_nonneg T)
    nlinarith [sq_abs T]
  unfold poleFreeKernel
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_pow,
    poleFree_gaussian_factor, norm_mul, norm_exp]
  calc
    _ ≤ (n.factorial : ℝ) * Real.exp (|T| + 2 + ‖b‖) * 1 *
        (Real.exp D * (Real.exp E * Real.exp (-Real.pi / 16 * T ^ 2))) * 2 := by
      gcongr
      exact poleFree_denominator_tail hT hy
    _ = (n.factorial : ℝ) * 2 *
        Real.exp (|T| + 2 + ‖b‖ + D + E + (-Real.pi / 16 * T ^ 2)) := by
      simp only [Real.exp_add]
      ring
    _ ≤ (n.factorial : ℝ) * 2 *
        Real.exp (6 + ‖b‖ + D + E + (-Real.pi / 32 * T ^ 2)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      linarith
    _ = _ := by rw [Real.exp_add]; ring

theorem poleFreeKernel_horizontal_integrable (n : ℕ) (b : ℂ) {y : ℝ} (hy : |y| < 1) :
    Integrable (fun t : ℝ => poleFreeKernel n b ((t : ℂ) + y * I)) := by
  let f := fun t : ℝ => poleFreeKernel n b ((t : ℂ) + y * I)
  have hf : Continuous f := poleFreeKernel_horizontal_continuous n b hy
  obtain ⟨B, hB, hb⟩ := poleFreeKernel_tail_bound n b
  have hc : Continuous (fun t : ℝ => ‖f t‖ / Real.exp (-Real.pi / 32 * t ^ 2)) :=
    hf.norm.div (by fun_prop) (fun _ => (Real.exp_pos _).ne')
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (hc.continuousOn : ContinuousOn _ (Icc (-3 : ℝ) 3))
  apply ((integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi / 32)).const_mul (max C B)).mono'
    hf.aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  simp only [← neg_div]
  by_cases ht : t ∈ Icc (-3 : ℝ) 3
  · have h := (div_le_iff₀ (Real.exp_pos _)).mp (hC (mem_image_of_mem _ ht))
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left C B) (Real.exp_pos _).le)
  · have ht' : 3 ≤ |t| := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · exact le_abs.mpr (Or.inr (by linarith))
      · exact le_abs.mpr (Or.inl ht.le)
    exact (hb t y ht' hy.le).trans
      (mul_le_mul_of_nonneg_right (le_max_right C B) (Real.exp_pos _).le)

end LiuWang.Proof.Campaign20260915.ZetaMordell
