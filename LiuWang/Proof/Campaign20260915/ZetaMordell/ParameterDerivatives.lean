import LiuWang.Proof.Campaign20260915.ZetaMordell.DirectedIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Filter
open scoped Real Topology

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

def mordellWeightedKernel (n : ℕ) (a : ℂ) (t : ℝ) : ℂ :=
  (2 * Real.pi * I * mordellLine t) ^ n * mordellKernel a t

def mordellMoment (n : ℕ) (a : ℂ) : ℂ := ∫ t : ℝ, mordellWeightedKernel n a t

theorem mordellLine_norm_le (t : ℝ) : ‖mordellLine t‖ ≤ 1 + 2 * |t| := by
  have hd : ‖(1 : ℂ) + I‖ ≤ 2 := by
    simpa only [norm_one, norm_I, one_add_one_eq_two] using norm_add_le (1 : ℂ) I
  calc
    ‖mordellLine t‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(1 + I) * (t : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 + 2 * |t| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      norm_num
      nlinarith [mul_le_mul_of_nonneg_right hd (abs_nonneg t)]

theorem mordellGaussian_norm_le {R : ℝ} {a : ℂ} (ha : ‖a‖ ≤ R) (t : ℝ) :
    ‖mordellGaussian a t‖ ≤ Real.exp
      (-2 * Real.pi * t ^ 2 + (2 * Real.pi * (1 + 2 * R)) * |t| +
        Real.pi * (1 / 4 + R)) := by
  have hR : 0 ≤ R := (norm_nonneg a).trans ha
  have hd : ‖(1 : ℂ) + I‖ ≤ 2 := by
    simpa only [norm_one, norm_I, one_add_one_eq_two] using norm_add_le (1 : ℂ) I
  have hc : ‖(Real.pi : ℂ) * I * (1 + 2 * a) * (1 + I)‖ ≤
      2 * Real.pi * (1 + 2 * R) := by
    calc
      _ = Real.pi * ‖1 + 2 * a‖ * ‖1 + I‖ := by
        simp [Real.pi_pos.le]
      _ ≤ Real.pi * (1 + 2 * R) * 2 := by
        gcongr
        calc
          ‖1 + 2 * a‖ ≤ ‖(1 : ℂ)‖ + ‖2 * a‖ := norm_add_le _ _
          _ ≤ 1 + 2 * R := by simpa [norm_mul] using (by linarith : 1 + 2 * ‖a‖ ≤ 1 + 2 * R)
      _ = _ := by ring
  have he : ‖(Real.pi : ℂ) * I * (1 / 4 + a)‖ ≤ Real.pi * (1 / 4 + R) := by
    calc
      _ = Real.pi * ‖(1 / 4 : ℂ) + a‖ := by simp [Real.pi_pos.le]
      _ ≤ Real.pi * (1 / 4 + R) := by
        gcongr
        calc
          ‖(1 / 4 : ℂ) + a‖ ≤ ‖(1 / 4 : ℂ)‖ + ‖a‖ := norm_add_le _ _
          _ ≤ 1 / 4 + R := by norm_num; exact ha
  rw [mordellGaussian_quadratic, norm_exp, Real.exp_le_exp]
  have ht := re_le_norm ((Real.pi : ℂ) * I * (1 + 2 * a) * (1 + I) * t)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at ht
  have hc' := mul_le_mul_of_nonneg_right hc (abs_nonneg t)
  have he' := (re_le_norm ((Real.pi : ℂ) * I * (1 / 4 + a))).trans he
  simp only [add_re]
  have hb : ((-2 * Real.pi : ℂ) * (t : ℂ) ^ 2).re = -2 * Real.pi * t ^ 2 := by
    simp [pow_two, mul_re, mul_im]
  rw [hb]
  linarith

theorem mordellWeightedKernel_continuous (n : ℕ) (a : ℂ) :
    Continuous (mordellWeightedKernel n a) := by
  have hk : Continuous (mordellKernel a) := by
    unfold mordellKernel
    apply Continuous.mul_const
    apply Continuous.div
    · unfold mordellGaussian mordellLine
      fun_prop
    · unfold mordellDenominator mordellLine
      fun_prop
    · exact mordellDenominator_ne_zero
  unfold mordellWeightedKernel
  apply Continuous.mul _ hk
  unfold mordellLine
  fun_prop

theorem mordellWeightedKernel_uniform_bound (n : ℕ) {R C : ℝ}
    (_hR : 0 ≤ R) (hC : 0 ≤ C)
    (hden : ∀ t : ℝ, ‖(mordellDenominator t)⁻¹‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : ℂ), ‖a‖ ≤ R → ∀ t : ℝ,
      ‖mordellWeightedKernel n a t‖ ≤ B * Real.exp (-Real.pi * t ^ 2) := by
  let K := 2 * Real.pi * (1 + 2 * R) + 4 * Real.pi
  let L := Real.pi * (1 / 4 + R) + 2 * Real.pi
  refine ⟨(n.factorial : ℝ) * C * 2 * Real.exp (K ^ 2 + L), by positivity, ?_⟩
  intro a ha t
  have hq : ‖2 * (Real.pi : ℂ) * I * mordellLine t‖ ≤
      2 * Real.pi * (1 + 2 * |t|) := by
    simpa [norm_mul, abs_of_pos Real.pi_pos] using
      mul_le_mul_of_nonneg_left (mordellLine_norm_le t) (by positivity : 0 ≤ 2 * Real.pi)
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hp : ‖2 * (Real.pi : ℂ) * I * mordellLine t‖ ^ n ≤
      (n.factorial : ℝ) * Real.exp (2 * Real.pi * (1 + 2 * |t|)) := by
    have h := Real.pow_div_factorial_le_exp (2 * Real.pi * (1 + 2 * |t|))
      (by positivity : 0 ≤ 2 * Real.pi * (1 + 2 * |t|)) n
    have h' := (div_le_iff₀ hf).mp h
    exact (pow_le_pow_left₀ (norm_nonneg _) hq n).trans (by nlinarith)
  have hd : ‖(1 : ℂ) + I‖ ≤ 2 := by
    simpa only [norm_one, norm_I, one_add_one_eq_two] using norm_add_le (1 : ℂ) I
  have hphase : -2 * Real.pi * t ^ 2 + K * |t| + L ≤
      K ^ 2 + L + (-Real.pi * t ^ 2) := by
    nlinarith [sq_nonneg (|t| - K), sq_abs t, Real.two_le_pi, sq_nonneg t]
  calc
    ‖mordellWeightedKernel n a t‖ =
        ‖2 * (Real.pi : ℂ) * I * mordellLine t‖ ^ n *
          ‖mordellGaussian a t‖ * ‖(mordellDenominator t)⁻¹‖ * ‖1 + I‖ := by
      simp only [mordellWeightedKernel, mordellKernel, div_eq_mul_inv, norm_mul, norm_pow]
      ring
    _ ≤ ((n.factorial : ℝ) * Real.exp (2 * Real.pi * (1 + 2 * |t|))) *
        Real.exp (-2 * Real.pi * t ^ 2 + (2 * Real.pi * (1 + 2 * R)) * |t| +
          Real.pi * (1 / 4 + R)) * C * 2 := by
      gcongr
      · exact mordellGaussian_norm_le ha t
      · exact hden t
    _ = (n.factorial : ℝ) * C * 2 * Real.exp (-2 * Real.pi * t ^ 2 + K * |t| + L) := by
      rw [show (n.factorial : ℝ) * Real.exp (2 * Real.pi * (1 + 2 * |t|)) *
          Real.exp (-2 * Real.pi * t ^ 2 + (2 * Real.pi * (1 + 2 * R)) * |t| +
            Real.pi * (1 / 4 + R)) =
          (n.factorial : ℝ) * (Real.exp (2 * Real.pi * (1 + 2 * |t|)) *
            Real.exp (-2 * Real.pi * t ^ 2 + (2 * Real.pi * (1 + 2 * R)) * |t| +
              Real.pi * (1 / 4 + R))) by ring, ← Real.exp_add]
      rw [show 2 * Real.pi * (1 + 2 * |t|) +
          (-2 * Real.pi * t ^ 2 + (2 * Real.pi * (1 + 2 * R)) * |t| +
            Real.pi * (1 / 4 + R)) = -2 * Real.pi * t ^ 2 + K * |t| + L by
              dsimp [K, L]; ring]
      ring
    _ ≤ (n.factorial : ℝ) * C * 2 * Real.exp (K ^ 2 + L + (-Real.pi * t ^ 2)) := by
      gcongr
    _ = _ := by rw [Real.exp_add]; ring

theorem mordellWeightedKernel_integrable (n : ℕ) (a : ℂ) :
    Integrable (mordellWeightedKernel n a) := by
  obtain ⟨C, hC, hden⟩ := mordellDenominator_inv_bounded
  obtain ⟨B, _, hB⟩ := mordellWeightedKernel_uniform_bound n (norm_nonneg a) hC hden
  exact ((integrable_exp_neg_mul_sq Real.pi_pos).const_mul B).mono'
    (mordellWeightedKernel_continuous n a).aestronglyMeasurable
    (Eventually.of_forall (hB a le_rfl))

theorem mordellWeightedKernel_hasDerivAt (n : ℕ) (a : ℂ) (t : ℝ) :
    HasDerivAt (fun a : ℂ => mordellWeightedKernel n a t)
      (mordellWeightedKernel (n + 1) a t) a := by
  have h := (((((hasDerivAt_id a).const_mul (2 * Real.pi * I)).mul_const
    (mordellLine t)).const_add (Real.pi * I * mordellLine t ^ 2)).cexp.div_const
      (mordellDenominator t)).mul_const (1 + I)
  have h' := h.const_mul ((2 * Real.pi * I * mordellLine t) ^ n)
  convert! h' using 1
  unfold mordellWeightedKernel mordellKernel mordellGaussian
  simp only [pow_succ, mul_one, id_eq]
  ring

theorem mordellMoment_hasDerivAt (n : ℕ) (a : ℂ) :
    HasDerivAt (mordellMoment n) (mordellMoment (n + 1) a) a := by
  obtain ⟨C, hC, hden⟩ := mordellDenominator_inv_bounded
  obtain ⟨B, _, hB⟩ := mordellWeightedKernel_uniform_bound (n + 1)
    (show 0 ≤ ‖a‖ + 1 by positivity) hC hden
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball a 1) (bound := fun t : ℝ => B * Real.exp (-Real.pi * t ^ 2))
    (Metric.ball_mem_nhds a (by norm_num))
    (Eventually.of_forall (fun b => (mordellWeightedKernel_continuous n b).aestronglyMeasurable))
    (mordellWeightedKernel_integrable n a)
    (mordellWeightedKernel_continuous (n + 1) a).aestronglyMeasurable
    (Eventually.of_forall (fun t b hb => hB b ?_ t))
    ((integrable_exp_neg_mul_sq Real.pi_pos).const_mul B)
    (Eventually.of_forall (fun t b _ => mordellWeightedKernel_hasDerivAt n b t))).2
  have hb' : ‖b - a‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hb
  have := norm_add_le (b - a) a
  rw [sub_add_cancel] at this
  linarith

theorem mordellMoment_zero : mordellMoment 0 = mordellIntegral := by
  ext a
  simp [mordellMoment, mordellWeightedKernel, mordellIntegral]

theorem mordellIntegral_iteratedDeriv (n : ℕ) :
    iteratedDeriv n mordellIntegral = mordellMoment n := by
  induction n with
  | zero => simpa using mordellMoment_zero.symm
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext (fun a => (mordellMoment_hasDerivAt n a).deriv)

end LiuWang.Proof.Campaign20260915.ZetaMordell
