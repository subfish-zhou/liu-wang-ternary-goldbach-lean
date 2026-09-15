import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelKernel

set_option autoImplicit false
noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsHankelRightBank (s : ℂ) (m : ℕ) (y : ℝ) : ℂ :=
  exp (-(Real.pi / 2 : ℂ) * I * s) * (y : ℂ) ^ (s - 1) *
    rsMellinTailKernel m (2 * Real.pi * y)

def rsHankelLeftBank (s : ℂ) (m : ℕ) (y : ℝ) : ℂ :=
  exp (2 * Real.pi * I * s) * rsHankelRightBank s m y

theorem rsHankelLog_right_limit {y : ℝ} (hy : 0 < y) :
    Tendsto rsHankelLog (𝓝[{z : ℂ | 0 < z.re}] (-I * y))
      (𝓝 ((Real.log y : ℂ) - Real.pi / 2 * I)) := by
  have ht : Tendsto (fun z : ℂ => -I * z) (𝓝[{z : ℂ | 0 < z.re}] (-I * y))
      (𝓝[{w : ℂ | w.im < 0}] (-y : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun z : ℂ => -I * z) := by fun_prop
      have h := (hc.tendsto (-I * (y : ℂ))).mono_left
        (nhdsWithin_le_nhds (s := {z : ℂ | 0 < z.re}))
      have he : -I * (-I * (y : ℂ)) = -(y : ℂ) := by simp [← mul_assoc]
      rwa [he] at h
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have hl := (tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (z := (-y : ℂ)) (by simpa) (by simp)).comp ht
  have h := hl.add_const (Real.pi / 2 * I)
  change Tendsto rsHankelLog _ (𝓝 ((Real.log ‖-(y : ℂ)‖ : ℂ) -
    Real.pi * I + Real.pi / 2 * I)) at h
  have he : (Real.log ‖-(y : ℂ)‖ : ℂ) - Real.pi * I + Real.pi / 2 * I =
      (Real.log y : ℂ) - Real.pi / 2 * I := by
    rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos hy]
    ring
  rwa [he] at h

theorem rsHankelLog_left_limit {y : ℝ} (hy : 0 < y) :
    Tendsto rsHankelLog (𝓝[{z : ℂ | z.re ≤ 0}] (-I * y))
      (𝓝 ((Real.log y : ℂ) + 3 * Real.pi / 2 * I)) := by
  have ht : Tendsto (fun z : ℂ => -I * z) (𝓝[{z : ℂ | z.re ≤ 0}] (-I * y))
      (𝓝[{w : ℂ | 0 ≤ w.im}] (-y : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun z : ℂ => -I * z) := by fun_prop
      have h := (hc.tendsto (-I * (y : ℂ))).mono_left
        (nhdsWithin_le_nhds (s := {z : ℂ | z.re ≤ 0}))
      have he : -I * (-I * (y : ℂ)) = -(y : ℂ) := by simp [← mul_assoc]
      rwa [he] at h
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have hl := (tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := (-y : ℂ)) (by simpa) (by simp)).comp ht
  have h := hl.add_const (Real.pi / 2 * I)
  change Tendsto rsHankelLog _ (𝓝 ((Real.log ‖-(y : ℂ)‖ : ℂ) +
    Real.pi * I + Real.pi / 2 * I)) at h
  have he : (Real.log ‖-(y : ℂ)‖ : ℂ) + Real.pi * I + Real.pi / 2 * I =
      (Real.log y : ℂ) + 3 * Real.pi / 2 * I := by
    rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos hy]
    ring
  rwa [he] at h

theorem rsHankelRightBank_factor (s : ℂ) (m : ℕ) {y : ℝ} (hy : 0 < y) :
    -I * exp ((s - 1) * ((Real.log y : ℂ) - Real.pi / 2 * I) -
      2 * Real.pi * I * m * (-I * y)) / rsHankelDenominator (-I * y) =
        rsHankelRightBank s m y := by
  have he : -(Real.pi / 2 : ℂ) * I * s + log (y : ℂ) * (s - 1) +
      (-(m : ℝ) * (2 * Real.pi * y) : ℝ) =
      -(Real.pi / 2 : ℂ) * I +
        ((s - 1) * ((Real.log y : ℂ) - Real.pi / 2 * I) -
          2 * Real.pi * I * m * (-I * y)) := by
    rw [← ofReal_log hy.le]
    push_cast
    ring_nf
    simp [I_sq]
    ring
  have hd : rsHankelDenominator (-I * y) = ((Real.exp (2 * Real.pi * y) - 1 : ℝ) : ℂ) := by
    unfold rsHankelDenominator
    push_cast
    congr 2
    ring_nf
    simp [I_sq]
  symm
  calc
    _ = (exp (-(Real.pi / 2 : ℂ) * I * s) * exp (log (y : ℂ) * (s - 1)) *
        exp (((-(m : ℝ) * (2 * Real.pi * y)) : ℝ) : ℂ)) / rsHankelDenominator (-I * y) := by
      rw [rsHankelRightBank, rsMellinTailKernel, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hy.ne'),
        hd, ofReal_div, ofReal_exp]
      ring
    _ = _ := by rw [← exp_add, ← exp_add, he, exp_add, ← neg_div, exp_neg_pi_div_two_mul_I]

theorem rsHankelRightBank_limit (s : ℂ) (m : ℕ) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun z : ℂ => -I * rsHankelKernel s m z)
      (𝓝[{z : ℂ | 0 < z.re}] (-I * y)) (𝓝 (rsHankelRightBank s m y)) := by
  have hn : rsHankelDenominator (-I * y) ≠ 0 := by
    rw [ne_eq, rsHankelDenominator_zero_iff]
    rintro ⟨n, hn⟩
    have hi := congrArg Complex.im hn
    simp at hi
    linarith
  have hid := (continuous_id.tendsto (-I * (y : ℂ))).mono_left
    (nhdsWithin_le_nhds (s := {z : ℂ | 0 < z.re}))
  have h := ((rsHankelLog_right_limit hy).const_mul (s - 1)).sub
    (hid.const_mul (2 * Real.pi * I * m))
  have ht := ((h.cexp.const_mul (-I)).div
    ((rsHankelDenominator_analytic _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hn)
  simp only [id_eq] at ht
  rw [rsHankelRightBank_factor s m hy] at ht
  convert ht using 1
  funext z
  simp only [rsHankelKernel, rsHankelNumerator, Pi.div_apply]
  ring

theorem rsHankelLeftBank_limit (s : ℂ) (m : ℕ) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun z : ℂ => -I * rsHankelKernel s m z)
      (𝓝[{z : ℂ | z.re ≤ 0}] (-I * y)) (𝓝 (rsHankelLeftBank s m y)) := by
  have hn : rsHankelDenominator (-I * y) ≠ 0 := by
    rw [ne_eq, rsHankelDenominator_zero_iff]
    rintro ⟨n, hn⟩
    have hi := congrArg Complex.im hn
    simp at hi
    linarith
  have hid := (continuous_id.tendsto (-I * (y : ℂ))).mono_left
    (nhdsWithin_le_nhds (s := {z : ℂ | z.re ≤ 0}))
  have h := ((rsHankelLog_left_limit hy).const_mul (s - 1)).sub
    (hid.const_mul (2 * Real.pi * I * m))
  have he : exp ((s - 1) * ((Real.log y : ℂ) + 3 * Real.pi / 2 * I) -
      2 * Real.pi * I * m * (-I * y)) =
      exp (2 * Real.pi * I * s) * exp ((s - 1) *
        ((Real.log y : ℂ) - Real.pi / 2 * I) - 2 * Real.pi * I * m * (-I * y)) := by
    rw [show (s - 1) * ((Real.log y : ℂ) + 3 * Real.pi / 2 * I) -
      2 * Real.pi * I * m * (-I * y) =
      2 * Real.pi * I * s - 2 * Real.pi * I +
        ((s - 1) * ((Real.log y : ℂ) - Real.pi / 2 * I) -
          2 * Real.pi * I * m * (-I * y)) by ring, exp_add, exp_sub,
      exp_two_pi_mul_I, div_one]
  have ht := ((h.cexp.const_mul (-I)).div
    ((rsHankelDenominator_analytic _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hn)
  simp only [id_eq] at ht
  rw [he] at ht
  have halg (A B D : ℂ) : -I * (A * B) / D = A * (-I * B / D) := by ring
  rw [halg, rsHankelRightBank_factor s m hy] at ht
  unfold rsHankelLeftBank
  convert ht using 1
  funext z
  simp only [rsHankelKernel, rsHankelNumerator, Pi.div_apply]
  ring

theorem rsHankelBanks_integrable {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (rsHankelRightBank s m) (Ioi 0) ∧
      IntegrableOn (rsHankelLeftBank s m) (Ioi 0) := by
  have hc : MellinConvergent (rsMellinTailKernel m) s := rsMellinTail_integrable hm hs
  have hc' := (MellinConvergent.comp_mul_left (a := 2 * Real.pi) (by positivity)).mpr hc
  have hr : IntegrableOn (rsHankelRightBank s m) (Ioi 0) := by
    have h := hc'.const_mul (exp (-(Real.pi / 2 : ℂ) * I * s))
    change IntegrableOn (fun y : ℝ => exp (-(Real.pi / 2 : ℂ) * I * s) *
      ((y : ℂ) ^ (s - 1) * rsMellinTailKernel m (2 * Real.pi * y))) (Ioi 0) at h
    exact IntegrableOn.congr_fun h (fun y _ => (mul_assoc _ _ _).symm) measurableSet_Ioi
  exact ⟨hr, hr.const_mul _⟩

theorem rsHankelBanks_actual_zeta (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 0, rsHankelLeftBank s m y) -
      (∫ y : ℝ in Ioi 0, rsHankelRightBank s m y) =
      (exp (2 * Real.pi * I * s) - 1) * exp (-(Real.pi / 2 : ℂ) * I * s) *
        (2 * Real.pi : ℂ) ^ (-s) * Gamma s *
          (riemannZeta s - ∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) := by
  have hr : (∫ y : ℝ in Ioi 0, rsHankelRightBank s m y) =
      exp (-(Real.pi / 2 : ℂ) * I * s) * (2 * Real.pi : ℂ) ^ (-s) *
        Gamma s * (riemannZeta s - ∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) := by
    have he : rsHankelRightBank s m = fun y : ℝ =>
        exp (-(Real.pi / 2 : ℂ) * I * s) *
          ((y : ℂ) ^ (s - 1) * rsMellinTailKernel m (2 * Real.pi * y)) := by
      funext y
      exact mul_assoc _ _ _
    rw [he, integral_const_mul]
    change exp (-(Real.pi / 2 : ℂ) * I * s) *
      mellin (fun y : ℝ => rsMellinTailKernel m (2 * Real.pi * y)) s = _
    rw [mellin_comp_mul_left _ _ (by positivity), smul_eq_mul, rsMellinTail_mellin m hs]
    push_cast
    ring
  simp_rw [rsHankelLeftBank]
  rw [integral_const_mul, hr]
  ring

end LiuWang.Proof.Campaign20260915.ZetaValidation
