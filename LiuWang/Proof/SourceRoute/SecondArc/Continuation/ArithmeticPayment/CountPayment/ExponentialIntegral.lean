import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.ActualInner

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment

def coupledKernel (P H z : ℝ) : ℝ :=
  heightKernel z * (z / 3 * Real.log z + P * (4 * Real.log z + 30)) *
    Real.exp (-0.478 * H / Real.log z)

theorem exponential_height_ratio {a z B : ℝ} (hz : 1 < z) (hzB : z ≤ B)
    (ha : (Real.log B) ^ 2 ≤ a) :
    Real.exp (-a / Real.log z) ≤ (z / B) * Real.exp (-a / Real.log B) := by
  have hz0 : 0 < z := by linarith
  have hB0 : 0 < B := hz0.trans_le hzB
  have hu : 0 < Real.log z := Real.log_pos hz
  have hv : 0 < Real.log B := hu.trans_le (Real.log_le_log hz0 hzB)
  have huv := Real.log_le_log hz0 hzB
  have hp : Real.log z * Real.log B ≤ a := by nlinarith
  have hm := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr huv)
  have hphase : -a / Real.log z ≤ Real.log z - Real.log B + -a / Real.log B := by
    apply (mul_le_mul_iff_left₀ (mul_pos hu hv)).mp
    field_simp
    nlinarith only [hm]
  calc
    _ ≤ Real.exp (Real.log z - Real.log B + -a / Real.log B) :=
      Real.exp_le_exp.mpr hphase
    _ = _ := by rw [Real.exp_add, Real.exp_sub, Real.exp_log hz0, Real.exp_log hB0]

theorem coupledKernel_continuous {P H A B : ℝ} (hA : 1 < A) :
    ContinuousOn (coupledKernel P H) (Set.Icc A B) := by
  have hz : ∀ z ∈ Set.Icc A B, z ≠ 0 := fun z hz => ne_of_gt (by linarith [hz.1])
  have hl : ContinuousOn (fun z : ℝ => Real.log z) (Set.Icc A B) := continuousOn_id.log hz
  have hn : ∀ z ∈ Set.Icc A B, Real.log z ≠ 0 :=
    fun z hz => ne_of_gt (Real.log_pos (hA.trans_le hz.1))
  unfold coupledKernel heightKernel
  exact ((continuousOn_id.rpow_const (fun z h => Or.inl (hz z h))).mul
    (((continuousOn_id.div_const 3).mul hl).add
      (continuousOn_const.mul ((continuousOn_const.mul hl).add continuousOn_const)))).mul
        (Real.continuous_exp.comp_continuousOn (continuousOn_const.div hl hn))

theorem rpow_half_integral_upper {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    (∫ z in A..B, z ^ (1 / 2 : ℝ)) ≤ (2 / 3 : ℝ) * B * Real.sqrt B ∧
      (∫ z in A..B, z ^ (-1 / 2 : ℝ)) ≤ 2 * Real.sqrt B := by
  have hB : 0 ≤ B := hA.trans hAB
  have hpow : B ^ (3 / 2 : ℝ) = B * Real.sqrt B := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hB (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0), Real.rpow_one,
      Real.sqrt_eq_rpow]
  constructor
  · rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
    norm_num only
    rw [hpow]
    nlinarith [Real.rpow_nonneg hA (3 / 2 : ℝ)]
  · rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
    norm_num only
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.rpow_nonneg hA (1 / 2 : ℝ)]

theorem coupled_integral_upper {P H A B : ℝ} (hP : 0 ≤ P) (hA : 1 < A)
    (hAB : A ≤ B) (hphase : (Real.log B) ^ 2 ≤ 0.478 * H) :
    (∫ z in A..B, coupledKernel P H z) ≤
      Real.sqrt B * ((2 / 9 : ℝ) * Real.log B +
        2 * (P / B) * (4 * Real.log B + 30)) *
          Real.exp (-0.478 * H / Real.log B) := by
  have hB0 : 0 < B := (by linarith : 0 < A).trans_le hAB
  have hlog0 : 0 ≤ Real.log B := (Real.log_pos (hA.trans_le hAB)).le
  let E := Real.exp (-0.478 * H / Real.log B)
  let f := fun z : ℝ => (E / B) *
    ((Real.log B / 3) * z ^ (1 / 2 : ℝ) +
      (P * (4 * Real.log B + 30)) * z ^ (-1 / 2 : ℝ))
  have hi1 := (intervalIntegral.intervalIntegrable_rpow' (a := A) (b := B)
    (by norm_num : (-1 : ℝ) < 1 / 2)).const_mul (Real.log B / 3)
  have hi2 := (intervalIntegral.intervalIntegrable_rpow' (a := A) (b := B)
    (by norm_num : (-1 : ℝ) < -1 / 2)).const_mul (P * (4 * Real.log B + 30))
  have hi := intervalIntegral.integral_mono_on hAB
    ((coupledKernel_continuous (P := P) (H := H) hA).intervalIntegrable_of_Icc hAB)
    ((hi1.add hi2).const_mul (E / B)) (g := f) (by
      intro z hz
      have hz1 := hA.trans_le hz.1
      have hz0 : 0 < z := by linarith
      have hl0 := (Real.log_pos hz1).le
      have hl := Real.log_le_log hz0 hz.2
      have he := exponential_height_ratio hz1 hz.2 hphase
      rw [← neg_mul] at he
      have hw : z / 3 * Real.log z + P * (4 * Real.log z + 30) ≤
          z / 3 * Real.log B + P * (4 * Real.log B + 30) := by gcongr
      have hp1 : heightKernel z * z ^ (2 : ℕ) = z ^ (1 / 2 : ℝ) := by
        rw [heightKernel, ← Real.rpow_natCast, ← Real.rpow_add hz0]
        norm_num
      have hp2 : heightKernel z * z = z ^ (-1 / 2 : ℝ) := by
        rw [heightKernel]
        nth_rw 2 [← Real.rpow_one z]
        rw [← Real.rpow_add hz0]
        norm_num
      unfold coupledKernel
      calc
        _ ≤ (heightKernel z * (z / 3 * Real.log B + P * (4 * Real.log B + 30))) *
            ((z / B) * E) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw (heightKernel_nonneg hz0.le))
            he (Real.exp_pos _).le (by unfold heightKernel; positivity)
        _ = f z := by
          dsimp [f]
          calc
            _ = (E / B) * ((Real.log B / 3) * (heightKernel z * z ^ (2 : ℕ)) +
                (P * (4 * Real.log B + 30)) * (heightKernel z * z)) := by ring
            _ = _ := by rw [hp1, hp2])
  have hp := rpow_half_integral_upper (by linarith : 0 ≤ A) hAB
  apply hi.trans
  dsimp [f]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  calc
    _ ≤ (E / B) * ((Real.log B / 3) * ((2 / 3 : ℝ) * B * Real.sqrt B) +
        (P * (4 * Real.log B + 30)) * (2 * Real.sqrt B)) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [E]; positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hp.1 (by positivity))
        (mul_le_mul_of_nonneg_left hp.2 (by positivity))
    _ = _ := by dsimp [E]; field_simp; ring

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
