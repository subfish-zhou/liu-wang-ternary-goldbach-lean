import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.ScalarReduction

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral

def sourcePolynomial (y : ℝ) : ℝ := 254231 * y ^ (5 : ℕ) + 33643 * y ^ (6 : ℕ)

def phaseSlope (H m : ℝ) : ℝ := -1 / 2 + 0.478 * H / m ^ (2 : ℕ)

def phaseIntercept (H m : ℝ) : ℝ := -0.956 * H / m

def denominatorChord (H u v y : ℝ) : ℝ :=
  H * (H - 4 * (u + v - y)) / ((H - 4 * u) * (H - 4 * v))

def cellEnvelope (H u v m y : ℝ) : ℝ :=
  sourcePolynomial y * denominatorChord H u v y *
    Real.exp (phaseSlope H m * y + phaseIntercept H m)

theorem densityKernel_polynomial {H y : ℝ} (hy : y ≠ 0) :
    densityKernel H y = sourcePolynomial y * (H / (H - 4 * y)) *
      Real.exp (-y / 2 - 0.478 * H / y) := by
  unfold densityKernel sourcePolynomial
  congr 2
  field_simp

theorem phase_tangent_remainder {H m y : ℝ} (hm : m ≠ 0) (hy : y ≠ 0) :
    phaseSlope H m * y + phaseIntercept H m - (-y / 2 - 0.478 * H / y) =
      0.478 * H * (y - m) ^ (2 : ℕ) / (m ^ (2 : ℕ) * y) := by
  unfold phaseSlope phaseIntercept
  field_simp
  ring

theorem phase_le_tangent {H m y : ℝ} (hH : 0 ≤ H) (hm : 0 < m) (hy : 0 < y) :
    -y / 2 - 0.478 * H / y ≤ phaseSlope H m * y + phaseIntercept H m := by
  have h := phase_tangent_remainder (H := H) hm.ne' hy.ne'
  have hp : 0 ≤ 0.478 * H * (y - m) ^ (2 : ℕ) / (m ^ (2 : ℕ) * y) := by positivity
  linarith only [h, hp]

theorem denominator_chord_remainder {H u v y : ℝ}
    (hu : H - 4 * u ≠ 0) (hv : H - 4 * v ≠ 0) (hy : H - 4 * y ≠ 0) :
    denominatorChord H u v y - H / (H - 4 * y) =
      16 * H * (y - u) * (v - y) /
        ((H - 4 * u) * (H - 4 * v) * (H - 4 * y)) := by
  unfold denominatorChord
  field_simp
  ring

theorem denominator_chord_endpoints {H u v : ℝ}
    (hu : H - 4 * u ≠ 0) (hv : H - 4 * v ≠ 0) :
    denominatorChord H u v u = H / (H - 4 * u) ∧
      denominatorChord H u v v = H / (H - 4 * v) := by
  unfold denominatorChord
  constructor <;> field_simp <;> ring

theorem denominator_chord_barycentric {H u v y : ℝ}
    (hu : H - 4 * u ≠ 0) (hv : H - 4 * v ≠ 0) (huv : u ≠ v) :
    denominatorChord H u v y =
      ((v - y) / (v - u)) * (H / (H - 4 * u)) +
        ((y - u) / (v - u)) * (H / (H - 4 * v)) := by
  have hw : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
  unfold denominatorChord
  field_simp
  ring

theorem denominator_le_chord {H u v y : ℝ} (hu : 0 < u)
    (hy : y ∈ Set.Icc u v) (hH : 4 * v < H) :
    0 ≤ H / (H - 4 * y) ∧ H / (H - 4 * y) ≤ denominatorChord H u v y := by
  have hHy : 0 < H - 4 * y := by linarith [hy.2]
  have hHu : 0 < H - 4 * u := by linarith [hy.1, hy.2]
  have hHv : 0 < H - 4 * v := by linarith
  have hHp : 0 < H := by linarith [hy.1, hy.2]
  have he := denominator_chord_remainder hHu.ne' hHv.ne' hHy.ne'
  have h1 : 0 ≤ y - u := sub_nonneg.mpr hy.1
  have h2 : 0 ≤ v - y := sub_nonneg.mpr hy.2
  have hp : 0 ≤ 16 * H * (y - u) * (v - y) /
      ((H - 4 * u) * (H - 4 * v) * (H - 4 * y)) := by positivity
  exact ⟨by positivity, by linarith only [he, hp]⟩

theorem densityKernel_le_cellEnvelope {H u v m y : ℝ} (hu : 0 < u)
    (hy : y ∈ Set.Icc u v) (hm : m ∈ Set.Icc u v) (hH : 4 * v < H) :
    densityKernel H y ≤ cellEnvelope H u v m y := by
  have hy0 := hu.trans_le hy.1
  have hm0 := hu.trans_le hm.1
  have hHp : 0 < H := by linarith [hy.1, hy.2]
  have hd := denominator_le_chord hu hy hH
  have he := Real.exp_le_exp.mpr (phase_le_tangent hHp.le hm0 hy0)
  rw [densityKernel_polynomial hy0.ne']
  unfold cellEnvelope
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hd.2 (by unfold sourcePolynomial; positivity)) he
    (Real.exp_pos _).le
    (mul_nonneg (by unfold sourcePolynomial; positivity) (hd.1.trans hd.2))

theorem densityKernel_nonnegative {H y : ℝ} (hy : 0 < y) (hH : 4 * y < H) :
    0 ≤ densityKernel H y := by
  have hHp : 0 < H := by linarith
  have hd : 0 < H - 4 * y := by linarith
  unfold densityKernel
  positivity

theorem densityKernel_continuousOn {H u v : ℝ} (hu : 0 < u) (hH : 4 * v < H) :
    ContinuousOn (densityKernel H) (Set.Icc u v) := by
  have hz : ∀ y ∈ Set.Icc u v, y ≠ 0 := fun y hy => (hu.trans_le hy.1).ne'
  have hd : ∀ y ∈ Set.Icc u v, H - 4 * y ≠ 0 :=
    fun y hy => ne_of_gt (by linarith [hy.2])
  unfold densityKernel
  exact ((((continuousOn_const.div continuousOn_id hz).add continuousOn_const).mul
    (continuousOn_id.pow 6)).mul
    (continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) hd)).mul
    (Real.continuous_exp.comp_continuousOn
      (((continuousOn_id.neg).div_const 2).sub (continuousOn_const.div continuousOn_id hz)))

theorem cellEnvelope_continuous (H u v m : ℝ) : Continuous (cellEnvelope H u v m) := by
  unfold cellEnvelope denominatorChord sourcePolynomial
  fun_prop

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral
