import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.Assembly

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

def lowUpperLog (L : ℝ) : ℝ := Real.log (scaledGate L)

def lowLogKernel (L z : ℝ) : ℝ :=
  L * ((z + 3 * Real.log L) / Real.pi - 0.874) *
      Real.exp (z / 2 - 0.478 * (L + Real.log 0.001) / z) +
    L * L ^ (3 : ℕ) * (6.8423 * (z + 3 * Real.log L) + 15) *
      Real.exp (-z / 2 - 0.478 * (L + Real.log 0.001) / z)

theorem low_log_jacobian {L : ℝ} (hL : 0 < L) (z : ℝ) :
    Real.exp z * (L * lowWeight (L ^ (3 : ℕ)) (Real.exp z) *
      Real.exp (-0.478 * (L + Real.log 0.001) / Real.log (Real.exp z))) =
        lowLogKernel L z := by
  have hl : Real.log (L ^ (3 : ℕ) * Real.exp z) = z + 3 * Real.log L := by
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
    norm_num
    ring
  have he (c a : ℝ) : Real.exp z * (Real.exp z) ^ c * Real.exp a = Real.exp ((1 + c) * z + a) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have he1 : Real.exp z * (Real.exp z) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-0.478 * (L + Real.log 0.001) / z) =
        Real.exp (z / 2 - 0.478 * (L + Real.log 0.001) / z) := by
    rw [he]
    congr 1
    ring
  have he3 : Real.exp z * (Real.exp z) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-0.478 * (L + Real.log 0.001) / z) =
        Real.exp (-z / 2 - 0.478 * (L + Real.log 0.001) / z) := by
    rw [he]
    congr 1
    ring
  unfold lowWeight lowLogKernel
  rw [hl, Real.log_exp, ← he1, ← he3]
  ring

theorem originalLowScalar_log {L : ℝ} (hL : 3100 ≤ L) :
    originalLowScalar L = ∫ z in lowerLog L..lowUpperLog L, lowLogKernel L z := by
  have hL0 : 0 < L := by linarith
  have hd := low_scalar_domain hL
  have hc := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := lowerLog L) (b := lowUpperLog L)
    (f := Real.exp) (f' := Real.exp)
    (g := fun y : ℝ => L * lowWeight (L ^ (3 : ℕ)) y *
      Real.exp (-0.478 * (L + Real.log 0.001) / Real.log y))
    (by fun_prop) (fun z _ => Real.hasDerivAt_exp z) (fun z _ => (Real.exp_pos z).le)
  rw [show Real.exp (lowerLog L) = 3.36 * L ^ (3 : ℕ) by exact Real.exp_log hd.1,
    show Real.exp (lowUpperLog L) = scaledGate L by exact Real.exp_log (hd.1.trans_le hd.2.1)] at hc
  unfold originalLowScalar
  unfold scaledGate at hc
  rw [← hc]
  apply intervalIntegral.integral_congr
  intro z _
  exact low_log_jacobian hL0 z

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight
