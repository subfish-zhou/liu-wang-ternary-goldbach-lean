import LiuWang.Proof.MajorArcApproximation.Integral
import LiuWang.Proof.SingularSeries.Decimal.Strong

/-! # 模型三次积分的实际 I11 与有号零点相互作用 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open MeasureTheory
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.MajorArcApproximation

def packet (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    zeroPacket q N a eta

theorem packet_eq {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    packet N a q eta = zeroPacket q N a eta := by
  simp only [packet, dif_neg (NeZero.ne q)]

theorem model_eq_main_sub_packet (N a q : ℕ) (eta : ℝ) :
    model N a q eta = principalCoefficient q * J N eta - packet N a q eta := by
  by_cases hq : q = 0
  · subst q
    simp [model, packet, principalCoefficient]
  · let : NeZero q := ⟨hq⟩
    rw [model_eq, packet_eq]

theorem continuous_packet {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    Continuous (packet N a q) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (packet_eq N a)]
    exact continuous_zeroPacket hN a

def interactionKernel (N a q : ℕ) (eta : ℝ) : ℂ :=
  -3 * (principalCoefficient q * J N eta)^2 * packet N a q eta +
    3 * (principalCoefficient q * J N eta) * packet N a q eta^2 -
    packet N a q eta^3

def interactionIntegral (N : ℕ) : ℂ :=
  ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
    interactionKernel N i.2 i.1 eta * arcPhase N i.2 i.1 eta

def pureIntegral (N : ℕ) : ℂ :=
  ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
    (principalCoefficient i.1 * J N eta)^3 * arcPhase N i.2 i.1 eta

theorem continuous_interactionKernel {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    Continuous (interactionKernel N a q) := by
  unfold interactionKernel
  have hJ := continuous_J hN
  have hZ := continuous_packet hN a q
  fun_prop

theorem interaction_integrable {N : ℕ} (hN : 0 < N) (a q : ℕ) (l r : ℝ) :
    IntervalIntegrable (fun eta => interactionKernel N a q eta * arcPhase N a q eta)
      volume l r :=
  ((continuous_interactionKernel hN a q).mul (continuous_arcPhase N a q)).intervalIntegrable l r

theorem cube_model_eq (N a q : ℕ) (eta : ℝ) :
    model N a q eta^3 =
      (principalCoefficient q * J N eta)^3 + interactionKernel N a q eta := by
  rw [model_eq_main_sub_packet]
  unfold interactionKernel
  ring

theorem arcPhase_split (N a q : ℕ) (eta : ℝ) :
    arcPhase N a q eta =
      charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ)) * charReal (-(N : ℝ) * eta) := by
  unfold arcPhase rationalCenter
  rw [show -(N : ℝ) * ((a : ℝ) / q + eta) =
    -(a : ℝ) * N / q + -(N : ℝ) * eta by ring, charReal_add]

theorem principalCoefficient_cube (q : ℕ) :
    principalCoefficient q^3 = (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)^3 := by
  unfold principalCoefficient
  rw [div_pow]
  have hm : (ArithmeticFunction.moebius q : ℂ)^3 = (ArithmeticFunction.moebius q : ℂ) := by
    rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> norm_num [h]
  rw [hm]

theorem pure_kernel_eq (N a q : ℕ) (eta : ℝ) :
    (principalCoefficient q * J N eta)^3 * arcPhase N a q eta =
      ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)^3 *
        charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ))) *
      (J N eta^3 * charReal (-(N : ℝ) * eta)) := by
  rw [mul_pow, principalCoefficient_cube, arcPhase_split]
  ring

theorem pureIntegral_eq_I11 (N : ℕ) : pureIntegral N = I11 N := by
  rw [pureIntegral, coreIndices, Finset.sum_sigma, I11_source]
  apply Finset.sum_congr rfl
  intro q _
  simp only [pure_kernel_eq, intervalIntegral.integral_const_mul, numerators,
    Finset.mul_sum, Finset.sum_mul]

theorem modelIntegral_eq_I11_add_interaction {N : ℕ} (hN : 0 < N) :
    modelIntegral N = I11 N + interactionIntegral N := by
  rw [← pureIntegral_eq_I11, modelIntegral, pureIntegral, interactionIntegral,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hp : Continuous (fun eta => (principalCoefficient i.1 * J N eta)^3 *
      arcPhase N i.2 i.1 eta) :=
    ((continuous_const.mul (continuous_J hN)).pow 3).mul (continuous_arcPhase N i.2 i.1)
  simp only [cube_model_eq, add_mul]
  exact intervalIntegral.integral_add (hp.intervalIntegrable _ _)
    (interaction_integrable hN _ _ _ _)

theorem norm_major_sub_I11_interaction {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖majorIntegral N - (I11 N + interactionIntegral N)‖ ≤ errorIntegral N := by
  rw [← modelIntegral_eq_I11_add_interaction (nat_pos_of_exp_le hN)]
  exact norm_major_sub_model_le_errorIntegral hN

theorem re_major_lower_mother {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (I11 N).re + (interactionIntegral N).re - errorIntegral N ≤ (majorIntegral N).re := by
  have hh := (Complex.re_le_norm (I11 N + interactionIntegral N - majorIntegral N)).trans
    (by simpa only [norm_sub_rev] using norm_major_sub_I11_interaction hN)
  simp only [Complex.sub_re, Complex.add_re] at hh
  linarith

theorem re_major_lower_log_power {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (I11 N).re + (interactionIntegral N).re -
      6760 * (N : ℝ)^2 / sourceL N^4 ≤ (majorIntegral N).re := by
  linarith [re_major_lower_mother hN, errorIntegral_le_log_power hN]

theorem re_major_lower_analytic {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    (((0.997 : ℝ)^2 * ((8 / Real.pi^2) * Decimal.smallRatio * (1 - (3 / 40000 : ℝ)))) -
      (0.997 : ℝ)^2 / 2 * (44 / sourceP N) - 62.04 / sourceP N) * (N : ℝ)^2 +
      (interactionIntegral N).re - errorIntegral N ≤ (majorIntegral N).re := by
  linarith [re_major_lower_mother (exp_2000_le_of_exp_3100_le hN),
    Decimal.re_I11_analytic_lower_bound hN hodd]

theorem re_major_lower_strong {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.65617 * (N : ℝ)^2 + (interactionIntegral N).re -
      6760 * (N : ℝ)^2 / sourceL N^4 ≤ (majorIntegral N).re := by
  linarith [re_major_lower_log_power (exp_2000_le_of_exp_3100_le hN),
    Decimal.re_I11_strong hN hodd]

end LiuWang.Proof.MajorArcApproximation
