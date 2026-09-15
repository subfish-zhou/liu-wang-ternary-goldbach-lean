import LiuWang.Proof.CompleteExpansion.Consumer
import LiuWang.Proof.SingularSeries.MainTerm
import LiuWang.Proof.ArcGeometry.Main

/-! # 真实零点模型、连续性与不估零点包的三次差 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.MajorArcApproximation

def model (N a q : ℕ) (eta : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    principalCoefficient q * J N eta - zeroPacket q N a eta

theorem model_eq {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    model N a q eta = principalCoefficient q * J N eta - zeroPacket q N a eta := by
  simp only [model, dif_neg (NeZero.ne q)]

theorem continuous_J {N : ℕ} (hN : 0 < N) : Continuous (J N) := by
  have he : J N = Jrho N 1 := by
    funext eta
    simp [J, Jrho]
  rw [he]
  exact SingularIntegral.Jrho_continuous hN 1

theorem continuous_zeroPacket {N q : ℕ} [NeZero q] (hN : 0 < N) (a : ℕ) :
    Continuous (zeroPacket q N a) := by
  unfold zeroPacket PrincipalExpansion.zeroSum NonprincipalPacket.Znp
  apply Continuous.add
  · exact continuous_const.mul (continuous_finsetSum _ (fun p _ =>
      SingularIntegral.Jrho_continuous hN _))
  · exact continuous_const.mul (continuous_finsetSum _ (fun chi _ =>
      continuous_const.mul (continuous_finsetSum _ (fun p _ =>
        SingularIntegral.Jrho_continuous hN _))))

theorem continuous_model {N : ℕ} (hN : 0 < N) (a q : ℕ) :
    Continuous (model N a q) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℂ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (model_eq N a)]
    exact (continuous_const.mul (continuous_J hN)).sub (continuous_zeroPacket hN a)

theorem norm_S_le_psi (N : ℕ) (alpha : ℝ) : ‖S N alpha‖ ≤ Chebyshev.psi (N : ℝ) := by
  rw [S_eq_closed_sum]
  apply (norm_sum_le _ _).trans
  have hs : windowFinset N ⊆ Finset.Icc 0 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, ((mem_windowFinset_iff N n).mp hn).1⟩
  calc
    _ = ∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_congr rfl
      intro n _
      simp [SingularIntegral.charReal_norm, abs_of_nonneg
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
    _ ≤ ∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = _ := by
      rw [Chebyshev.psi, Nat.floor_natCast]
      symm
      apply Finset.sum_subset (by intro n hn; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢; omega)
      intro n hn hn'
      have hn0 : n = 0 := by
        simp only [Finset.mem_Icc, Finset.mem_Ioc] at hn hn'
        omega
      simp [hn0]

theorem norm_S_le_seven (N : ℕ) (alpha : ℝ) : ‖S N alpha‖ ≤ 7 * (N : ℝ) := by
  apply (norm_S_le_psi N alpha).trans
  apply (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)).trans
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg N)

theorem norm_S_sub_model {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - model N a q eta‖ ≤ errorBound q N a eta := by
  rw [model_eq, sub_sub_eq_add_sub]
  rw [add_sub_right_comm]
  exact complete_error_function hN hi hq eta

def cubicCost (B epsilon : ℝ) : ℝ :=
  epsilon * (3 * B^2 + 3 * B * epsilon + epsilon^2)

theorem norm_cube_sub_le {s f : ℂ} {B epsilon : ℝ}
    (hB : 0 ≤ B) (_he : 0 ≤ epsilon) (hs : ‖s‖ ≤ B) (hr : ‖s - f‖ ≤ epsilon) :
    ‖s^3 - f^3‖ ≤ cubicCost B epsilon := by
  have hid : s^3 - f^3 = 3*s^2*(s-f) - 3*s*(s-f)^2 + (s-f)^3 := by ring
  rw [hid]
  apply ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans
  simp only [norm_mul, norm_pow, show ‖(3 : ℂ)‖ = (3 : ℝ) by norm_num]
  calc
    _ ≤ 3*B^2*epsilon + 3*B*epsilon^2 + epsilon^3 := by gcongr
    _ = _ := by unfold cubicCost; ring

theorem cubicCost_nonneg {B epsilon : ℝ} (hB : 0 ≤ B) (he : 0 ≤ epsilon) :
    0 ≤ cubicCost B epsilon := by unfold cubicCost; positivity

theorem cubicCost_mono {B C e d : ℝ} (hB : 0 ≤ B) (he : 0 ≤ e)
    (hBC : B ≤ C) (hed : e ≤ d) : cubicCost B e ≤ cubicCost C d := by
  unfold cubicCost
  have hC := hB.trans hBC
  have hd := he.trans hed
  gcongr

def arcPhase (N a q : ℕ) (eta : ℝ) : ℂ :=
  charReal (-(N : ℝ) * (rationalCenter a q + eta))

theorem continuous_arcPhase (N a q : ℕ) : Continuous (arcPhase N a q) := by
  unfold arcPhase charReal
  fun_prop

theorem norm_arcPhase (N a q : ℕ) (eta : ℝ) : ‖arcPhase N a q eta‖ = 1 :=
  SingularIntegral.charReal_norm _

theorem model_cube_integrable {N : ℕ} (hN : 0 < N) (a q : ℕ) (l r : ℝ) :
    IntervalIntegrable (fun eta => model N a q eta^3 * arcPhase N a q eta) volume l r :=
  (((continuous_model hN a q).pow 3).mul (continuous_arcPhase N a q)).intervalIntegrable l r

end LiuWang.Proof.MajorArcApproximation
