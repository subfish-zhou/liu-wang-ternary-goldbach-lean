import LiuWang.Proof.MinorArcEnergy.Fourth

/-!
# 实际 Lambda 三元计数消费者

只替换已付的第四弧；其余三片仍为原核在真实集合上的积分实部。
没有主弧净正假设，也不宣称正计数或降低最终阈值。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.MinorArcEnergy

open Interfaces Parameters ArcGeometry VaughanRecovery AnalyticNumberTheory.LargeSieve

theorem lambdaTripleCount_ge_sub_M4_norm {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    (∫ α in M1 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re +
      (∫ α in M2 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re +
      (∫ α in M3 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re -
      ‖∫ α in M4 N, S N α ^ 3 * charReal (-(N : ℝ) * α)‖ ≤
        lambdaTripleCount N := by
  have h := congrArg Complex.re (circleIntegral_fourArc hN)
  simp only [Complex.add_re, Complex.ofReal_re] at h
  have hr := Complex.re_le_norm
    (-(∫ α in M4 N, S N α ^ 3 * charReal (-(N : ℝ) * α)))
  simp only [Complex.neg_re, norm_neg] at hr
  linarith

theorem lambdaTripleCount_ge_repaid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ α in M1 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re +
      (∫ α in M2 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re +
      (∫ α in M3 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re -
      mother N 0.1741355 3.2354175 0.077006 *
        ∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2 ≤
          lambdaTripleCount N := by
  have h := lambdaTripleCount_ge_sub_M4_norm (exp_2000_le_of_exp_3100_le hN)
  have hb := M4_integral_le_repaid_window hN
  linarith

theorem lambdaTripleCount_ge_explicit {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ α in M1 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re +
      (∫ α in M2 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re +
      (∫ α in M3 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re -
      0.17450916 * (N : ℝ) ^ 2 ≤ lambdaTripleCount N := by
  have h := lambdaTripleCount_ge_sub_M4_norm (exp_2000_le_of_exp_3100_le hN)
  have hb := M4_integral_le_explicit hN
  linarith

end LiuWang.Proof.MinorArcEnergy
