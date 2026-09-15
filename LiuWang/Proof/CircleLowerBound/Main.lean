import LiuWang.Proof.MajorArcApproximation.Consumer
import LiuWang.Proof.MinorArcEnergy.Consumer

/-! # 实际三元计数的主弧与第四弧合账

仅合并已付主弧近似误差与第四弧费用。零点相互作用、M2、M3 的实部
原样保留；这里没有净正结论，也没有把 Lambda 计数替换成素数表示数。
母界与小数界是替代出口，不相加支付。共享次弧能量的另一路账本不在此重复使用。
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.SingularSeries
namespace LiuWang.Proof.CircleLowerBound

theorem lambdaTripleCount_ge_mother {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (I11 N).re + (interactionIntegral N).re - errorIntegral N +
      (∫ α in M2 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re +
      (∫ α in M3 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re -
      VaughanRecovery.mother N 0.1741355 3.2354175 0.077006 *
        ∑ n ∈ windowFinset N, ArithmeticFunction.vonMangoldt n ^ 2 ≤
      lambdaTripleCount N := by
  have hmajor := re_major_lower_mother (exp_2000_le_of_exp_3100_le hN)
  have hminor := MinorArcEnergy.lambdaTripleCount_ge_repaid hN
  simp only [majorIntegral] at hmajor
  linarith

theorem lambdaTripleCount_ge_strong {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hodd : Odd N) :
    0.48166084 * (N : ℝ) ^ 2 + (interactionIntegral N).re +
      (∫ α in M2 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re +
      (∫ α in M3 N, S N α ^ 3 * charReal (-(N : ℝ) * α)).re -
      6760 * (N : ℝ) ^ 2 / sourceL N ^ 4 ≤ lambdaTripleCount N := by
  have hmajor := major_arc_re_strong hN hodd
  have hminor := MinorArcEnergy.lambdaTripleCount_ge_explicit hN
  linarith

end LiuWang.Proof.CircleLowerBound
