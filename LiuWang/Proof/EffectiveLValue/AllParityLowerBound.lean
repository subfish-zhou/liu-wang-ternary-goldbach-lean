import LiuWang.Proof.EffectiveLValue.EvenEffectiveBound
import LiuWang.Proof.EffectiveLValue.OddEffectiveBound

/-!
# The lower bound for every real primitive character

The even branch uses the original cyclotomic product's integral Pell equation;
the odd branch is the existing integral-moment theorem, without changes.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

theorem real_primitive_LFunction_one_lower {r : ℕ} [NeZero r]
    (χ : Interfaces.Character r) (hr : 987 ≤ r) (hprimitive : χ.IsPrimitive)
    (hreal : ∀ a : ZMod r, (χ a).im = 0) :
    Real.pi / Real.sqrt (r : ℝ) ≤ (χ.LFunction 1).re := by
  rcases χ.even_or_odd with heven | hodd
  · exact even_real_primitive_LFunction_one_lower χ hr hprimitive hreal heven
  · exact odd_real_primitive_LFunction_one_lower χ hr hprimitive hreal hodd

end LiuWang.Proof.EffectiveLValue
