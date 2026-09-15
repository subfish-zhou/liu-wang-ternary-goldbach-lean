import LiuWang.Proof.EffectiveLValue.OddEffectiveBound

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue.OddConsumer

variable {r : ℕ} [NeZero r]

theorem actual_odd_branch (χ : Interfaces.Character r) (hr : 987 ≤ r)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod r, (χ a).im = 0) (hodd : χ.Odd) :
    Real.pi / Real.sqrt (r : ℝ) ≤ (χ.LFunction 1).re :=
  odd_real_primitive_LFunction_one_lower χ hr hprimitive hreal hodd

theorem scaled_odd_branch (χ : Interfaces.Character r) (hr : 987 ≤ r)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod r, (χ a).im = 0) (hodd : χ.Odd) :
    Real.pi ≤ Real.sqrt (r : ℝ) * (χ.LFunction 1).re := by
  have hs : 0 < Real.sqrt (r : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos r)
  simpa only [mul_comm] using (div_le_iff₀ hs).mp
    (actual_odd_branch χ hr hprimitive hreal hodd)

theorem cutoff_987 (χ : Interfaces.Character 987) (hprimitive : χ.IsPrimitive)
    (hreal : ∀ a : ZMod 987, (χ a).im = 0) (hodd : χ.Odd) :
    Real.pi / Real.sqrt (987 : ℝ) ≤ (χ.LFunction 1).re :=
  actual_odd_branch χ (by norm_num) hprimitive hreal hodd

end LiuWang.Proof.EffectiveLValue.OddConsumer
