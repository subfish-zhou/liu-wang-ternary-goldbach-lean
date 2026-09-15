import LiuWang.Proof.ExceptionalZeroGap.Main

set_option autoImplicit false

namespace LiuWang.Proof.ExceptionalZeroGap

theorem derivative_interval_consumer {r : ℕ} [NeZero r]
    (χ : Interfaces.Character r) (hr : 987 ≤ r) (hχ : χ.IsPrimitive)
    {x : ℝ} (hx : 10 ≤ x) (hrx : (r : ℝ) ≤ x) :
    ∀ σ ∈ Set.Icc (1 - 1 / (9.645908801 * Real.log x)) 1,
      ‖deriv χ.LFunction (σ : ℂ)‖ ≤ 0.4923 * (Real.log r) ^ 2 := by
  intro σ hσ
  exact norm_deriv_LFunction_le hχ hr hx hrx hσ.1 hσ.2

theorem large_conductor_local_zero_consumer {r : ℕ} [NeZero r]
    (χ : Interfaces.Character r) (hr : 987 ≤ r) (hχ : χ.IsPrimitive)
    (hreal : ∀ a : ZMod r, (χ a).im = 0) {x β : ℝ}
    (hx : 10 ≤ x) (hrx : (r : ℝ) ≤ x)
    (hβ : 1 - 1 / (9.645908801 * Real.log x) ≤ β)
    (hzero : χ.LFunction (β : ℂ) = 0) :
    β < 1 ∧ Real.pi / (0.4923 * Real.sqrt r * (Real.log r) ^ 2) ≤ 1 - β :=
  ⟨real_zero_lt_one hχ hr hzero,
    real_primitive_local_zero_gap hχ hr hreal hx hrx hβ hzero⟩

end LiuWang.Proof.ExceptionalZeroGap
