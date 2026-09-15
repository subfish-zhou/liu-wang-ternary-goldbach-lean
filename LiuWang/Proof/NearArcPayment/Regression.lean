import LiuWang.Proof.NearArcPayment.Integral

/-! Boundary, modulus-one and same-witness regression checks. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment

open Interfaces Parameters ArcGeometry CompleteExpansion CharacterExpansion

theorem kernelBill_neg (N : ℕ) (rho : ℂ) (eta : ℝ) :
    kernelBill N rho (-eta) = kernelBill N rho eta := by
  simp only [kernelBill, abs_neg, realKernel, farKernel]

theorem kernelBill_real {rho : ℂ} (hg : rho.im = 0) (N : ℕ) (eta : ℝ) :
    kernelBill N rho eta = min (weightKernel N rho) (realKernel N rho eta) := by
  simp only [kernelBill, hg, ↓reduceIte]

theorem kernelBill_lower_boundary {N : ℕ} (hN : 0 < N)
    {rho : ℂ} (hg : rho.im ≠ 0) :
    kernelBill N rho (|rho.im| / (10 * Real.pi * (N : ℝ))) =
      min (weightKernel N rho) (min (sqrtKernel N rho) (nearKernel N rho)) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  simp only [kernelBill, hg, ↓reduceIte, abs_of_nonneg (by positivity :
    0 ≤ |rho.im| / (10 * Real.pi * (N : ℝ))), le_refl]

theorem kernelBill_upper_boundary {N : ℕ} (hN : 0 < N)
    {rho : ℂ} (hg : rho.im ≠ 0) :
    kernelBill N rho (|rho.im| / (0.001 * Real.pi * (N : ℝ))) =
      min (weightKernel N rho) (min (sqrtKernel N rho)
        (farKernel N rho (|rho.im| / (0.001 * Real.pi * (N : ℝ))))) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hh : |rho.im| / (10 * Real.pi * (N : ℝ)) <
      |rho.im| / (0.001 * Real.pi * (N : ℝ)) :=
    div_lt_div_of_pos_left (abs_pos.mpr hg) (by positivity)
      (by nlinarith [mul_pos Real.pi_pos hn])
  simp only [kernelBill, hg, ↓reduceIte, abs_of_nonneg (by positivity :
    0 ≤ |rho.im| / (0.001 * Real.pi * (N : ℝ))), not_le.mpr hh, le_refl]

theorem zeroBill_one (N a : ℕ) (eta : ℝ) :
    zeroBill 1 N a eta =
      ∑ rho ∈ zeroValues (1 : Character 1) (sourceT N),
        (analyticOrderNatAt (1 : Character 1).LFunction rho : ℝ) *
          kernelBill N rho eta := by
  unfold zeroBill
  rw [Fintype.sum_subsingleton _ (1 : Character 1),
    NonprincipalPacket.G_one_eq_moebius (Nat.coprime_one_right a)]
  simp

theorem shell_eta_nonzero {N a q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) {alpha : ℝ} (ha : alpha ∈ shell N a q) :
    alpha - rationalCenter a q ≠ 0 :=
  abs_pos.mp ((deltaRadius_pos hN (sourceIndex_den_pos hi)).trans (shell_same_eta hq hi ha).1)

theorem principal_modulus_one {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {eta : ℝ} (he : deltaRadius N 1 < |eta|) :
    ‖J N eta‖ ≤ (10 / 3.36) * (N : ℝ) / sourceL N ^ 3 := by
  simpa only [principalCoefficient_one, one_mul, principalPayment, principalMass_one,
    Nat.cast_one, mul_one, sourceP] using principal_payment hN (by norm_num) he

end LiuWang.Proof.NearArcPayment
