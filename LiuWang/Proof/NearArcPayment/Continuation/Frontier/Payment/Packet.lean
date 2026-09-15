import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Kernels

/-! 一次全字符近一计数支付两个振荡分支的并集，不把 14000 按字符重复使用。 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment

open Interfaces Parameters CompleteExpansion CharacterExpansion

def densityPacket (q : ℕ) [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ densityValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

def residualPacket (q : ℕ) [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ residualValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem tailPacket_eq_density_add_residual {q : ℕ} [NeZero q]
    (N a : ℕ) (positive : Bool) (eta : ℝ) :
    tailPacket q N a positive eta =
      densityPacket q N a positive eta + residualPacket q N a positive eta := by
  unfold tailPacket densityPacket residualPacket densityValues residualValues
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hh : densityAlpha N ≤ rho.re ∧
      (sourceL N ^ 6 ≤ |rho.im| ∨
        (sourceL N ^ 4 ≤ |rho.im| ∧ if positive then 0 < rho.im else rho.im < 0)) <;> simp [hh]

def gaussDensityMass (q : ℕ) [NeZero q] (N a : ℕ) (positive : Bool) : ℝ :=
  (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
    (∑ rho ∈ densityValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ))

theorem norm_densityPacket_le_mass {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {positive : Bool} {eta : ℝ}
    (he : if positive then 0 ≤ eta else eta ≤ 0) :
    ‖densityPacket q N a positive eta‖ ≤
      (20 * (N : ℝ) / sourceL N ^ 3) * gaussDensityMass q N a positive := by
  have hc (chi : Character q) :
      ‖∑ rho ∈ densityValues chi N positive,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      (∑ rho ∈ densityValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ)) *
        (20 * (N : ℝ) / sourceL N ^ 3) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro rho hr
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (Jrho_density_paid hN hr he) (Nat.cast_nonneg _)
  unfold densityPacket gaussDensityMass
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
        ((∑ rho ∈ densityValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ)) *
          (20 * (N : ℝ) / sourceL N ^ 3)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro chi _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hc chi) (norm_nonneg _)
    _ = _ := by simp only [← mul_assoc, ← Finset.sum_mul]; ring

theorem norm_G_le_totient {q : ℕ} [NeZero q] (a : ℕ) (chi : Character q) :
    ‖G a chi‖ ≤ (q.totient : ℝ) := by
  have hh : ‖G a chi‖ ^ 2 ≤ ∑ chi : Character q, ‖G a chi‖ ^ 2 :=
    Finset.single_le_sum (f := fun chi : Character q => ‖G a chi‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ chi)
  rw [NonprincipalPacket.gauss_energy] at hh
  nlinarith [norm_nonneg (G a chi), Nat.cast_nonneg (α := ℝ) q.totient]

theorem gaussDensityMass_le_count {q : ℕ} [NeZero q] (N a : ℕ) (positive : Bool) :
    gaussDensityMass q N a positive ≤
      ∑ chi : Character q, ∑ rho ∈ densityValues chi N positive,
        (analyticOrderNatAt chi.LFunction rho : ℝ) := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  unfold gaussDensityMass
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, (q.totient : ℝ) *
        (∑ rho ∈ densityValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro chi _
      exact mul_le_mul_of_nonneg_right (norm_G_le_totient a chi)
        (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
    _ = _ := by rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

theorem gaussDensityMass_le_sharp {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (positive : Bool) :
    gaussDensityMass q N a positive ≤
      (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
        sharpCount chi (sourceT N) := by
  unfold gaussDensityMass
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro chi _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply le_trans _ (complete_count_le_sharp chi (sourceT_pos hN).le)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    ((densityValues_subset chi positive).trans (Finset.filter_subset _ _))
    (fun _ _ _ => Nat.cast_nonneg _)

theorem gaussDensityMass_le_min {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (positive : Bool) :
    gaussDensityMass q N a positive ≤ min 14000
      ((q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
        sharpCount chi (sourceT N)) :=
  le_min ((gaussDensityMass_le_count N a positive).trans (density_count_le_row hN hq positive))
    (gaussDensityMass_le_sharp hN positive)

theorem norm_densityPacket_le_polynomial {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {positive : Bool} {eta : ℝ} (he : if positive then 0 ≤ eta else eta ≤ 0) :
    ‖densityPacket q N a positive eta‖ ≤ 280000 * (N : ℝ) / sourceL N ^ 3 := by
  have hL := sourceL_pos hN
  apply (norm_densityPacket_le_mass hN he).trans
  calc
    _ ≤ (20 * (N : ℝ) / sourceL N ^ 3) * 14000 :=
      mul_le_mul_of_nonneg_left
        ((gaussDensityMass_le_count N a positive).trans (density_count_le_row hN hq positive))
        (by positivity)
    _ = _ := by ring

theorem norm_densityPacket_le_paid {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {positive : Bool} {eta : ℝ} (he : if positive then 0 ≤ eta else eta ≤ 0) :
    ‖densityPacket q N a positive eta‖ ≤ 0.03 * (N : ℝ) / sourceL N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hp : (280000 : ℝ) ≤ 0.03 * sourceL N ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) (sourceL_ge_3100 hN) 2
    norm_num at hh
    linarith
  apply (norm_densityPacket_le_polynomial hN0 hq he).trans
  rw [show sourceL N ^ 3 = sourceL N ^ 2 * sourceL N by ring, div_mul_eq_div_div]
  apply div_le_div_of_nonneg_right _ hL.le
  apply (div_le_iff₀ (pow_pos hL 2)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) N)]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment
