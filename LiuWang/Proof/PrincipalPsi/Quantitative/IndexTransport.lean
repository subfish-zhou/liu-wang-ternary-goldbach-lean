import LiuWang.Proof.PrincipalPsi.Quantitative.HeightSelection
import LiuWang.Proof.PrincipalPsi.CenteredZeros

/-! # xi 闭窗口与原主字符闭窗口的逐值、逐重数有限和运输 -/

set_option autoImplicit false
noncomputable section

open Complex
open Complex.Hadamard
open scoped BigOperators
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.PrincipalPsi.Quantitative

def xiWindowValues (H r : ℝ) : Finset ℂ := by
  classical
  exact (xiWindow H r).image riemannXiDivisorZeroValue

theorem mem_xiWindowValues {H r : ℝ} {rho : ℂ} :
    rho ∈ xiWindowValues H r ↔ riemannXi rho = 0 ∧ |rho.im - H| ≤ r := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    exact ⟨riemannXiDivisorZeroValue_eq_zero p, mem_xiWindow.mp hp⟩
  · rintro ⟨hz, him⟩
    have hr0 : rho ≠ 0 := by intro h; simp [h, riemannXi_zero] at hz
    obtain ⟨p, hp⟩ := BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
      differentiable_riemannXi riemannXi_nontrivial hr0 hz
    exact Finset.mem_image.mpr ⟨p, mem_xiWindow.mpr (by simpa only [hp] using him), hp⟩

theorem xiWindow_fiber_card {H r : ℝ} {rho : ℂ} (hrho : rho ∈ xiWindowValues H r) :
    ((xiWindow H r).filter (fun p => riemannXiDivisorZeroValue p = rho)).card =
      analyticOrderNatAt riemannXi rho := by
  classical
  obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hrho
  have hr0 : rho ≠ 0 := hpv ▸ riemannXiDivisorZeroValue_ne_zero p
  have hf : (xiWindow H r).filter (fun p => riemannXiDivisorZeroValue p = rho) =
      divisorZeroIndex₀_fiberFinset riemannXi rho := by
    ext a
    rw [Finset.mem_filter, mem_xiWindow, mem_divisorZeroIndex₀_fiberFinset]
    change (_ ∧ riemannXiDivisorZeroValue a = rho) ↔ riemannXiDivisorZeroValue a = rho
    refine and_iff_right_of_imp ?_
    intro ha
    simpa only [ha, hpv] using mem_xiWindow.mp hp
  rw [hf, divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt differentiable_riemannXi hr0]

theorem sum_xiWindow_values (H r : ℝ) (f : ℂ → ℂ) :
    ∑ rho ∈ xiWindowValues H r, (analyticOrderNatAt riemannXi rho : ℂ) * f rho =
      ∑ p ∈ xiWindow H r, f (riemannXiDivisorZeroValue p) := by
  classical
  calc
    _ = ∑ rho ∈ xiWindowValues H r,
        ∑ p ∈ (xiWindow H r).filter (fun p => riemannXiDivisorZeroValue p = rho),
          f (riemannXiDivisorZeroValue p) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      simp only [Finset.sum_congr rfl (fun p hp =>
        congrArg f (Finset.mem_filter.mp hp).2), Finset.sum_const, nsmul_eq_mul,
        xiWindow_fiber_card hrho]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) _

def principalClosedValues (T : ℝ) : Finset ℂ := by
  classical
  exact (closedZeroIndices 1 T).image principalZeroValue

theorem principalClosedValues_eq_xiWindowValues (T : ℝ) :
    principalClosedValues T = xiWindowValues 0 T := by
  classical
  ext rho
  rw [mem_xiWindowValues]
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    have hr := mem_closedZeroIndices.mp hp
    refine ⟨(xi_zero_iff_regularized_zero (by linarith [hr.1])).mpr
      (regularizedPrincipal_zero_at_index p), ?_⟩
    simpa using hr.2.2
  · rintro ⟨hz, him⟩
    have hr0 : rho ≠ 0 := by intro h; simp [h, riemannXi_zero] at hz
    obtain ⟨p, hp⟩ := BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
      differentiable_riemannXi riemannXi_nontrivial hr0 hz
    have hr : 0 < rho.re ∧ rho.re < 1 := by
      have hr := riemannXiDivisorZeroValue_re_mem_Ioo p
      change riemannXiDivisorZeroValue p = rho at hp
      simpa only [hp, Set.mem_Ioo] using hr
    have hreg := (xi_zero_iff_regularized_zero (by linarith [hr.1])).mp hz
    obtain ⟨a, ha⟩ := BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1)
      ⟨1, regularizedPrincipal_one_ne_zero 1⟩ hr0 hreg
    refine Finset.mem_image.mpr ⟨a, mem_closedZeroIndices.mpr ?_, ha⟩
    simpa only [show principalZeroValue a = rho from ha] using
      And.intro hr.1 (And.intro hr.2 (by simpa only [sub_zero] using him))

theorem principalClosed_fiber_card {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ principalClosedValues T) :
    ((closedZeroIndices 1 T).filter (fun p => principalZeroValue p = rho)).card =
      analyticOrderNatAt riemannXi rho := by
  classical
  obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hrho
  have hr := mem_closedZeroIndices.mp hp
  have hre : 0 < rho.re := hpv ▸ hr.1
  have hr0 : rho ≠ 0 := by intro h; simp [h] at hre
  have hf : (closedZeroIndices 1 T).filter (fun p => principalZeroValue p = rho) =
      divisorZeroIndex₀_fiberFinset (regularizedPrincipal 1) rho := by
    ext a
    rw [Finset.mem_filter, mem_closedZeroIndices, mem_divisorZeroIndex₀_fiberFinset]
    change (_ ∧ principalZeroValue a = rho) ↔ principalZeroValue a = rho
    refine and_iff_right_of_imp ?_
    intro ha
    simpa only [ha, hpv] using hr
  rw [hf, divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1) hr0,
    analyticOrderNatAt_xi_eq_regularized (by linarith)]

theorem sum_principal_closed_eq_xi (T : ℝ) (f : ℂ → ℂ) :
    ∑ p ∈ closedZeroIndices 1 T, f (principalZeroValue p) =
      ∑ p ∈ xiWindow 0 T, f (riemannXiDivisorZeroValue p) := by
  classical
  calc
    _ = ∑ rho ∈ principalClosedValues T,
        ∑ p ∈ (closedZeroIndices 1 T).filter (fun p => principalZeroValue p = rho),
          f (principalZeroValue p) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) _).symm
    _ = ∑ rho ∈ principalClosedValues T, (analyticOrderNatAt riemannXi rho : ℂ) * f rho := by
      apply Finset.sum_congr rfl
      intro rho hrho
      simp only [Finset.sum_congr rfl (fun p hp =>
        congrArg f (Finset.mem_filter.mp hp).2), Finset.sum_const, nsmul_eq_mul,
        principalClosed_fiber_card hrho]
    _ = _ := by rw [principalClosedValues_eq_xiWindowValues, sum_xiWindow_values]

theorem card_principal_closed_eq_xi (T : ℝ) :
    (closedZeroIndices 1 T).card = (xiWindow 0 T).card := by
  have h := sum_principal_closed_eq_xi T (fun _ => 1)
  simpa using h

theorem principal_closed_card_le {T : ℝ} (hT : 0 ≤ T) :
    ((closedZeroIndices 1 T).card : ℝ) ≤ (2 / 3) * T ^ 2 := by
  rw [card_principal_closed_eq_xi]
  exact xiWindow_total_card_le hT

theorem norm_closedCentered_sub_high_le {t T : ℝ} (ht : 2.5 ≤ t) (hT : 0 ≤ T) :
    ‖closedCenteredZeroSum 1 t T - highZeroSum 1 t T‖ ≤
      (2 * Real.sqrt t + 5) * ((2 / 3) * T ^ 2) := by
  classical
  have hc := principal_closed_card_le hT
  have hl : ((lowZeroIndices 1 T).card : ℝ) ≤ (2 / 3) * T ^ 2 :=
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))).trans hc
  have hh : ((highZeroIndices 1 T).card : ℝ) ≤ (2 / 3) * T ^ 2 :=
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))).trans hc
  exact (norm_closedCentered_sub_high_le_card 1 ht T).trans
    ((add_le_add (mul_le_mul_of_nonneg_left hl (by positivity))
      (mul_le_mul_of_nonneg_left hh (by norm_num))).trans_eq (by ring))

end LiuWang.Proof.PrincipalPsi.Quantitative
