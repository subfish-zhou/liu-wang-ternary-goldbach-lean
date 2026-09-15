import LiuWang.Proof.CompleteExpansion.Budget

/-! # 通过真实普通 L 值集合统一主/非主闭窗，不识别不同索引 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.FixedHeightZeroSum
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.CompleteExpansion

theorem nonprincipal_zero_window {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {T : ℝ} {rho : ℂ} :
    rho ∈ NonprincipalPsi.highZeroValues chi T ↔
      chi.LFunction rho = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧
        |rho.im| ≤ T ∧ 1 / 2 ≤ rho.re := by
  constructor
  · intro h
    obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp h
    have hparts := (NonprincipalPsi.mem_highZeroIndices_nonprincipal hchi T p).mp hp
    have hre : 0 < (completedZeroValue p).re := by linarith [hparts.2]
    have hz : chi.LFunction rho = 0 := by
      apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
      rw [← NonprincipalPsi.highZeroFiber_card hchi h]
      exact (Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpv⟩⟩).ne'
    refine ⟨hz, ?_, ?_, ?_, ?_⟩
    · simpa only [hpv] using hre
    · simpa only [hpv] using NonprincipalPsi.completedZeroValue_re_lt_one_of_pos hchi p hre
    · simpa only [hpv] using hparts.1
    · simpa only [hpv] using hparts.2
  · rintro ⟨hz, hre, _, hheight, hhalf⟩
    have hr0 : rho ≠ 0 := by intro h; simp [h] at hre
    have hcomp : symmetricCompletedLFunction chi rho = 0 := by
      rw [symmetricCompletedLFunction,
        DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos chi hre,
        hz, zero_mul, mul_zero]
    obtain ⟨p, hp⟩ := BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
      (differentiable_symmetricCompletedLFunction hchi)
      ⟨2, symmetricCompletedLFunction_two_ne_zero hchi⟩ hr0 hcomp
    change completedZeroValue p = rho at hp
    exact Finset.mem_image.mpr ⟨p,
      (NonprincipalPsi.mem_highZeroIndices_nonprincipal hchi T p).mpr
        (by simpa only [hp] using ⟨hheight, hhalf⟩), hp⟩

def zeroValues {q : ℕ} [NeZero q] (chi : Character q) (T : ℝ) : Finset ℂ :=
  if chi = 1 then PrincipalPsi.highZeroValues q T else NonprincipalPsi.highZeroValues chi T

theorem mem_zeroValues {q : ℕ} [NeZero q] {chi : Character q} {T : ℝ} {rho : ℂ} :
    rho ∈ zeroValues chi T ↔
      chi.LFunction rho = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧
        |rho.im| ≤ T ∧ 1 / 2 ≤ rho.re := by
  by_cases hc : chi = 1
  · subst chi
    simpa only [zeroValues, ↓reduceIte] using
      (PrincipalPsi.mem_highZeroValues (q := q) (T := T) (rho := rho))
  · simpa only [zeroValues, if_neg hc] using
      (nonprincipal_zero_window hc (T := T) (rho := rho))

theorem zeroValues_pole_excluded {q : ℕ} [NeZero q] (chi : Character q) (T : ℝ) :
    (1 : ℂ) ∉ zeroValues chi T := by
  intro h
  have hh := (mem_zeroValues.mp h).2.2.1
  norm_num at hh

def zeroValueSum {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (T eta : ℝ) : ℂ :=
  ∑ rho ∈ zeroValues chi T, (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem zeroValueSum_principal (q : ℕ) [NeZero q] (N : ℕ) (T eta : ℝ) :
    zeroValueSum (1 : Character q) N T eta = PrincipalExpansion.zeroSum q N T eta := by
  rw [PrincipalExpansion.zeroSum_eq_values]
  simp only [zeroValueSum, zeroValues, ↓reduceIte]

theorem zeroValueSum_nonprincipal {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (N : ℕ) (T eta : ℝ) :
    zeroValueSum chi N T eta =
      ∑ p ∈ highZeroIndices chi T, Jrho N (completedZeroValue p) eta := by
  simp only [zeroValueSum, zeroValues, if_neg hchi]
  exact NonprincipalPsi.sum_highZeroValues_multiplicity hchi T (fun rho => Jrho N rho eta)

theorem zeroPacket_eq_all_values {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ)
    (haq : Nat.Coprime a q) :
    zeroPacket q N a eta =
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi * zeroValueSum chi N (sourceT N) eta := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Character q)),
    zeroValueSum_principal, NonprincipalPacket.G_one_eq_moebius haq]
  have hnp :
      (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
        G a chi * zeroValueSum chi N (sourceT N) eta) =
      NonprincipalPacket.Znp (q := q) N a eta := by
    apply Finset.sum_congr rfl
    intro chi hc
    rw [zeroValueSum_nonprincipal (Finset.mem_erase.mp hc).1]
  rw [hnp]
  unfold zeroPacket principalCoefficient
  ring

theorem zeroValues_eq_literal {q : ℕ} [NeZero q] (chi : Character q) (T : ℝ) :
    (zeroValues chi T : Set ℂ) =
      {rho | chi.LFunction rho = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧
        |rho.im| ≤ T ∧ 1 / 2 ≤ rho.re} := by
  ext rho
  exact mem_zeroValues

theorem zeroPacket_values_one (N a : ℕ) (eta : ℝ) :
    (Nat.totient 1 : ℂ)⁻¹ *
      (∑ chi : Character 1, G a chi * zeroValueSum chi N (sourceT N) eta) =
      PrincipalExpansion.zeroSum 1 N (sourceT N) eta := by
  rw [← zeroPacket_eq_all_values N a eta (Nat.coprime_one_right a), zeroPacket_one]

end LiuWang.Proof.CompleteExpansion
