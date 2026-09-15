import LiuWang.Proof.PrincipalPsi.EulerTransport
import BombieriVinogradov.Helpers.ComplexAnalysis.DivisorZeroIndex
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber

/-!
# 主字符的闭高度真实零点和

使用去极点整函数的规范除子索引，再显式限制 `0 < Re ρ < 1`。
闭高度包含端点，临界线归入高实部；普通 L 函数的实际重数由纤维基数给出。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Complex.Hadamard

namespace LiuWang.Proof.PrincipalPsi

abbrev PrincipalZeroIndex (q : ℕ) [NeZero q] :=
  divisorZeroIndex₀ (regularizedPrincipal q) (Set.univ : Set ℂ)

abbrev principalZeroValue {q : ℕ} [NeZero q] (p : PrincipalZeroIndex q) : ℂ :=
  divisorZeroIndex₀_val p

theorem regularizedPrincipal_zero_at_index {q : ℕ} [NeZero q]
    (p : PrincipalZeroIndex q) :
    regularizedPrincipal q (principalZeroValue p) = 0 := by
  apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
  intro h
  have hsupport := divisorZeroIndex₀_val_mem_divisor_support p
  rw [divisor_univ_eq_analyticOrderNatAt_int
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ q), h] at hsupport
  exact hsupport (by simp)

theorem principalZeroValue_ne_one {q : ℕ} [NeZero q] (p : PrincipalZeroIndex q) :
    principalZeroValue p ≠ 1 := by
  intro h
  exact regularizedPrincipal_one_ne_zero q (h ▸ regularizedPrincipal_zero_at_index p)

theorem principal_zero_at_index {q : ℕ} [NeZero q] (p : PrincipalZeroIndex q) :
    (1 : DirichletCharacter ℂ q).LFunction (principalZeroValue p) = 0 := by
  have h := regularizedPrincipal_zero_at_index p
  rw [regularizedPrincipal_eq (principalZeroValue_ne_one p)] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (principalZeroValue_ne_one p))

def closedZeroSet (q : ℕ) [NeZero q] (T : ℝ) : Set (PrincipalZeroIndex q) :=
  {p | 0 < (principalZeroValue p).re ∧ (principalZeroValue p).re < 1 ∧
    |(principalZeroValue p).im| ≤ T}

theorem closedZeroSet_finite (q : ℕ) [NeZero q] (T : ℝ) :
    (closedZeroSet q T).Finite := by
  apply (divisorZeroIndex₀_norm_le_finite
    (f := regularizedPrincipal q) (U := Set.univ) (B := |T| + 2) (by simp)).subset
  rintro p ⟨hre, hre1, him⟩
  have hrabs : |(principalZeroValue p).re| ≤ 1 := by
    rw [abs_of_pos hre]
    exact hre1.le
  have hiabs : |(principalZeroValue p).im| ≤ |T| := him.trans (le_abs_self T)
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

def closedZeroIndices (q : ℕ) [NeZero q] (T : ℝ) : Finset (PrincipalZeroIndex q) :=
  (closedZeroSet_finite q T).toFinset

theorem mem_closedZeroIndices {q : ℕ} [NeZero q] {T : ℝ} {p : PrincipalZeroIndex q} :
    p ∈ closedZeroIndices q T ↔
      0 < (principalZeroValue p).re ∧ (principalZeroValue p).re < 1 ∧
        |(principalZeroValue p).im| ≤ T := by
  simp [closedZeroIndices, closedZeroSet]

def highZeroIndices (q : ℕ) [NeZero q] (T : ℝ) : Finset (PrincipalZeroIndex q) := by
  classical
  exact (closedZeroIndices q T).filter (fun p => 1 / 2 ≤ (principalZeroValue p).re)

def lowZeroIndices (q : ℕ) [NeZero q] (T : ℝ) : Finset (PrincipalZeroIndex q) := by
  classical
  exact (closedZeroIndices q T).filter (fun p => (principalZeroValue p).re < 1 / 2)

theorem mem_highZeroIndices {q : ℕ} [NeZero q] {T : ℝ} {p : PrincipalZeroIndex q} :
    p ∈ highZeroIndices q T ↔
      (0 < (principalZeroValue p).re ∧ (principalZeroValue p).re < 1 ∧
        |(principalZeroValue p).im| ≤ T) ∧ 1 / 2 ≤ (principalZeroValue p).re := by
  classical
  simp only [highZeroIndices, Finset.mem_filter, mem_closedZeroIndices]

theorem sum_closed_eq_low_add_high (q : ℕ) [NeZero q] (T : ℝ)
    (f : PrincipalZeroIndex q → ℂ) :
    ∑ p ∈ closedZeroIndices q T, f p =
      (∑ p ∈ lowZeroIndices q T, f p) + ∑ p ∈ highZeroIndices q T, f p := by
  classical
  simpa only [lowZeroIndices, highZeroIndices, not_lt] using
    (Finset.sum_filter_add_sum_filter_not (closedZeroIndices q T)
      (fun p => (principalZeroValue p).re < 1 / 2) f).symm

def highZeroValues (q : ℕ) [NeZero q] (T : ℝ) : Finset ℂ := by
  classical
  exact (highZeroIndices q T).image principalZeroValue

theorem mem_highZeroValues {q : ℕ} [NeZero q] {T : ℝ} {rho : ℂ} :
    rho ∈ highZeroValues q T ↔
      (1 : DirichletCharacter ℂ q).LFunction rho = 0 ∧
        0 < rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ T ∧ 1 / 2 ≤ rho.re := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    have hm := mem_highZeroIndices.mp hp
    exact ⟨principal_zero_at_index p, hm.1.1, hm.1.2.1, hm.1.2.2, hm.2⟩
  · rintro ⟨hzero, hre, hre1, him, hhigh⟩
    have hr0 : rho ≠ 0 := by intro h; simp [h] at hre
    have hr1 : rho ≠ 1 := by intro h; simp [h] at hre1
    have hreg : regularizedPrincipal q rho = 0 := by
      rw [regularizedPrincipal_eq hr1, hzero, mul_zero]
    obtain ⟨p, hp⟩ := BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q)
      ⟨1, regularizedPrincipal_one_ne_zero q⟩ hr0 hreg
    exact Finset.mem_image.mpr ⟨p, mem_highZeroIndices.mpr (by
      simpa only [show principalZeroValue p = rho from hp] using
        And.intro ⟨hre, hre1, him⟩ hhigh), hp⟩

theorem highZeroValues_eq_zeta (q : ℕ) [NeZero q] (T : ℝ) :
    highZeroValues q T = highZeroValues 1 T := by
  ext rho
  rw [mem_highZeroValues, mem_highZeroValues, DirichletCharacter.LFunction_modOne_eq]
  by_cases hre : 0 < rho.re
  · by_cases hre1 : rho.re < 1
    · have hr1 : rho ≠ 1 := by intro h; simp [h] at hre1
      rw [principal_zero_iff_zeta_zero hre hr1]
    · simp [hre1]
  · simp [hre]

theorem highZeroFiber_card {q : ℕ} [NeZero q] {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ highZeroValues q T) :
    ((highZeroIndices q T).filter (fun p => principalZeroValue p = rho)).card =
      analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction rho := by
  classical
  have hr := mem_highZeroValues.mp hrho
  have hr0 : rho ≠ 0 := by intro h; simp [h] at hr
  have hr1 : rho ≠ 1 := by intro h; simp [h] at hr
  have hf : (highZeroIndices q T).filter (fun p => principalZeroValue p = rho) =
      divisorZeroIndex₀_fiberFinset (regularizedPrincipal q) rho := by
    ext p
    rw [Finset.mem_filter, mem_highZeroIndices, mem_divisorZeroIndex₀_fiberFinset]
    change (_ ∧ principalZeroValue p = rho) ↔ principalZeroValue p = rho
    refine and_iff_right_of_imp ?_
    intro h
    simpa only [h] using And.intro ⟨hr.2.1, hr.2.2.1, hr.2.2.2.1⟩ hr.2.2.2.2
  rw [hf, divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ q) hr0,
    analyticOrderNatAt_regularized_eq_principal hr1]

theorem sum_highZeroValues_multiplicity (q : ℕ) [NeZero q] (T : ℝ) (f : ℂ → ℂ) :
    ∑ rho ∈ highZeroValues q T,
        (analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction rho : ℂ) * f rho =
      ∑ p ∈ highZeroIndices q T, f (principalZeroValue p) := by
  classical
  calc
    _ = ∑ rho ∈ highZeroValues q T,
        ∑ p ∈ (highZeroIndices q T).filter (fun p => principalZeroValue p = rho),
          f (principalZeroValue p) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      simp only [Finset.sum_congr rfl (fun p hp =>
        congrArg f (Finset.mem_filter.mp hp).2), Finset.sum_const, nsmul_eq_mul,
        highZeroFiber_card hrho]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) _

def highZeroSum (q : ℕ) [NeZero q] (t T : ℝ) : ℂ :=
  ∑ p ∈ highZeroIndices q T, (t : ℂ) ^ principalZeroValue p / principalZeroValue p

theorem highZeroSum_eq_zeta (q : ℕ) [NeZero q] (t T : ℝ) :
    highZeroSum q t T = highZeroSum 1 t T := by
  unfold highZeroSum
  rw [← sum_highZeroValues_multiplicity q T (fun rho => (t : ℂ) ^ rho / rho),
    ← sum_highZeroValues_multiplicity 1 T (fun rho => (t : ℂ) ^ rho / rho),
    highZeroValues_eq_zeta]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hr := mem_highZeroValues.mp hrho
  have hr1 : rho ≠ 1 := by intro h; simp [h] at hr
  rw [analyticOrderNatAt_principal_eq_zeta hr.2.1 hr1,
    DirichletCharacter.LFunction_modOne_eq]

end LiuWang.Proof.PrincipalPsi
