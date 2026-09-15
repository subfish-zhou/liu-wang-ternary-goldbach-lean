import LiuWang.Proof.MiddleArcPayment.Consumer

/-! # Explicit scalar alternative to the retained actual Gauss/conductor masses -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.CompleteExpansion

namespace LiuWang.Proof.MiddleArcPayment

def modulusCount (q : ℕ) (y : ℝ) : ℝ :=
  (y + 2) * (Real.log q / 2 + Real.log (y + 4) / 2 + 7 / 3) / Real.arctan 1

theorem modulusCount_nonneg {q : ℕ} [NeZero q] {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ modulusCount q y := by
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ q))
  have hlogy : 0 ≤ Real.log (y + 4) := Real.log_nonneg (by linarith)
  unfold modulusCount
  positivity

theorem sharpenedBound_le_modulus {q : ℕ} [NeZero q] (chi : Character q)
    {y : ℝ} (hy : 0 ≤ y) :
    DirichletZeroCount.sharpenedBound chi y 2 ≤ modulusCount q y := by
  apply (min_le_right _ _).trans
  have hd : 0 ≤ Real.arctan 1 := Real.arctan_nonneg.mpr (by norm_num)
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ q))
  have hc : Real.log chi.conductor ≤ Real.log q :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero chi.conductor_ne_zero))
      (Nat.cast_le.mpr (BombieriVinogradov.DirichletCharacter.conductor_le_level chi))
  unfold modulusCount
  rw [show y + 2 + 2 = y + 4 by ring]
  norm_num only [show (2 / 2 : ℝ) = 1 by norm_num]
  split_ifs
  · apply div_le_div_of_nonneg_right _ hd
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  · apply div_le_div_of_nonneg_right _ hd
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith

def scalarCount (q N : ℕ) (eta b : ℝ) : ℝ :=
  Real.sqrt q * (N : ℝ) ^ b *
    ∑ j ∈ Finset.range (sourceDyadicHeight N + 1),
      heightCost N eta (cellLower 1 j) * modulusCount q (cellUpper 1 j)

theorem countPayment_le_scalar {q : ℕ} [NeZero q] (N a : ℕ) (eta b : ℝ) :
    countPayment q N a eta b ≤ scalarCount q N eta b := by
  let D := (N : ℝ) ^ b * ∑ j ∈ Finset.range (sourceDyadicHeight N + 1),
    heightCost N eta (cellLower 1 j) * modulusCount q (cellUpper 1 j)
  have hD : 0 ≤ D := by
    apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (heightCost_nonneg N eta _)
      (modulusCount_nonneg (by unfold cellUpper; positivity))
  have hc (chi : Character q) :
      dyadicCountBound chi N eta b 1 2 (sourceDyadicHeight N) ≤ D := by
    unfold dyadicCountBound
    dsimp [D]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    unfold cellBound
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (sharpenedBound_le_modulus chi (by unfold cellUpper; positivity))
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (heightCost_nonneg N eta _))
  have hp : (0 : ℝ) < q.totient :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hg : (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ ≤ Real.sqrt q := by
    calc
      _ ≤ (q.totient : ℝ)⁻¹ * (Real.sqrt (q.totient : ℝ) * q.totient) :=
        mul_le_mul_of_nonneg_left (NonprincipalPacket.sum_norm_G_le a) (by positivity)
      _ = Real.sqrt (q.totient : ℝ) := by field_simp
      _ ≤ _ := Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.totient_le q))
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ * D := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun chi _ => mul_le_mul_of_nonneg_left (hc chi) (norm_nonneg _))
    _ = ((q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖) * D := by
      rw [← Finset.sum_mul, mul_assoc]
    _ ≤ Real.sqrt q * D := mul_le_mul_of_nonneg_right hg hD
    _ = _ := by unfold scalarCount; dsimp [D]; ring

theorem M3_scalar_payment {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq0 : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N)
    {eta : ℝ} (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) (b : ℝ) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      min (principalBound q N eta + scalarCount q N eta 1)
        (‖principalCoefficient q * J N eta - upperPacket q N a eta b‖ +
          scalarCount q N eta b) + 0.000000000001 * (N : ℝ) / sourceL N := by
  have he := middle_error_regression (a := a) hN hq0 hq1 heta
  have hf := (S_le_full_count hN hi hq1 eta).trans
    (add_le_add (add_le_add le_rfl (countPayment_le_scalar N a eta 1)) he)
  have hc := (S_le_countPayment hN hi hq1 eta b).trans
    (add_le_add (add_le_add le_rfl (countPayment_le_scalar N a eta b)) he)
  rw [← min_add_add_right]
  exact le_min hf hc

end LiuWang.Proof.MiddleArcPayment
