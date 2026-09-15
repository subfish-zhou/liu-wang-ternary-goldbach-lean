import LiuWang.Proof.NonprincipalPacket.Principal
import LiuWang.Proof.NonprincipalPacket.Budget

/-!
# 实际 S 的非主零点 Gauss 包与未近似主字符模式

原高度为 T=L^15；全部非主字符（含非本原）保持各自原零点索引、
闭高度、临界线等号与全部重数。仅对字符误差三角化，不对零点包三角化。
主字符仍为实际 twistedS；这里不是完整 R12。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.FixedHeightZeroSum

namespace LiuWang.Proof.NonprincipalPacket

def Znp {q : ℕ} [NeZero q] (N a : ℕ) (η : ℝ) : ℂ :=
  ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
    G a chi * ∑ p ∈ highZeroIndices chi (sourceT N),
      Jrho N (completedZeroValue p) η

theorem packet_error_identity {q : ℕ} [NeZero q] (N a : ℕ) (η : ℝ)
    (haq : Nat.Coprime a q) :
    S N (rationalCenter a q + η) -
        ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
          twistedS N η (1 : Character q) +
        (q.totient : ℂ)⁻¹ * Znp (q := q) N a η =
      (q.totient : ℂ)⁻¹ *
        (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
          G a chi * (twistedS N η chi +
            ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) η)) +
        nonCoprimeError N q (rationalCenter a q + η) := by
  rw [S_sub_principal_mode N a η haq]
  simp only [Znp, mul_add, Finset.sum_add_distrib]
  ring

theorem norm_weighted_nonprincipal_error_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hqUpper : (q : ℝ) ≤ sourceP1 N)
    (a : ℕ) (η : ℝ) :
    ‖(q.totient : ℂ)⁻¹ *
        (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
          G a chi * (twistedS N η chi +
            ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) η))‖ ≤
      Real.sqrt (q : ℝ) *
        ((1.3756 + 4.3287 * (N : ℝ) * |η|) * (N : ℝ) /
          sourceT N * sourceL N ^ 2) := by
  let B : ℝ := (1.3756 + 4.3287 * (N : ℝ) * |η|) * (N : ℝ) /
    sourceT N * sourceL N ^ 2
  have hT0 := sourceT_pos hN
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have he (chi : Character q) (hc : chi ≠ 1) :
      ‖twistedS N η chi +
        ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) η‖ ≤ B := by
    simpa only [NonprincipalExpansion.S_chi_eq_twistedS] using
      NonprincipalExpansion.nonprincipal_expansion_source_strong chi hN hqUpper hc η
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ *
        (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
          ‖G a chi * (twistedS N η chi +
            ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) η)‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (q.totient : ℝ)⁻¹ *
        (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, ‖G a chi‖ * B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro chi hc
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (he chi (Finset.mem_erase.mp hc).1) (norm_nonneg _)
    _ = ((q.totient : ℝ)⁻¹ *
        (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, ‖G a chi‖)) * B := by
      rw [← Finset.sum_mul, mul_assoc]
    _ ≤ Real.sqrt (q : ℝ) * B :=
      mul_le_mul_of_nonneg_right (nonprincipal_gauss_mass_le a) hB

theorem nonprincipal_packet_source {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (η : ℝ) :
    ‖S N (rationalCenter a q + η) -
        ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
          twistedS N η (1 : Character q) +
        (q.totient : ℂ)⁻¹ * Znp (q := q) N a η‖ ≤
      (1.3757 + 4.3287 * (N : ℝ) * |η|) * Real.sqrt (q : ℝ) *
        (N : ℝ) / sourceT N * sourceL N ^ 2 := by
  rw [packet_error_identity N a η hi.2.2]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ Real.sqrt (q : ℝ) *
          ((1.3756 + 4.3287 * (N : ℝ) * |η|) * (N : ℝ) /
            sourceT N * sourceL N ^ 2) +
        0.0001 * Real.sqrt (q : ℝ) * (N : ℝ) / sourceT N * sourceL N ^ 2 :=
      add_le_add (norm_weighted_nonprincipal_error_le hN hqUpper a η)
        (norm_nonCoprimeError_packet_le hN (hi.1.trans hi.2.1) hqUpper _)
    _ = _ := by ring

theorem nonprincipal_packet {N a q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hqUpper : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ)) (η : ℝ) :
    letI : NeZero q := ⟨by have := hi.1.trans hi.2.1; omega⟩
    ‖S N (rationalCenter a q + η) -
        ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
          twistedS N η (1 : Character q) +
        (q.totient : ℂ)⁻¹ *
          (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
            G a chi *
              ∑ p ∈ highZeroIndices chi ((Real.log (N : ℝ)) ^ (15 : ℕ)),
                Jrho N (completedZeroValue p) η)‖ ≤
      (1.3757 + 4.3287 * (N : ℝ) * |η|) * Real.sqrt (q : ℝ) *
        (N : ℝ) / (Real.log (N : ℝ)) ^ (15 : ℕ) *
          (Real.log (N : ℝ)) ^ (2 : ℕ) := by
  let : NeZero q := ⟨by have := hi.1.trans hi.2.1; omega⟩
  exact nonprincipal_packet_source hN hi hqUpper η

@[simp] theorem Znp_one (N a : ℕ) (η : ℝ) : Znp (q := 1) N a η = 0 := by
  simp [Znp, Subsingleton.elim (default : Character 1) 1]

theorem packet_modulus_one (N a : ℕ) (η : ℝ) :
    S N (rationalCenter a 1 + η) -
        ((ArithmeticFunction.moebius 1 : ℂ) / (Nat.totient 1 : ℂ)) *
          twistedS N η (1 : Character 1) +
        (Nat.totient 1 : ℂ)⁻¹ * Znp (q := 1) N a η = 0 := by
  rw [S_modulus_one]
  simp

end LiuWang.Proof.NonprincipalPacket
