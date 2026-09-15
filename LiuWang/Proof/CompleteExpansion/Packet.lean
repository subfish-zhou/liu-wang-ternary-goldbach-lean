import LiuWang.Proof.PrincipalExpansion.Consumer
import LiuWang.Proof.NonprincipalPacket.Consumer

/-! # 实际全 S 的有号双分支零点包与字符误差合成 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.FixedHeightZeroSum
open LiuWang.Proof.NonprincipalPacket

namespace LiuWang.Proof.CompleteExpansion

def principalCoefficient (q : ℕ) : ℂ :=
  (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)

def principalMass (q : ℕ) : ℝ :=
  |(ArithmeticFunction.moebius q : ℝ)| / (q.totient : ℝ)

def nonprincipalMass (q : ℕ) [NeZero q] (a : ℕ) : ℝ :=
  (q.totient : ℝ)⁻¹ * ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, ‖G a chi‖

def zeroPacket (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) : ℂ :=
  principalCoefficient q * PrincipalExpansion.zeroSum q N (sourceT N) eta +
    (q.totient : ℂ)⁻¹ * Znp (q := q) N a eta

def nonprincipalError (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ *
    ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
      G a chi * (twistedS N eta chi +
        ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) eta)

theorem norm_principalCoefficient (q : ℕ) :
    ‖principalCoefficient q‖ = principalMass q := by
  simp [principalCoefficient, principalMass, Complex.norm_intCast]

theorem principalMass_nonneg (q : ℕ) : 0 ≤ principalMass q := by
  unfold principalMass
  positivity

theorem nonprincipalMass_nonneg (q : ℕ) [NeZero q] (a : ℕ) :
    0 ≤ nonprincipalMass q a := by
  unfold nonprincipalMass
  positivity

theorem zeroPacket_eq_gauss (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ)
    (haq : Nat.Coprime a q) :
    zeroPacket q N a eta = (q.totient : ℂ)⁻¹ *
      (G a (1 : Character q) * PrincipalExpansion.zeroSum q N (sourceT N) eta +
        Znp (q := q) N a eta) := by
  rw [G_one_eq_moebius haq]
  unfold zeroPacket principalCoefficient
  ring

theorem complete_error_identity {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ)
    (haq : Nat.Coprime a q) :
    S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
        zeroPacket q N a eta =
      principalCoefficient q *
        (twistedS N eta (1 : Character q) - J N eta +
          PrincipalExpansion.zeroSum q N (sourceT N) eta) +
        nonprincipalError q N a eta + nonCoprimeError N q (rationalCenter a q + eta) := by
  have h := packet_error_identity N a eta haq
  change S N (rationalCenter a q + eta) -
      principalCoefficient q * twistedS N eta (1 : Character q) +
      (q.totient : ℂ)⁻¹ * Znp (q := q) N a eta =
    nonprincipalError q N a eta + nonCoprimeError N q (rationalCenter a q + eta) at h
  unfold zeroPacket
  linear_combination h

theorem norm_nonprincipalError_le (q : ℕ) [NeZero q] (N a : ℕ) (eta B : ℝ)
    (hE : ∀ chi : Character q, chi ≠ 1 →
      ‖twistedS N eta chi +
        ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) eta‖ ≤ B) :
    ‖nonprincipalError q N a eta‖ ≤ nonprincipalMass q a * B := by
  rw [nonprincipalError, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ *
        ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
          ‖G a chi * (twistedS N eta chi +
            ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) eta)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (q.totient : ℝ)⁻¹ *
        ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, ‖G a chi‖ * B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro chi hc
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hE chi (Finset.mem_erase.mp hc).1) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; exact (mul_assoc _ _ _).symm

theorem complete_error_of_bounds {q : ℕ} [NeZero q] (N a : ℕ) (eta Bp Bnp : ℝ)
    (haq : Nat.Coprime a q)
    (hp : ‖twistedS N eta (1 : Character q) - J N eta +
      PrincipalExpansion.zeroSum q N (sourceT N) eta‖ ≤ Bp)
    (hnp : ∀ chi : Character q, chi ≠ 1 →
      ‖twistedS N eta chi +
        ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) eta‖ ≤ Bnp) :
    ‖S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
      zeroPacket q N a eta‖ ≤
      principalMass q * Bp + nonprincipalMass q a * Bnp +
        ‖nonCoprimeError N q (rationalCenter a q + eta)‖ := by
  rw [complete_error_identity N a eta haq]
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  apply (norm_add_le _ _).trans
  apply add_le_add _ (norm_nonprincipalError_le q N a eta Bnp hnp)
  rw [norm_mul, norm_principalCoefficient]
  exact mul_le_mul_of_nonneg_left hp (principalMass_nonneg q)

theorem nonprincipalMass_le_totient (q : ℕ) [NeZero q] (a : ℕ) :
    nonprincipalMass q a ≤ Real.sqrt (q.totient : ℝ) :=
  nonprincipal_gauss_mass_le_totient a

theorem nonprincipalMass_le_modulus (q : ℕ) [NeZero q] (a : ℕ) :
    nonprincipalMass q a ≤ Real.sqrt (q : ℝ) := nonprincipal_gauss_mass_le a

@[simp] theorem nonprincipalMass_one (a : ℕ) : nonprincipalMass 1 a = 0 := by
  simp [nonprincipalMass, Subsingleton.elim (default : Character 1) 1]

@[simp] theorem principalCoefficient_one : principalCoefficient 1 = 1 := by
  simp [principalCoefficient]

@[simp] theorem principalMass_one : principalMass 1 = 1 := by simp [principalMass]

@[simp] theorem zeroPacket_one (N a : ℕ) (eta : ℝ) :
    zeroPacket 1 N a eta = PrincipalExpansion.zeroSum 1 N (sourceT N) eta := by
  simp [zeroPacket]

theorem complete_modulus_one_identity (N a : ℕ) (eta : ℝ) :
    S N (rationalCenter a 1 + eta) - principalCoefficient 1 * J N eta +
      zeroPacket 1 N a eta =
    twistedS N eta (1 : Character 1) - J N eta +
      PrincipalExpansion.zeroSum 1 N (sourceT N) eta := by
  rw [S_modulus_one]
  simp

end LiuWang.Proof.CompleteExpansion
