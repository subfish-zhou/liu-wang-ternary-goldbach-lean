import LiuWang.Proof.NonprincipalDensityAdvance.CharacterEnergy
import LiuWang.Proof.DirichletZeroCount.Applications.CompleteValues

/-!
# Consumers on the frozen complete-S zero packet

The high-alpha packet is split off by an exact identity; the complementary
packet and principal contribution remain present. Its bound uses the actual
detector's orders, not an assumed Chen zero count.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.CharacterExpansion

namespace LiuWang.Proof.NonprincipalDensityAdvance

def highZeroPacket (q : ℕ) [NeZero q] (N a : ℕ) (alpha y eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi ∈ nonprincipalCharacters q,
    G a chi * ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter
      (fun rho => alpha ≤ rho.re), (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta

def remainingZeroPacket (q : ℕ) [NeZero q] (N a : ℕ) (alpha y eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi ∈ nonprincipalCharacters q,
    G a chi * ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter
      (fun rho => ¬alpha ≤ rho.re), (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta

theorem complete_zeroPacket_split {q : ℕ} [NeZero q] (N a : ℕ) (alpha eta : ℝ)
    (haq : Nat.Coprime a q) :
    CompleteExpansion.zeroPacket q N a eta =
      (q.totient : ℂ)⁻¹ * G a (1 : Character q) *
        CompleteExpansion.zeroValueSum (1 : Character q) N (sourceT N) eta +
      highZeroPacket q N a alpha (sourceT N) eta +
      remainingZeroPacket q N a alpha (sourceT N) eta := by
  rw [CompleteExpansion.zeroPacket_eq_all_values N a eta haq,
    ← sum_erase_add _ _ (mem_univ (1 : Character q))]
  have hs (chi : Character q) :
      CompleteExpansion.zeroValueSum chi N (sourceT N) eta =
        (∑ rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter
          (fun rho => alpha ≤ rho.re), (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta) +
        (∑ rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter
          (fun rho => ¬alpha ≤ rho.re), (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta) :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  unfold highZeroPacket remainingZeroPacket nonprincipalCharacters
  simp_rw [hs, mul_add, sum_add_distrib]
  ring

@[simp] theorem highZeroPacket_one (N a : ℕ) (alpha y eta : ℝ) :
    highZeroPacket 1 N a alpha y eta = 0 := by
  simp [highZeroPacket]

theorem high_count_eq_complete_values (q : ℕ) [NeZero q] {alpha : ℝ}
    (halpha : 1 / 2 ≤ alpha) (y : ℝ) :
    nonprincipalCount q alpha y =
      ∑ chi ∈ nonprincipalCharacters q,
        ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha ≤ rho.re),
          zeroMultiplicity chi rho := by
  rw [nonprincipalCount_eq_multiplicity_sum]
  simp only [DirichletZeroCount.Applications.values_eq_complete_filter _ halpha]

theorem norm_highZeroPacket_le_detector (q : ℕ) [NeZero q] (N a : ℕ)
    (alpha y eta : ℝ) {X : ℝ} (hX : 3 < X) :
    ‖highZeroPacket q N a alpha y eta‖ ≤
      (∑ chi ∈ nonprincipalCharacters q, ‖G a chi‖ *
        ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha ≤ rho.re),
          (analyticOrderNatAt (H chi X) rho : ℝ) * ‖Jrho N rho eta‖) / q.totient := by
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      ‖∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha ≤ rho.re),
        (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta‖ ≤
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => alpha ≤ rho.re),
        (analyticOrderNatAt (H chi X) rho : ℝ) * ‖Jrho N rho eta‖ := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro rho _
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (multiplicity_le_detector hchi hX rho)) (norm_nonneg _)
  unfold highZeroPacket
  rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_mul_inv, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro chi hchi
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hi chi (mem_nonprincipalCharacters chi |>.mp hchi))
    (norm_nonneg _)

theorem source_nonprincipal_right_boundary (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (∑ chi ∈ nonprincipalCharacters q,
      ∫ t in -y..y, |Real.log ‖H chi y ((2 : ℂ) + t * Complex.I)‖|) / q.totient ≤
        ((q.totient - 1 : ℕ) : ℝ) / q.totient * (16 * y / (y - 1) ^ 2) := by
  have hy' := DirichletZeroCount.Applications.source_height_ge_ten_thousand hy
  exact normalized_right_boundary_paid q (by linarith) (by linarith)

end LiuWang.Proof.NonprincipalDensityAdvance
