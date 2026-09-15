import LiuWang.Proof.NonprincipalPacket.Consumer

/-! 保留实际非主Gauss质量与原log(q)修正，不提前放宽至sqrt(q)。 -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.FixedHeightZeroSum
namespace LiuWang.Proof.NonprincipalPacket

theorem norm_weighted_nonprincipal_error_le_mass {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hqUpper : (q : ℝ) ≤ sourceP1 N)
    (a : ℕ) (η : ℝ) :
    ‖(q.totient : ℂ)⁻¹ *
        (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
          G a chi * (twistedS N η chi +
            ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) η))‖ ≤
      ((q.totient : ℝ)⁻¹ *
        (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, ‖G a chi‖)) *
        ((1.3756 + 4.3287 * (N : ℝ) * |η|) * (N : ℝ) /
          sourceT N * sourceL N ^ 2) := by
  let B : ℝ := (1.3756 + 4.3287 * (N : ℝ) * |η|) * (N : ℝ) /
    sourceT N * sourceL N ^ 2
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

theorem nonprincipal_packet_mass_bound {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (η : ℝ) :
    ‖S N (rationalCenter a q + η) -
        ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
          twistedS N η (1 : Character q) +
        (q.totient : ℂ)⁻¹ * Znp (q := q) N a η‖ ≤
      ((q.totient : ℝ)⁻¹ *
        (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, ‖G a chi‖)) *
        ((1.3756 + 4.3287 * (N : ℝ) * |η|) * (N : ℝ) /
          sourceT N * sourceL N ^ 2) + Real.log q * sourceL N / Real.log 2 := by
  rw [packet_error_identity N a η hi.2.2]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_weighted_nonprincipal_error_le_mass hN hqUpper a η)
    (norm_nonCoprimeError_le_log (nat_pos_of_exp_le hN) (NeZero.pos q) _))

theorem nonprincipal_packet_totient_bound {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (η : ℝ) :
    ‖S N (rationalCenter a q + η) -
        ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
          twistedS N η (1 : Character q) +
        (q.totient : ℂ)⁻¹ * Znp (q := q) N a η‖ ≤
      Real.sqrt (q.totient : ℝ) *
        ((1.3756 + 4.3287 * (N : ℝ) * |η|) * (N : ℝ) /
          sourceT N * sourceL N ^ 2) + Real.log q * sourceL N / Real.log 2 := by
  apply (nonprincipal_packet_mass_bound hN hi hqUpper η).trans
  apply add_le_add _ le_rfl
  have hT := sourceT_pos hN
  exact mul_le_mul_of_nonneg_right (nonprincipal_gauss_mass_le_totient a) (by positivity)

end LiuWang.Proof.NonprincipalPacket
