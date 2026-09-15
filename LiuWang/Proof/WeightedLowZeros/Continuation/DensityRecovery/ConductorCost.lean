import LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery.WeakerRemainder

/-! # The fixed actual source pays sqrt(conductor), not sqrt(ambient modulus) -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.ZeroRegionFamily
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery

def sourceTerm (N a q : ℕ) [NeZero q] (d : PrimitiveQuadraticDatum) (e : ℂ) (eta : ℝ) : ℂ :=
  if d.modulus ∣ q then (q.totient : ℂ)⁻¹ * G a (inducedAt d q) * Jrho N e eta else 0

def sourceCost (N q : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) : ℝ :=
  if d.modulus ∣ q then (q.totient : ℝ)⁻¹ *
    (Real.sqrt (d.modulus : ℝ) * ((N : ℝ) * weight N e.re)) else 0

theorem induced_G_conductor {a q : ℕ} [NeZero q] (haq : Nat.Coprime a q)
    (d : PrimitiveQuadraticDatum) (hdiv : d.modulus ∣ q) :
    ‖G a (inducedAt d q)‖ ≤ Real.sqrt (d.modulus : ℝ) := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  simpa only [inducedAt, dif_pos hdiv] using norm_G_induced_le_sqrt hdiv haq d.character d.isPrimitive

theorem norm_sourceTerm_le {N a q : ℕ} [NeZero q]
    (hN : 0 < N) (haq : Nat.Coprime a q) (d : PrimitiveQuadraticDatum)
    {e : ℂ} (he : 0 < e.re) (eta : ℝ) :
    ‖sourceTerm N a q d e eta‖ ≤ sourceCost N q d e := by
  unfold sourceTerm sourceCost
  split_ifs with hdiv
  · rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (induced_G_conductor haq d hdiv) (Jrho_le_weight hN he eta)
        (norm_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
  · simp only [norm_zero, le_refl]

theorem sourceCost_le_ambient {N q : ℕ} [NeZero q]
    (d : PrimitiveQuadraticDatum) {e : ℂ} (he : 0 < e.re) :
    sourceCost N q d e ≤
      if d.modulus ∣ q then (q.totient : ℝ)⁻¹ *
        (Real.sqrt (q : ℝ) * ((N : ℝ) * weight N e.re)) else 0 := by
  unfold sourceCost
  split_ifs with hdiv
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.le_of_dvd (NeZero.pos q) hdiv)))
    exact mul_nonneg (Nat.cast_nonneg _) (weight_nonneg N he)
  · exact le_rfl

theorem sourceCost_nonneg (N q : ℕ) (d : PrimitiveQuadraticDatum)
    {e : ℂ} (he : 0 < e.re) : 0 ≤ sourceCost N q d e := by
  unfold sourceCost
  split_ifs
  · exact mul_nonneg (by positivity)
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (weight_nonneg N he)))
  · exact le_rfl

theorem paper_lowPacket_conductor {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (haq : Nat.Coprime a q)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.27) (eta : ℝ) :
    ‖lowPacket N a q eta‖ ≤
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (7.6e-10 / sourceL N) +
        sourceCost N q d e := by
  have he : 0 < e.re := by linarith [paper_source_half hN hd]
  rw [paper_lowPacket_split hN hq hd]
  exact (norm_add_le _ _).trans (add_le_add (retained_packet_027 hN hq haq d e hregion eta)
    (norm_sourceTerm_le (nat_pos_of_exp_le hN) haq d he eta))

theorem paper_S_conductor {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.27) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        highPacket N a q eta‖ ≤ CompleteExpansion.errorBound q N a eta +
      (((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (7.6e-10 / sourceL N) +
        sourceCost N q d e) := by
  have he := complete_error_low_high hN hi hq eta
  have hp := paper_lowPacket_conductor hN hq hi.2.2 hd hregion eta
  have hid :
      S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        highPacket N a q eta =
      (S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        (lowPacket N a q eta + highPacket N a q eta)) - lowPacket N a q eta := by ring
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add he hp)

theorem paper_S_no_induction {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : ¬ d.modulus ∣ q)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.27) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        highPacket N a q eta‖ ≤ CompleteExpansion.errorBound q N a eta +
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (7.6e-10 / sourceL N) := by
  simpa only [sourceCost, if_neg hdiv, add_zero] using paper_S_conductor hN hi hq hd hregion eta

end LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery
