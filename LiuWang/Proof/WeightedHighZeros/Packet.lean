import LiuWang.Proof.WeightedHighZeros.LargeLog
import LiuWang.Proof.CharacterExpansion.GaussInduction

/-!
# The actual Gauss-weighted high part of the complete zero packet

The complementary set uses strict `< omega`, so the displayed identity
assigns each boundary zero exactly once. No low-height estimate is asserted.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.WeightedHighZeros

def highPacket (N q a : ℕ) [NeZero q] (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q,
    CharacterExpansion.G a chi * ∑ rho ∈ highValues N chi,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem complete_zeroPacket_split {N q a : ℕ} [NeZero q] (ha : Nat.Coprime a q)
    (eta : ℝ) :
    CompleteExpansion.zeroPacket q N a eta =
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q,
        CharacterExpansion.G a chi *
          ∑ rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter
            (fun rho => |rho.im| < omegaCutoff N q),
              (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta +
      highPacket N q a eta := by
  have hs (chi : Character q) :
      CompleteExpansion.zeroValueSum chi N (sourceT N) eta =
        (∑ rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter
          (fun rho => |rho.im| < omegaCutoff N q),
            (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta) +
        ∑ rho ∈ highValues N chi,
          (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
    rw [highValues_eq_complete, add_comm]
    simpa only [CompleteExpansion.zeroValueSum, not_le] using
      (Finset.sum_filter_add_sum_filter_not
        (CompleteExpansion.zeroValues chi (sourceT N))
        (fun rho => omegaCutoff N q ≤ |rho.im|)
        (fun rho => (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta)).symm
  rw [CompleteExpansion.zeroPacket_eq_all_values N a eta ha]
  simp only [hs, mul_add, Finset.sum_add_distrib, highPacket]

theorem highPacket_le_weighted {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : Nat.Coprime a q)
    {eta : ℝ} (heta : |eta| ≤ deltaRadius N q) :
    ‖highPacket N q a eta‖ ≤
      (5 * (N : ℝ) * Real.sqrt q / q.totient) * highSum N q := by
  have hg (chi : Character q) : ‖CharacterExpansion.G a chi‖ ≤ Real.sqrt q :=
    (CharacterExpansion.norm_G_le_sqrt_conductor ha chi).trans
      (Real.sqrt_le_sqrt
        (Nat.cast_le.mpr (BombieriVinogradov.DirichletCharacter.conductor_le_level chi)))
  have hterm (chi : Character q) (rho : ℂ) (hrho : rho ∈ highValues N chi) :
      ‖CharacterExpansion.G a chi *
          ((analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta)‖ ≤
        Real.sqrt q * (5 * (N : ℝ) * ((analyticOrderNatAt chi.LFunction rho : ℝ) *
          ((N : ℝ) ^ (rho.re - 1) / |rho.im|))) := by
    rw [norm_mul]
    exact mul_le_mul (hg chi) (highValue_norm_mul_Jrho_le hN heta hrho)
      (norm_nonneg _) (Real.sqrt_nonneg _)
  have hsum :
      ‖∑ chi : Character q, CharacterExpansion.G a chi *
        ∑ rho ∈ highValues N chi, (analyticOrderNatAt chi.LFunction rho : ℂ) *
          Jrho N rho eta‖ ≤ Real.sqrt q * (5 * (N : ℝ) * highSum N q) := by
    simp_rw [Finset.mul_sum]
    calc
      _ ≤ ∑ chi : Character q, ∑ rho ∈ highValues N chi,
          ‖CharacterExpansion.G a chi *
            ((analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
      _ ≤ ∑ chi : Character q, ∑ rho ∈ highValues N chi,
          Real.sqrt q * (5 * (N : ℝ) * ((analyticOrderNatAt chi.LFunction rho : ℝ) *
            ((N : ℝ) ^ (rho.re - 1) / |rho.im|))) :=
        Finset.sum_le_sum (fun chi _ => Finset.sum_le_sum (hterm chi))
      _ = _ := by
        simp only [highSum, bandSum, highValues, Finset.mul_sum]
  rw [highPacket, norm_mul, norm_inv, Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)

theorem highPacket_le_mother {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta r : ℝ}
    (heta : |eta| ≤ deltaRadius N q) (hr : 1 < r) :
    ‖highPacket N q a eta‖ ≤
      (5 * (N : ℝ) * Real.sqrt q / q.totient) * motherBound N q r :=
  (highPacket_le_weighted hN ha heta).trans
    (mul_le_mul_of_nonneg_left (highSum_le_motherBound hN hq hr) (by positivity))

theorem highPacket_le_large_log {N q a : ℕ} [NeZero q]
    (hN : Real.exp 100000000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ} (heta : |eta| ≤ deltaRadius N q) :
    ‖highPacket N q a eta‖ ≤
      (5 * (N : ℝ) * Real.sqrt q / q.totient) * (0.0126 * q / sourceL N ^ (4 : ℕ)) :=
  (highPacket_le_weighted ((Real.exp_le_exp.mpr (by norm_num)).trans hN) ha heta).trans
    (mul_le_mul_of_nonneg_left (highSum_le_large_log hN hq) (by positivity))

end LiuWang.Proof.WeightedHighZeros
