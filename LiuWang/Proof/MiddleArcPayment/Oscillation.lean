import LiuWang.Proof.MiddleArcPayment.Error
import LiuWang.Proof.OscillatoryBounds.Consumer
import LiuWang.Proof.OscillatoryBounds.StrongConsumer

/-!
# Simultaneous oscillation and fixed-modulus Gauss payment

The real-zero branch never uses a reciprocal ordinate. The constants 10 and
3/pi are the already proved stronger oscillation constants. Conductor packets
retain their signs; the separate Cauchy bound is over characters of one q,
not an average over moduli.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.CompleteExpansion
open LiuWang.Proof.OscillatoryBounds

namespace LiuWang.Proof.MiddleArcPayment

def weightBound (N : ℕ) (rho : ℂ) : ℝ :=
  (1 - (0.001 : ℝ) ^ rho.re) / rho.re * (N : ℝ) ^ rho.re

def sqrtBound (N : ℕ) (rho : ℂ) : ℝ :=
  10 * (0.001 : ℝ) ^ (rho.re - 1) * (N : ℝ) ^ rho.re / Real.sqrt |rho.im|

def oscillationBound (N : ℕ) (rho : ℂ) (eta : ℝ) : ℝ :=
  if rho.im = 0 then
    if eta = 0 then weightBound N rho
    else min (weightBound N rho)
      ((0.001 * (N : ℝ)) ^ (rho.re - 1) / (Real.pi * |eta|))
  else min (weightBound N rho) (min (sqrtBound N rho)
    (if |eta| ≤ |rho.im| / (10 * Real.pi * (N : ℝ)) then
      5 * (N : ℝ) ^ rho.re / |rho.im|
    else if |rho.im| / (0.001 * Real.pi * (N : ℝ)) ≤ |eta| then
      (3 / Real.pi) * (0.001 * (N : ℝ)) ^ (rho.re - 1) / |eta|
    else sqrtBound N rho))

theorem Jrho_le_oscillationBound {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hr : 0 < rho.re) (hr1 : rho.re ≤ 1) (eta : ℝ) :
    ‖Jrho N rho eta‖ ≤ oscillationBound N rho eta := by
  unfold oscillationBound
  split_ifs with hg he hn hf
  · exact Jrho_weight hN hr eta
  · exact le_min (Jrho_weight hN hr eta) (Jrho_real_reciprocal hN hr1 hg he)
  · exact le_min (Jrho_weight hN hr eta)
      (le_min (Jrho_sqrt_ten hN hr1 hg eta) (Jrho_near hN hr.le hg hn))
  · exact le_min (Jrho_weight hN hr eta)
      (le_min (Jrho_sqrt_ten hN hr1 hg eta) (Jrho_far_three_pi hN hr1 hg hf))
  · exact le_min (Jrho_weight hN hr eta)
      (le_min (Jrho_sqrt_ten hN hr1 hg eta) (Jrho_sqrt_ten hN hr1 hg eta))

def characterOscillation {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ rho ∈ CompleteExpansion.zeroValues chi (sourceT N),
    (analyticOrderNatAt chi.LFunction rho : ℝ) * oscillationBound N rho eta

theorem norm_zeroValueSum_le {q N : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) (eta : ℝ) :
    ‖zeroValueSum chi N (sourceT N) eta‖ ≤ characterOscillation chi N eta := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro rho hrho
  rw [norm_mul, Complex.norm_natCast]
  have hr := CompleteExpansion.mem_zeroValues.mp hrho
  exact mul_le_mul_of_nonneg_left (Jrho_le_oscillationBound hN hr.2.1 hr.2.2.1.le eta)
    (Nat.cast_nonneg _)

theorem characterOscillation_nonneg {q N : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) (eta : ℝ) : 0 ≤ characterOscillation chi N eta :=
  (norm_nonneg _).trans (norm_zeroValueSum_le hN chi eta)

def gaussOscillation (q N a : ℕ) [NeZero q] (eta : ℝ) : ℝ :=
  (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ * characterOscillation chi N eta

def conductorNorm (q N a : ℕ) [NeZero q] (eta : ℝ) : ℝ :=
  (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors, ‖conductorPacket q d N a eta‖

theorem norm_zeroPacket_le_conductorNorm {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ)
    (haq : Nat.Coprime a q) :
    ‖zeroPacket q N a eta‖ ≤ conductorNorm q N a eta := by
  rw [zeroPacket_eq_conductors N a eta haq, norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

theorem conductorNorm_le_gaussOscillation {q N : ℕ} [NeZero q] (hN : 0 < N)
    (a : ℕ) (eta : ℝ) :
    conductorNorm q N a eta ≤ gaussOscillation q N a eta := by
  unfold conductorNorm gaussOscillation
  rw [← sum_conductorCharacters]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro d _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro chi _
  rw [norm_mul, ← zeroValueSum_eq_primitiveSource]
  exact mul_le_mul_of_nonneg_left (norm_zeroValueSum_le hN chi eta) (norm_nonneg _)

theorem gaussOscillation_le_energy {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    gaussOscillation q N a eta ≤
      Real.sqrt (∑ chi : Character q, characterOscillation chi N eta ^ 2) := by
  have hp : (0 : ℝ) < q.totient :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Character q))
    (fun chi => ‖G a chi‖) (fun chi => characterOscillation chi N eta)
  rw [NonprincipalPacket.gauss_energy, Real.sqrt_sq (Nat.cast_nonneg _)] at h
  apply (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)).trans_eq
  exact inv_mul_cancel_left₀ hp.ne' _

def jointPacketBound (q N a : ℕ) [NeZero q] (eta : ℝ) : ℝ :=
  min (conductorNorm q N a eta)
    (Real.sqrt (∑ chi : Character q, characterOscillation chi N eta ^ 2))

theorem norm_zeroPacket_le_joint {q N : ℕ} [NeZero q] (hN : 0 < N)
    (a : ℕ) (eta : ℝ) (haq : Nat.Coprime a q) :
    ‖zeroPacket q N a eta‖ ≤ jointPacketBound q N a eta := by
  have h := norm_zeroPacket_le_conductorNorm N a eta haq
  exact le_min h (h.trans ((conductorNorm_le_gaussOscillation hN a eta).trans
    (gaussOscillation_le_energy N a eta)))

def principalBound (q N : ℕ) (eta : ℝ) : ℝ :=
  principalMass q * (if eta = 0 then 0.999 * (N : ℝ)
    else min (0.999 * (N : ℝ)) (1 / (Real.pi * |eta|)))

theorem S_le_joint {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      principalBound q N eta + jointPacketBound q N a eta + errorBound q N a eta := by
  have he := complete_error_function hN hi hq eta
  have hz := norm_zeroPacket_le_joint (nat_pos_of_exp_le hN) a eta hi.2.2
  have hp : ‖principalCoefficient q * J N eta‖ ≤ principalBound q N eta := by
    rw [norm_mul, norm_principalCoefficient]
    exact mul_le_mul_of_nonneg_left (J_bound N eta) (principalMass_nonneg q)
  calc
    _ = ‖(principalCoefficient q * J N eta - zeroPacket q N a eta) +
        (S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
          zeroPacket q N a eta)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add hp hz)) he)

theorem M3_joint_bound {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq0 : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      principalBound q N eta + jointPacketBound q N a eta +
        0.000000000001 * (N : ℝ) / sourceL N :=
  (S_le_joint hN hi hq1 eta).trans
    (add_le_add le_rfl (middle_error_regression hN hq0 hq1 heta))

end LiuWang.Proof.MiddleArcPayment
