import LiuWang.Proof.NearArcPayment.Payment
import LiuWang.Proof.OscillatoryBounds.StrongConsumer

/-!
# Multiplicity-preserving oscillatory bill

Every value is an actual ordinary L-function zero in the frozen half strip.
Real zeros, including any exceptional zero, are retained. All branch
thresholds use this same eta. The unconditional square-root constant is 10,
and the far constant is 3/pi, not the weaker 16 and 4/pi.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment

open Interfaces Parameters ArcGeometry CompleteExpansion CharacterExpansion OscillatoryBounds

def weightKernel (N : ℕ) (rho : ℂ) : ℝ :=
  (1 - (0.001 : ℝ) ^ rho.re) / rho.re * (N : ℝ) ^ rho.re

def sqrtKernel (N : ℕ) (rho : ℂ) : ℝ :=
  10 * (0.001 : ℝ) ^ (rho.re - 1) * (N : ℝ) ^ rho.re / Real.sqrt |rho.im|

def nearKernel (N : ℕ) (rho : ℂ) : ℝ :=
  5 * (N : ℝ) ^ rho.re / |rho.im|

def realKernel (N : ℕ) (rho : ℂ) (eta : ℝ) : ℝ :=
  (0.001 * (N : ℝ)) ^ (rho.re - 1) / (Real.pi * |eta|)

def farKernel (N : ℕ) (rho : ℂ) (eta : ℝ) : ℝ :=
  (3 / Real.pi) * (0.001 * (N : ℝ)) ^ (rho.re - 1) / |eta|

def kernelBill (N : ℕ) (rho : ℂ) (eta : ℝ) : ℝ :=
  if rho.im = 0 then min (weightKernel N rho) (realKernel N rho eta)
  else if |eta| ≤ |rho.im| / (10 * Real.pi * (N : ℝ)) then
    min (weightKernel N rho) (min (sqrtKernel N rho) (nearKernel N rho))
  else if |rho.im| / (0.001 * Real.pi * (N : ℝ)) ≤ |eta| then
    min (weightKernel N rho) (min (sqrtKernel N rho) (farKernel N rho eta))
  else min (weightKernel N rho) (sqrtKernel N rho)

theorem Jrho_le_kernelBill {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hb : 0 < rho.re) (hb1 : rho.re ≤ 1) {eta : ℝ} (he : eta ≠ 0) :
    ‖Jrho N rho eta‖ ≤ kernelBill N rho eta := by
  have hw : ‖Jrho N rho eta‖ ≤ weightKernel N rho := Jrho_weight hN hb eta
  unfold kernelBill
  split_ifs with hg hn hf
  · exact le_min hw (Jrho_real_reciprocal hN hb1 hg he)
  · exact le_min hw (le_min (Jrho_sqrt_ten hN hb1 hg eta) (Jrho_near hN hb.le hg hn))
  · exact le_min hw (le_min (Jrho_sqrt_ten hN hb1 hg eta) (Jrho_far_three_pi hN hb1 hg hf))
  · exact le_min hw (Jrho_sqrt_ten hN hb1 hg eta)

theorem actual_zero_kernel {N q : ℕ} [NeZero q] (hN : 0 < N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ zeroValues chi (sourceT N))
    {eta : ℝ} (he : eta ≠ 0) :
    ‖Jrho N rho eta‖ ≤ kernelBill N rho eta :=
  Jrho_le_kernelBill hN (mem_zeroValues.mp hr).2.1 (mem_zeroValues.mp hr).2.2.1.le he

theorem kernelBill_nonneg_on_zeros {N q : ℕ} [NeZero q] (hN : 0 < N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ zeroValues chi (sourceT N))
    {eta : ℝ} (he : eta ≠ 0) :
    0 ≤ kernelBill N rho eta :=
  (norm_nonneg _).trans (actual_zero_kernel hN hr he)

def zeroBill (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) : ℝ :=
  (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
    ∑ rho ∈ zeroValues chi (sourceT N),
      (analyticOrderNatAt chi.LFunction rho : ℝ) * kernelBill N rho eta

theorem norm_zeroPacket_le_bill {N a q : ℕ} [NeZero q]
    (hN : 0 < N) (hi : sourceIndex a q) {eta : ℝ} (he : eta ≠ 0) :
    ‖zeroPacket q N a eta‖ ≤ zeroBill q N a eta := by
  rw [zeroPacket_eq_all_values N a eta hi.2.2, norm_mul, norm_inv, Complex.norm_natCast]
  unfold zeroBill
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro chi _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold zeroValueSum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro rho hr
  rw [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (actual_zero_kernel hN hr he) (Nat.cast_nonneg _)

theorem zeroBill_nonneg {N a q : ℕ} [NeZero q]
    (hN : 0 < N) (hi : sourceIndex a q) {eta : ℝ} (he : eta ≠ 0) :
    0 ≤ zeroBill q N a eta :=
  (norm_nonneg _).trans (norm_zeroPacket_le_bill hN hi he)

def branchBill (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ)
    (p : ℂ → Prop) : ℝ :=
  (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
    ∑ rho ∈ (zeroValues chi (sourceT N)).filter p,
      (analyticOrderNatAt chi.LFunction rho : ℝ) * kernelBill N rho eta

def realBranch (rho : ℂ) : Prop := rho.im = 0

def nearBranch (N : ℕ) (eta : ℝ) (rho : ℂ) : Prop :=
  rho.im ≠ 0 ∧ |eta| ≤ |rho.im| / (10 * Real.pi * (N : ℝ))

def farBranch (N : ℕ) (eta : ℝ) (rho : ℂ) : Prop :=
  rho.im ≠ 0 ∧ ¬ |eta| ≤ |rho.im| / (10 * Real.pi * (N : ℝ)) ∧
    |rho.im| / (0.001 * Real.pi * (N : ℝ)) ≤ |eta|

def transitionBranch (N : ℕ) (eta : ℝ) (rho : ℂ) : Prop :=
  rho.im ≠ 0 ∧ ¬ |eta| ≤ |rho.im| / (10 * Real.pi * (N : ℝ)) ∧
    ¬ |rho.im| / (0.001 * Real.pi * (N : ℝ)) ≤ |eta|

theorem zeroBill_eq_four_branches (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) :
    zeroBill q N a eta =
      branchBill q N a eta realBranch +
      branchBill q N a eta (nearBranch N eta) +
      branchBill q N a eta (farBranch N eta) +
      branchBill q N a eta (transitionBranch N eta) := by
  unfold zeroBill branchBill
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  apply Finset.sum_congr rfl
  intro rho _
  unfold realBranch nearBranch farBranch transitionBranch
  by_cases hg : rho.im = 0 <;>
    by_cases hn : |eta| ≤ |rho.im| / (10 * Real.pi * (N : ℝ)) <;>
    by_cases hf : |rho.im| / (0.001 * Real.pi * (N : ℝ)) ≤ |eta| <;>
    simp [hg, hn, hf]

theorem high_height_is_near {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q) {eta : ℝ}
    (he : |eta| ≤ 1 / ((q : ℝ) * sourceQ N)) {rho : ℂ}
    (hh : 10 * Real.pi * sourceL N ^ 7 / (q : ℝ) ≤ |rho.im|) :
    |eta| ≤ |rho.im| / (10 * Real.pi * (N : ℝ)) := by
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hn := natCast_pos_of_exp_le hN
  rw [approximationRadius_eq hN hq] at he
  apply he.trans
  apply (le_div_iff₀ (by positivity : 0 < 10 * Real.pi * (N : ℝ))).mpr
  calc
    sourceL N ^ 7 / ((q : ℝ) * (N : ℝ)) * (10 * Real.pi * (N : ℝ)) =
        10 * Real.pi * sourceL N ^ 7 / (q : ℝ) := by field_simp
    _ ≤ _ := hh

theorem tiny_height_is_far {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q) {eta : ℝ}
    (he : deltaRadius N q < |eta|) {rho : ℂ}
    (hh : |rho.im| ≤ omegaCutoff N q / 10000) :
    |rho.im| / (0.001 * Real.pi * (N : ℝ)) ≤ |eta| := by
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hn := natCast_pos_of_exp_le hN
  apply le_trans _ he.le
  calc
    _ ≤ (omegaCutoff N q / 10000) / (0.001 * Real.pi * (N : ℝ)) :=
      div_le_div_of_nonneg_right hh (by positivity)
    _ = deltaRadius N q := by
      rw [deltaRadius_eq_omega]
      ring

end LiuWang.Proof.NearArcPayment
