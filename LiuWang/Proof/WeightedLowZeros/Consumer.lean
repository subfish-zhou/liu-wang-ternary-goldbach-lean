import LiuWang.Proof.WeightedLowZeros.Deletion
import LiuWang.Proof.WeightedLowZeros.SourceBulk
import LiuWang.Proof.CompleteExpansion.Consumer

/-!
# Original S and Jrho consumers with an exact low/high boundary

The high-height packet is retained unchanged and is not estimated here.
All character sums use ordinary analytic multiplicity, including the principal
character exactly once. No `q <= P1` low-height claim is made.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.ZeroRegionFamily
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros

def lowPacket (N a q : ℕ) [NeZero q] (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q,
    G a chi * CompleteExpansion.zeroValueSum chi N (omegaCutoff N q) eta

def highPacket (N a q : ℕ) [NeZero q] (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter
      (fun rho => omegaCutoff N q < |rho.im|),
        (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta

def retainedPacket (N a q : ℕ) [NeZero q] (eta : ℝ)
    (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ retainedValues chi (omegaCutoff N q) d e,
      (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta

def gaussMother (N a q : ℕ) [NeZero q] (padding : ℝ) : ℝ :=
  ∑ chi : Character q, ‖G a chi‖ * sharpenedBound chi (omegaCutoff N q) padding

theorem omegaCutoff_le_sourceT {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) : omegaCutoff N q ≤ sourceT N := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_ge_3100 hN
  have hp : 3.36 ≤ sourceL N ^ (12 : ℕ) :=
    (by linarith : (3.36 : ℝ) ≤ sourceL N).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ (one_le_sourceL hN') (by norm_num : 1 ≤ 12))
  calc
    omegaCutoff N q ≤ 3.36 * sourceP N :=
      div_le_self (by have := sourceP_pos hN'; positivity)
        (by exact_mod_cast (NeZero.one_le : 1 ≤ q))
    _ ≤ sourceL N ^ 12 * sourceP N :=
      mul_le_mul_of_nonneg_right hp (sourceP_pos hN').le
    _ = sourceT N := by unfold sourceP sourceT; ring

theorem values_low_eq_filter {q : ℕ} [NeZero q] (chi : Character q)
    {y T : ℝ} (hyT : y ≤ T) :
    CompleteExpansion.zeroValues chi y =
      (CompleteExpansion.zeroValues chi T).filter (fun rho => |rho.im| ≤ y) := by
  ext rho
  simp only [Finset.mem_filter, CompleteExpansion.mem_zeroValues]
  constructor
  · rintro ⟨hz, h0, h1, hy, hb⟩
    exact ⟨⟨hz, h0, h1, hy.trans hyT, hb⟩, hy⟩
  · rintro ⟨⟨hz, h0, h1, _, hb⟩, hy⟩
    exact ⟨hz, h0, h1, hy, hb⟩

theorem zeroValueSum_split (N : ℕ) {q : ℕ} [NeZero q] (chi : Character q)
    {y T : ℝ} (hyT : y ≤ T) (eta : ℝ) :
    CompleteExpansion.zeroValueSum chi N T eta =
      CompleteExpansion.zeroValueSum chi N y eta +
        ∑ rho ∈ (CompleteExpansion.zeroValues chi T).filter (fun rho => y < |rho.im|),
          (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta := by
  unfold CompleteExpansion.zeroValueSum
  rw [values_low_eq_filter chi hyT]
  simpa only [not_le, zeroMultiplicity] using
    (Finset.sum_filter_add_sum_filter_not (CompleteExpansion.zeroValues chi T)
      (fun rho => |rho.im| ≤ y)
      (fun rho => (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta)).symm

theorem zeroPacket_split {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (haq : Nat.Coprime a q) (eta : ℝ) :
    CompleteExpansion.zeroPacket q N a eta = lowPacket N a q eta + highPacket N a q eta := by
  rw [CompleteExpansion.zeroPacket_eq_all_values N a eta haq]
  unfold lowPacket highPacket
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  rw [← mul_add, zeroValueSum_split N chi (omegaCutoff_le_sourceT (q := q) hN) eta]

theorem complete_error_low_high {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP N) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) -
      CompleteExpansion.principalCoefficient q * J N eta +
        (lowPacket N a q eta + highPacket N a q eta)‖ ≤
          CompleteExpansion.errorBound q N a eta := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have h := CompleteExpansion.complete_error_function hN' hi
    (hq.trans (sourceP_le_sourceP1 hN')) eta
  rwa [zeroPacket_split hN hi.2.2] at h

theorem norm_capped_packet_le {N a q : ℕ} [NeZero q]
    (hN : 1000 ≤ (N : ℝ)) {padding sigma : ℝ} (hp : 0 < padding) (hs : 0 < sigma)
    (hy : 0 ≤ omegaCutoff N q) (eta : ℝ) (Z : Character q → Finset ℂ)
    (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hcap : ∀ chi rho, rho ∈ Z chi → rho.re ≤ sigma) :
    ‖(q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
        ∑ rho ∈ Z chi, (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta‖ ≤
      (q.totient : ℝ)⁻¹ * ((N : ℝ) * weight N sigma * gaussMother N a q padding) := by
  have hn : 0 < N := Nat.cast_pos.mp (by linarith : (0 : ℝ) < N)
  have hc (chi : Character q) :
      ‖∑ rho ∈ Z chi, (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta‖ ≤
        (N : ℝ) * (weight N sigma * sharpenedBound chi (omegaCutoff N q) padding) :=
    (norm_subset_Jrho_le hn chi (omegaCutoff N q) eta (Z chi) (hZ chi)).trans
        (mul_le_mul_of_nonneg_left
          (subset_weighted_le hN chi hy hp hs (Z chi) (hZ chi) (hcap chi)) (Nat.cast_nonneg _))
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ chi : Character q, ‖G a chi‖ *
        ((N : ℝ) * (weight N sigma * sharpenedBound chi (omegaCutoff N q) padding)) := by
      apply Finset.sum_le_sum
      intro chi _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hc chi) (norm_nonneg _)
    _ = _ := by
      unfold gaussMother
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro _ _
      ring

theorem norm_lowPacket_le {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {padding : ℝ} (hp : 0 < padding) (eta : ℝ) :
    ‖lowPacket N a q eta‖ ≤
      (q.totient : ℝ)⁻¹ * ((N : ℝ) * 0.999 * gaussMother N a q padding) := by
  simpa only [weight_one, lowPacket, CompleteExpansion.zeroValueSum, zeroMultiplicity] using
    norm_capped_packet_le (a := a) (source_endpoint_ge_thousand hN) hp (by norm_num : (0 : ℝ) < 1)
      (le_trans (by norm_num) (omegaCutoff_ge (NeZero.pos q) hq)) eta
      (fun chi => CompleteExpansion.zeroValues chi (omegaCutoff N q)) (fun _ _ h => h)
      (fun _ _ hr => (CompleteExpansion.mem_zeroValues.mp hr).2.2.1.le)

theorem norm_retainedPacket_le {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {padding : ℝ} (hp : 0 < padding)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt (lowScale N) d e) (eta : ℝ) :
    ‖retainedPacket N a q eta d e‖ ≤ (q.totient : ℝ)⁻¹ *
      ((N : ℝ) * weight N (regionCap (lowScale N)) * gaussMother N a q padding) := by
  obtain ⟨hx, hqx, he⟩ := lowScale_parameters hN hq
  apply norm_capped_packet_le (source_endpoint_ge_thousand hN) hp (regionCap_pos hx)
    (le_trans (by norm_num) (omegaCutoff_ge (NeZero.pos q) hq)) eta
    (fun chi => retainedValues chi (omegaCutoff N q) d e)
    (fun _ => Finset.filter_subset _ _)
  intro chi rho hr
  rw [← he] at hr
  exact retained_re_le hx hqx hd chi hr

theorem gaussMother_le_conductors (N a q : ℕ) [NeZero q]
    (haq : Nat.Coprime a q) {padding : ℝ} (hp : 0 < padding)
    (hy : 0 ≤ omegaCutoff N q) :
    gaussMother N a q padding ≤
      ∑ chi : Character q, Real.sqrt chi.conductor * sharpenedBound chi (omegaCutoff N q) padding :=
  Finset.sum_le_sum fun chi _ => mul_le_mul_of_nonneg_right (norm_G_le_sqrt_conductor haq chi)
    (sharpenedBound_nonneg chi hy hp)

theorem lowPacket_split_source {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt (lowScale N) d e) (eta : ℝ) :
    lowPacket N a q eta = retainedPacket N a q eta d e +
      if d.modulus ∣ q then (q.totient : ℂ)⁻¹ * G a (inducedAt d q) * Jrho N e eta else 0 := by
  obtain ⟨hx, hqx, he⟩ := lowScale_parameters hN hq
  have h := sum_split_retained (q := q) (lowScale N / q) d e
    (fun chi rho => G a chi * ((zeroMultiplicity chi rho : ℂ) * Jrho N rho eta))
  simp only [source_mem_iff hx hqx hd, and_true] at h
  rw [he] at h
  simp only [← Finset.mul_sum] at h
  have hh := congrArg (fun z : ℂ => (q.totient : ℂ)⁻¹ * z) h
  by_cases hdq : d.modulus ∣ q
  · simpa only [lowPacket, retainedPacket, CompleteExpansion.zeroValueSum, zeroMultiplicity,
      if_pos hdq, show analyticOrderNatAt (inducedAt d q).LFunction e = 1 from
        source_multiplicity hx hqx hd hdq, Nat.cast_one, one_mul, mul_add, mul_assoc] using hh
  · simpa only [lowPacket, retainedPacket, CompleteExpansion.zeroValueSum, zeroMultiplicity,
      if_neg hdq, add_zero] using hh

end LiuWang.Proof.WeightedLowZeros
