import LiuWang.Proof.WeightedLowZeros.Continuation.PaperSource
import LiuWang.Proof.WeightedLowZeros.Consumer
import LiuWang.Proof.WeightedHighZeros.Consumer
import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.RegularCubic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.SingularIntegral
open LiuWang.Proof.SourceRoute.MajorException
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1

theorem exceptional_beta_ge_09957 {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : PaperSource N d e) : 0.9957 ≤ e.re := by
  have hexp : Real.exp 8 ≤ 2981 := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 8
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    exact h.trans (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < Real.exp 8 / 3100 by positivity)
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hlog
  have hL := Real.log_le_log (by norm_num : (0 : ℝ) < 3100) (sourceL_ge_3100 hN)
  have hl : 24.115 ≤ Real.log (sourceP N) := by
    rw [sourceP, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hg : 1 / (9.645908801 * Real.log (sourceP N)) ≤ 0.0043 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  linarith [hd.2.2.2.2]

def ordinaryMass (N q : ℕ) [NeZero q] (d : PrimitiveQuadraticDatum) (e : ℂ) : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ retainedValues chi (sourceT N) d e,
    (zeroMultiplicity chi rho : ℝ) * regularWeight N q rho

def ordinaryPacket (N a q : ℕ) [NeZero q] (d : PrimitiveQuadraticDatum)
    (e : ℂ) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ retainedValues chi (sourceT N) d e,
      (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta

theorem ordinaryMass_nonneg {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (d : PrimitiveQuadraticDatum) (e : ℂ) :
    0 ≤ ordinaryMass N q d e := by
  apply Finset.sum_nonneg
  intro chi _
  apply Finset.sum_nonneg
  intro rho hr
  exact mul_nonneg (Nat.cast_nonneg _) (regularWeight_pos
    (exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)
    (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.1).le

theorem retained_low_filter {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (d : PrimitiveQuadraticDatum) (e : ℂ)
    (chi : Character q) :
    (retainedValues chi (sourceT N) d e).filter
      (fun rho => |rho.im| ≤ omegaCutoff N q) =
        retainedValues chi (omegaCutoff N q) d e := by
  simp only [retainedValues]
  rw [values_low_eq_filter chi (omegaCutoff_le_sourceT (q := q) hN)]
  ext rho
  simp only [Finset.mem_filter]
  tauto

theorem ordinaryMass_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (d : PrimitiveQuadraticDatum) (e : ℂ) :
    ordinaryMass N q d e =
      retainedSum N q (omegaCutoff N q) d e +
        5 * ∑ chi : Character q,
          ∑ rho ∈ (retainedValues chi (sourceT N) d e).filter
            (fun rho => omegaCutoff N q < |rho.im|),
              (zeroMultiplicity chi rho : ℝ) * highWeight N rho := by
  simp only [ordinaryMass, regularWeight, mul_ite, Finset.sum_ite,
    not_le, retained_low_filter hN,
    retainedSum, weight, lowWeight, baseWeight,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  apply Finset.sum_congr rfl
  intro rho _
  ring

theorem ordinaryPacket_continuous {N q : ℕ} [NeZero q] (hN : 0 < N)
    (a : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) :
    Continuous (ordinaryPacket N a q d e) := by
  unfold ordinaryPacket
  apply continuous_const.mul
  apply continuous_finsetSum
  intro chi _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro rho _
  exact continuous_const.mul (Jrho_continuous hN rho)

theorem norm_G_le_sqrt_modulus {a q : ℕ} [NeZero q] (ha : Nat.Coprime a q)
    (chi : Character q) : ‖G a chi‖ ≤ Real.sqrt q :=
  (norm_G_le_sqrt_conductor ha chi).trans (Real.sqrt_le_sqrt
    (Nat.cast_le.mpr (BombieriVinogradov.DirichletCharacter.conductor_le_level chi)))

theorem ordinaryPacket_bound {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : Nat.Coprime a q)
    (d : PrimitiveQuadraticDatum) (e : ℂ) {eta : ℝ}
    (heta : |eta| ≤ deltaRadius N q) :
    ‖ordinaryPacket N a q d e eta‖ ≤
      (Real.sqrt q / q.totient) * (N : ℝ) * ordinaryMass N q d e := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  rw [ordinaryPacket, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q,
        Real.sqrt q * ∑ rho ∈ retainedValues chi (sourceT N) d e,
          (zeroMultiplicity chi rho : ℝ) * ((N : ℝ) * regularWeight N q rho) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro chi _
      rw [norm_mul]
      apply mul_le_mul (norm_G_le_sqrt_modulus ha chi) _ (norm_nonneg _)
        (Real.sqrt_nonneg _)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro rho hr
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (regular_Jrho_bound hN' (NeZero.pos q)
        (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.1 heta)
        (Nat.cast_nonneg _)
    _ = _ := by
      simp only [ordinaryMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _
      apply Finset.sum_congr rfl
      intro rho _
      ring

theorem paper_lowPacket_split {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) (eta : ℝ) :
    lowPacket N a q eta = retainedPacket N a q eta d e +
      if d.modulus ∣ q then
        (q.totient : ℂ)⁻¹ * G a (inducedAt d q) * Jrho N e eta else 0 := by
  have h := sum_split_retained (q := q) (omegaCutoff N q) d e
    (fun chi rho => G a chi * ((zeroMultiplicity chi rho : ℂ) * Jrho N rho eta))
  simp only [paper_induced_mem_iff hN hq hd] at h
  simp only [← Finset.mul_sum] at h
  have hh := congrArg (fun z : ℂ => (q.totient : ℂ)⁻¹ * z) h
  by_cases hdq : d.modulus ∣ q
  · simpa only [lowPacket, retainedPacket, zeroValueSum, zeroMultiplicity,
      if_pos hdq, show analyticOrderNatAt (inducedAt d q).LFunction e = 1 from
        paper_source_multiplicity hN hd hdq, Nat.cast_one, one_mul,
      mul_add, mul_assoc] using hh
  · simpa only [lowPacket, retainedPacket, zeroValueSum, zeroMultiplicity,
      if_neg hdq, add_zero] using hh

theorem ordinaryMass_le_original {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (d : PrimitiveQuadraticDatum) (e : ℂ)
    (hlow : retainedSum N q (omegaCutoff N q) d e ≤ 8.2e-10 / sourceL N)
    (hhigh : WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4) :
    ordinaryMass N q d e ≤ 8.2e-10 / sourceL N + 0.063 * q / sourceL N ^ 4 := by
  have hh :
      (∑ chi : Character q,
        ∑ rho ∈ (retainedValues chi (sourceT N) d e).filter
          (fun rho => omegaCutoff N q < |rho.im|),
            (zeroMultiplicity chi rho : ℝ) * highWeight N rho) ≤
        WeightedHighZeros.highSum N q := by
    change _ ≤ ∑ chi : Character q, ∑ rho ∈ WeightedHighZeros.highValues N chi,
      (analyticOrderNatAt chi.LFunction rho : ℝ) * ((N : ℝ) ^ (rho.re - 1) / |rho.im|)
    apply Finset.sum_le_sum
    intro chi _
    simp only [zeroMultiplicity, highWeight, baseWeight]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro rho hr
      obtain ⟨hr, hh⟩ := Finset.mem_filter.mp hr
      rw [WeightedHighZeros.highValues_eq_complete]
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1, hh.le⟩
    · intro rho _ _
      positivity
  rw [ordinaryMass_split hN]
  have h := add_le_add hlow
    (mul_le_mul_of_nonneg_left (hh.trans hhigh) (by norm_num : (0 : ℝ) ≤ 5))
  exact h.trans_eq (by ring)

theorem exceptional_J_third_moment_original {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {d : PrimitiveQuadraticDatum} {e : ℂ}
    (hd : PaperSource N d e) :
    (∫ eta in -deltaRadius N q..deltaRadius N q, ‖Jrho N (e.re : ℂ) eta‖ ^ 3) ≤
      (3 * 1.0302 * 1.0033 ^ 2 / Real.pi) * (N : ℝ) ^ (3 * e.re - 1) :=
  Jrho_cubic_source (nat_pos_of_exp_le hN) (exceptional_beta_ge_09957 hN hd)
    hd.2.2.2.1.le (deltaRadius_pos (exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)).le

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1
