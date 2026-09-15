import LiuWang.Proof.Campaign20260915.SecondTerminal.ArcPayments
import LiuWang.Proof.Campaign20260915.HighSums.OriginalHighSum
import LiuWang.Proof.Campaign20260915.GammaLow.Consumers
import LiuWang.Proof.Campaign20260915.GammaHigh.Consumers
import LiuWang.Proof.SourceRoute.ThirdArc.Heights

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.DirichletZeroCount hiding heightKernel zeroValues mem_zeroValues
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

theorem original_high_packet_le_highSum {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ}
    (heta : |eta| ≤ 1 / ((q : ℝ) * sourceQ N)) :
    ‖originalHighPacket N q a eta‖ ≤
      (5 * (N : ℝ) * Real.sqrt q / q.totient) * WeightedHighZeros.highSum N q := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hn := natCast_pos_of_exp_le hN
  have hh := middle_height_domain hN hq
  have heta' := heta
  rw [approximationRadius_eq hN0 (NeZero.pos q)] at heta'
  have hg (chi : Character q) : ‖G a chi‖ ≤ Real.sqrt q :=
    (norm_G_le_sqrt_conductor ha chi).trans
      (Real.sqrt_le_sqrt (Nat.cast_le.mpr
        (BombieriVinogradov.DirichletCharacter.conductor_le_level chi)))
  have hsub (chi : Character q) :
      (zeroValues chi (sourceT N)).filter (fun rho => middleUpper N q < |rho.im|) ⊆
        WeightedHighZeros.highValues N chi := by
    rw [WeightedHighZeros.highValues_eq_complete]
    intro rho hr
    obtain ⟨hr, hu⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hr, hh.2.1.trans hu.le⟩
  have hJ (chi : Character q) (rho : ℂ)
      (hr : rho ∈ (zeroValues chi (sourceT N)).filter
        (fun rho => middleUpper N q < |rho.im|)) :
      ‖Jrho N rho eta‖ ≤
        5 * (N : ℝ) * ((N : ℝ) ^ (rho.re - 1) / |rho.im|) := by
    obtain ⟨hr, hu⟩ := Finset.mem_filter.mp hr
    have hb := mem_zeroValues.mp hr
    have hgamma : rho.im ≠ 0 := abs_pos.mp ((hh.1.trans_le hh.2.1).trans hu)
    have hnear := SourceRoute.ThirdArc.near_condition hN0 heta'
      (show SourceRoute.ThirdArc.middleHeight N q ≤ |rho.im| from hu.le)
    have h := OscillatoryBounds.Jrho_near (nat_pos_of_exp_le hN) hb.2.1.le hgamma hnear
    apply h.trans_eq
    rw [Real.rpow_sub_one hn.ne']
    field_simp
  rw [originalHighPacket, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, Real.sqrt q *
        ∑ rho ∈ (zeroValues chi (sourceT N)).filter (fun rho => middleUpper N q < |rho.im|),
          5 * (N : ℝ) * ((analyticOrderNatAt chi.LFunction rho : ℝ) *
            ((N : ℝ) ^ (rho.re - 1) / |rho.im|)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro chi _
      rw [norm_mul]
      apply mul_le_mul (hg chi) _ (norm_nonneg _) (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro rho hr
      rw [norm_mul, Complex.norm_natCast]
      exact (mul_le_mul_of_nonneg_left (hJ chi rho hr) (Nat.cast_nonneg _)).trans_eq (by ring)
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, Real.sqrt q *
        ∑ rho ∈ WeightedHighZeros.highValues N chi,
          5 * (N : ℝ) * ((analyticOrderNatAt chi.LFunction rho : ℝ) *
            ((N : ℝ) ^ (rho.re - 1) / |rho.im|)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro chi _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg (hsub chi) (by intros; positivity)
    _ = _ := by
      simp only [WeightedHighZeros.highSum, WeightedHighZeros.bandSum,
        WeightedHighZeros.highValues, Finset.mul_sum]
      ring

theorem original_high_T1_input {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2) :
    ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      MultiZeroRepulsion.strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4 := by
  intro y hy
  have hd := exact_scale_domain hN hq hy.1
  have hx : 8000000000 ≤ (q : ℝ) * y := by linarith [hd.2.1]
  have hqx : (q : ℝ) ≤ (q : ℝ) * y :=
    le_mul_of_one_le_right (Nat.cast_nonneg q) hd.1
  have h := GammaLow.original_T1_strict_family_le_four hx hqx hRS
    (GammaHigh.source_gammaHalfDifference_high hx)
  have he : (q : ℝ) * y / q = y := by
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    field_simp
  simpa only [he] using h

theorem original_high_packet_payment {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ}
    (heta : |eta| ≤ 1 / ((q : ℝ) * sourceQ N))
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N))
    (hlocal : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    ‖originalHighPacket N q a eta‖ ≤
      (5 * 0.0126 * sourceNu (sourceP N)) * (N : ℝ) /
        (sourceL N ^ (2 : ℕ) * Real.sqrt (sourceL N)) := by
  have hL : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
  have hnu0 : 0 ≤ sourceNu (sourceP N) := (by positivity : 0 ≤ (q : ℝ) / q.totient).trans hnu
  have hT7 (alpha y : ℝ) (ha0 : 1 / 2 ≤ alpha) (ha1 : alpha < 1)
      (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :=
    hseven y hy alpha ha0 ha1
  have hreal : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ), rho ∈ DirichletZeroCount.zeroValues chi 0 y →
        1 - (1 / Source3536.c1) / Real.log ((q : ℝ) * y) < rho.re → rho.im = 0 := by
    intro y hy chi rho hr hn
    have hb := DirichletZeroCount.mem_zeroValues.mp hr
    exact hlocal y hy chi rho hb.1 hb.2.1.1 hb.2.1.2.1 hb.2.1.2.2
      (by simpa only [Source3536.c1, div_div] using hn)
  have hh := HighSums.highSum_original_of_T1_T7_near_one_real hN hq
    (original_high_T1_input hN hq hRS) hT7 hreal
  have hp := (original_high_packet_le_highSum hN hq ha heta).trans
    (mul_le_mul_of_nonneg_left hh (by positivity))
  have hs : Real.sqrt q ≤ sourceL N * Real.sqrt (sourceL N) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hL.le]
    change (q : ℝ) ≤ sourceL N ^ (3 : ℕ) at hq
    nlinarith only [hq]
  have hratio := mul_le_mul hnu hs (Real.sqrt_nonneg q) hnu0
  have hb := mul_le_mul_of_nonneg_right hratio
    (show 0 ≤ (5 * 0.0126 : ℝ) * (N : ℝ) / sourceL N ^ (4 : ℕ) by positivity)
  have he : (sourceNu (sourceP N) * (sourceL N * Real.sqrt (sourceL N))) *
      ((5 * 0.0126 : ℝ) * (N : ℝ) / sourceL N ^ (4 : ℕ)) =
      (5 * 0.0126 * sourceNu (sourceP N)) * (N : ℝ) /
        (sourceL N ^ (2 : ℕ) * Real.sqrt (sourceL N)) := by
    have hs0 := Real.sqrt_pos.mpr hL
    field_simp
    rw [Real.sq_sqrt hL.le]
  rw [he] at hb
  simp only [div_eq_mul_inv] at hp hb ⊢
  nlinarith only [hp, hb]

theorem S_le_original_low_remaining {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) (eta : ℝ)
    (hlo : deltaRadius N q < |eta|)
    (hhi : |eta| ≤ 1 / ((q : ℝ) * sourceQ N))
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N))
    (hlocal : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      (10 * (N : ℝ) / (3.36 * sourceP N)) * sourceNu (sourceP N) +
      4.3368 * (N : ℝ) / sourceL N ^ (6 : ℕ) +
      ‖originalLowPacket N q a eta‖ +
      (0.00104 + 0.032281 + 8 * 0.0000076 + 0.000021 + 0.000024 + 0.022445) *
        (N : ℝ) / sourceL N +
      (5 * 0.0126 * sourceNu (sourceP N)) * (N : ℝ) /
        (sourceL N ^ (2 : ℕ) * Real.sqrt (sourceL N)) := by
  have hd := middle_height_domain hN hq
  have hs := S_le_original_low_high hN hq hi eta hlo hhi hseven hnu
    (fun y hy => hlocal y ⟨hy.1, hy.2.trans hd.2.2⟩)
  have hh := original_high_packet_payment hN hq hi.2.2 hhi hRS hseven hnu hlocal
  linarith only [hs, hh]

#print axioms original_high_packet_le_highSum
#print axioms original_high_T1_input
#print axioms original_high_packet_payment
#print axioms S_le_original_low_remaining

end LiuWang.Proof.Campaign20260915.SecondTerminal
