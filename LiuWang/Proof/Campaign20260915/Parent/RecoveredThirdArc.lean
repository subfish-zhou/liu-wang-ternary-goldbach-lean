import LiuWang.Proof.Campaign20260915.ThirdBudgets.MiddleRealCreditPayment
import LiuWang.Proof.Campaign20260915.ThirdBudgets.Sigma6Payment
import LiuWang.Proof.Campaign20260915.Totient.M6
import LiuWang.Proof.Campaign20260915.OriginalRegion.SourceFreeConsumers
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.Assembly
import LiuWang.Proof.MinorArcEnergy.Fourth

/-! Parent-only integration of the original three paid bands. The density,
totient and small-conductor inputs remain explicit. No uncredited middle
integral, real-tail vanishing, or desired pointwise bound is an input. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Parent.RecoveredThirdArc

/-- Only the unpaid conductor field is supplied; the original region constructs
all other fields, including the common selected zero and its multiplicity. -/
theorem localC1Data_of_conductor {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (h987 : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ lowHeight →
      Source525526.lastUpper q < rho.re → 987 ≤ chi.conductor) :
    ∃ e : Option ((_chi : Character q) × ℂ), Source521523.LocalC1Data q e := by
  classical
  have hd := Source525526.theorem_two_low_domain hN hq
  have ho := Source525526.last_interval_order hN hq
  obtain ⟨ep, hep, hcp⟩ := OriginalRegion.source_free_original_option hd.1 hd.2.1
  let e : Option ((_chi : Character q) × ℂ) := ep.map (fun z => ⟨z.1, z.2⟩)
  have hm (z : (_chi : Character q) × ℂ) : e = some z ↔ ep = some (z.1, z.2) := by
    cases ep with
    | none => simp [e]
    | some w =>
      cases z
      cases w
      simp [e]
  have he (chi : Character q) (rho : ℂ) :
      (1 - 1 / (9.645908801 * Real.log ((q : ℝ) * lowHeight)) < rho.re ∧
        rho.re < 1 ∧ |rho.im| ≤ (q : ℝ) * lowHeight / q ∧ chi.LFunction rho = 0) ↔
        e = some ⟨chi, rho⟩ := (hep chi rho).trans (hm ⟨chi, rho⟩).symm
  have hc (z : (_chi : Character q) × ℂ) (hz : e = some z) :
      z.1 ≠ 1 ∧ z.1 ^ 2 = 1 ∧ z.2.im = 0 ∧ analyticOrderNatAt z.1.LFunction z.2 = 1 :=
    hcp (z.1, z.2) ((hm z).mp hz)
  have hs (z : (_chi : Character q) × ℂ) (hz : e = some z) :
      Source525526.lastUpper q < z.2.re ∧ z.2.re < 1 ∧
        |z.2.im| ≤ lowHeight ∧ z.1.LFunction z.2 = 0 := by
    simpa only [Source525526.lastUpper, hd.2.2] using (he z.1 z.2).mpr hz
  have hreal (chi : Character q) (hsq : chi ^ 2 = 1) : ∀ n, (chi n).im = 0 := by
    intro n
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsq n with h | h | h <;> simp [h]
  refine ⟨e, ?_⟩
  constructor
  · intro z hz
    have hh := hs z hz
    exact Source521523.rectangle_mem.mpr (mem_zeroValues.mpr
      ⟨hh.2.2.2, ⟨by linarith [ho.1, ho.2.1], hh.2.1, hh.2.2.1⟩,
        by linarith [ho.1, ho.2.1]⟩)
  · exact fun z hz => (hs z hz).1
  · exact fun z hz => (hc z hz).2.2.1
  · exact fun z hz => (hc z hz).2.2.2
  · exact fun z hz => (hc z hz).1
  · exact fun z hz => hreal z.1 (hc z hz).2.1
  · intro z hz
    have hh := hs z hz
    have hclass := hc z hz
    have hn := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one
      z.1 hclass.1
    have hsq := BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one
      z.1 hclass.2.1
    have hzero := BombieriVinogradov.SiegelWalfisz.primitive_LFunction_eq_zero_of_LFunction_eq_zero
      z.1 hclass.1 (by linarith [ho.1, ho.2.1]) hh.2.2.2
    have hle : (z.1.conductor : ℝ) ≤ (q : ℝ) * lowHeight :=
      (by exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level z.1 :
        (z.1.conductor : ℝ) ≤ q).trans hd.2.1
    exact ⟨z.1.primitiveCharacter_isPrimitive, hn,
      fun n => by
        rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsq n with h | h | h <;> simp [h],
      hzero, h987 z.1 z.2 hh.2.2.2 (by linarith [ho.1, ho.2.1])
        hh.2.1 hh.2.2.1 hh.1, hle⟩
  · intro chi rho hz _h0 h1 ht hr
    exact (he chi rho).mp ⟨hr, h1, by simpa only [hd.2.2] using ht, hz⟩

/-- The common T7 input is used only at its original legal heights. -/
theorem density_inputs {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hT7 : ∀ (y alpha : ℝ),
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      1 / 2 ≤ alpha → alpha < 1 →
      (familyCount q alpha y : ℝ) ≤ sourceDensity q y alpha) :
    (∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      (familyCount q alpha (10000 * Real.log q) : ℝ) ≤
        sourceDensity q (10000 * Real.log q) alpha) ∧
    (∀ r ∈ Set.Icc (max (100000 / (q : ℝ)) (10000 * Real.log q)) (sourceT N),
      ∀ alpha ∈ Set.Icc (59 / 60 : ℝ) (sourceCutoff q 0.478 r),
        (familyCount q alpha r : ℝ) ≤ sourceDensity q r alpha) := by
  have hs := (M3_density_logs hN hq hq1).1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqbig : 100000 ≤ (q : ℝ) := by
    linarith [OriginalRegion.sourceP_original_scale hN]
  have hdiv : 100000 / (q : ℝ) ≤ 1 := (div_le_one hqpos).mpr hqbig
  have hlegal : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤
      10000 * Real.log q := max_le (by linarith) le_rfl
  have hheight : lowHeight ≤ 10000 * Real.log (q : ℝ) := by
    unfold lowHeight
    nlinarith [Real.pi_lt_four]
  constructor
  · intro alpha ha
    apply hT7 _ _ hlegal (by linarith [ha.1])
    have hp : 0 < 0.478 / Real.log ((q : ℝ) * lowHeight) :=
      div_pos (by norm_num) (by linarith [M3_log_product_ge_thirty hN hq le_rfl])
    linarith [ha.2]
  · intro r hr alpha ha
    have hy : lowHeight ≤ r := hheight.trans ((le_max_right _ _).trans hr.1)
    apply hT7 _ _ hr.1 (by linarith [ha.1])
    have hp : 0 < 0.478 / Real.log ((q : ℝ) * r) :=
      div_pos (by norm_num) (by linarith [M3_log_product_ge_thirty hN hq hy])
    have hau : alpha ≤ 1 - 0.478 / Real.log ((q : ℝ) * r) := ha.2
    linarith only [hau, hp]

/-- Original 0.5033 bound for both literal sums, on one q,a,eta witness. -/
theorem S_and_primeS_original_fixed {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N))
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hT7 : ∀ (y alpha : ℝ),
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      1 / 2 ≤ alpha → alpha < 1 →
      (familyCount q alpha y : ℝ) ≤ sourceDensity q y alpha)
    (h987 : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ lowHeight →
      Source525526.lastUpper q < rho.re → 987 ≤ chi.conductor) :
    ‖S N (rationalCenter a q + eta)‖ ≤ 0.5033 * (N : ℝ) / sourceL N ∧
      ‖primeS N (rationalCenter a q + eta)‖ ≤ 0.5033 * (N : ℝ) / sourceL N := by
  obtain ⟨hlow, hdensity⟩ := density_inputs hN hq.le hq1 hT7
  obtain ⟨e, he⟩ := localC1Data_of_conductor hN hq.le h987
  have hnu := Totient.third_sourceNu_le_sixth hN hq.le hq1
  have hlocal : ∀ y ∈ Set.Icc lowHeight (middleHeight N q),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0 := by
    intro y hy chi rho hz _h0 h1 ht hr
    exact OriginalRegion.moving_original_real
      (by linarith [(M3_table_domain hN hq.le hy.1).1])
      (lowHeight_ge_one.trans hy.1) chi rho hz h1 ht hr
  have h4 := Source521523.equation_5_27_original_conditional hN hq.le hq1
    htotient hlow he
  have h5 := ThirdBudgets.sigma5_original_paid hN hq.le hq1 hdensity htotient hnu hlocal
  have h6 := ThirdBudgets.sigma6_original_paid hN hq.le hq1 hdensity htotient hnu
    (OriginalRegion.original_high_local_source_free hN hq.le hq1)
  have hS := S_principal_and_error_paid hN hi hq hq1 heta
  have hprime := primeS_M3_fixed hN hi hq hq1 heta
  have hp := principal_bound_paid hN hq.le
  have hNL : 0 ≤ (N : ℝ) / sourceL N :=
    div_nonneg (Nat.cast_nonneg N) (sourceL_pos (exp_2000_le_of_exp_3100_le hN)).le
  ring_nf at h4 h5 h6 hS hprime hp hNL ⊢
  constructor <;> linarith only [h4, h5, h6, hS, hprime, hp, hNL]

section WholeArc

variable {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (htotient : ∀ q : ℕ, sourceP N < (q : ℝ) → (q : ℝ) ≤ sourceP1 N →
      (q : ℝ) / q.totient ≤ sourceNu q)
    (hT7 : ∀ (q : ℕ) [NeZero q], sourceP N < (q : ℝ) →
      (q : ℝ) ≤ sourceP1 N → ∀ (y alpha : ℝ),
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      1 / 2 ≤ alpha → alpha < 1 →
      (familyCount q alpha y : ℝ) ≤ sourceDensity q y alpha)
    (h987 : ∀ (q : ℕ) [NeZero q], sourceP N < (q : ℝ) →
      (q : ℝ) ≤ sourceP1 N → ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ lowHeight →
      Source525526.lastUpper q < rho.re → 987 ≤ chi.conductor)

include hN htotient hT7 h987

/-- M3 itself, without choosing separate witnesses for its three budgets. -/
theorem M3_original_pointwise {alpha : ℝ} (ha : alpha ∈ M3 N) :
    ‖S N alpha‖ ≤ 0.5033 * (N : ℝ) / sourceL N ∧
      ‖primeS N alpha‖ ≤ 0.5033 * (N : ℝ) / sourceL N := by
  obtain ⟨q, a, eta, hq0, hq1, hi, he, heta⟩ := LiuWang.Proof.ArcGeometry.M3_eta_range ha
  have hq := LiuWang.Proof.ArcGeometry.sourceIndex_den_pos hi
  let : NeZero q := ⟨hq.ne'⟩
  rw [approximationRadius_eq (exp_2000_le_of_exp_3100_le hN) hq] at heta
  rw [he]
  exact S_and_primeS_original_fixed hN hi hq0 hq1 heta
    (htotient q hq0 hq1) (hT7 q hq0 hq1) (h987 q hq0 hq1)

/-- The literal third-arc local-energy input required by the parent root. -/
theorem M3_original_local_energy :
    ‖∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.5033 * (N : ℝ) / sourceL N) * ∫ alpha in M3 N, ‖S N alpha‖ ^ 2 :=
  LiuWang.Proof.MinorArcEnergy.norm_setIntegral_le_local_energy N
    (LiuWang.Proof.ArcGeometry.measurableSet_M3 N)
    (LiuWang.Proof.ArcGeometry.M3_subset_sourceDomain (exp_2000_le_of_exp_3100_le hN))
    (fun _ ha => (M3_original_pointwise hN htotient hT7 h987 ha).1)

end WholeArc

#check @localC1Data_of_conductor
#check @density_inputs
#check @S_and_primeS_original_fixed
#check @M3_original_pointwise
#check @M3_original_local_energy
#print axioms localC1Data_of_conductor
#print axioms density_inputs
#print axioms S_and_primeS_original_fixed
#print axioms M3_original_pointwise
#print axioms M3_original_local_energy

end LiuWang.Proof.Campaign20260915.Parent.RecoveredThirdArc
