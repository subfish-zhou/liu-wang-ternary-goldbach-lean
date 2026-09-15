import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.SingleScale
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.BaseConsumer
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526.Consumer
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.CountFubini

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523

def primedZeros (q : ℕ) [NeZero q] (e : Option ((_chi : Character q) × ℂ)) :
    Finset ((_chi : Character q) × ℂ) :=
  (rectangleZeros q (1 / 2) lowHeight).filter (fun z => some z ≠ e)

def primedSigma4 (N q : ℕ) [NeZero q] (e : Option ((_chi : Character q) × ℂ)) : ℝ :=
  ((N : ℝ) * Real.sqrt q / q.totient) *
    ∑ z ∈ primedZeros q e, (analyticOrderNatAt z.1.LFunction z.2 : ℝ) *
      (lowCoefficient z.2.re * (N : ℝ) ^ (z.2.re - 1))

def selectedBill (N q : ℕ) [NeZero q] (e : Option ((_chi : Character q) × ℂ)) : ℝ :=
  match e with
  | none => 0
  | some z => (Real.sqrt q / q.totient) *
      ((analyticOrderNatAt z.1.LFunction z.2 : ℝ) * lowCoefficient z.2.re *
        (N : ℝ) ^ z.2.re)

/-- The uninstantiated local LWD Lemma 2.1 data at x=q*(10000*pi). -/
structure LocalC1Data (q : ℕ) [NeZero q] (e : Option ((_chi : Character q) × ℂ)) : Prop where
  selected_mem : ∀ z, e = some z → z ∈ rectangleZeros q (1 / 2) lowHeight
  selected_right : ∀ z, e = some z → Source525526.lastUpper q < z.2.re
  selected_real : ∀ z, e = some z → z.2.im = 0
  selected_simple : ∀ z, e = some z → analyticOrderNatAt z.1.LFunction z.2 = 1
  selected_nonprincipal : ∀ z, e = some z → z.1 ≠ 1
  selected_real_character : ∀ z, e = some z → ∀ n, (z.1 n).im = 0
  primitive_source : ∀ z, e = some z →
    z.1.primitiveCharacter.IsPrimitive ∧ z.1.primitiveCharacter ≠ 1 ∧
      (∀ n, (z.1.primitiveCharacter n).im = 0) ∧
      z.1.primitiveCharacter.LFunction z.2 = 0 ∧
      987 ≤ z.1.conductor ∧ (z.1.conductor : ℝ) ≤ (q : ℝ) * lowHeight
  region : ∀ (chi : Character q) (rho : ℂ),
    chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ lowHeight →
    Source525526.lastUpper q < rho.re → e = some ⟨chi, rho⟩

theorem rectangle_mem {q : ℕ} [NeZero q] {z : (_chi : Character q) × ℂ} :
    z ∈ rectangleZeros q (1 / 2) lowHeight ↔ z.2 ∈ zeroValues z.1 (1 / 2) lowHeight := by
  simp [rectangleZeros]

theorem primed_right_boundary {q : ℕ} [NeZero q]
    {e : Option ((_chi : Character q) × ℂ)} (hloc : LocalC1Data q e)
    {z : (_chi : Character q) × ℂ} (hz : z ∈ primedZeros q e) :
    z.2.re ≤ Source525526.lastUpper q := by
  obtain ⟨hz, he⟩ := Finset.mem_filter.mp hz
  obtain ⟨hzero, ⟨h0, h1, hh⟩, _⟩ := mem_zeroValues.mp (rectangle_mem.mp hz)
  by_contra hb
  exact he (hloc.region z.1 z.2 hzero h0 h1 hh (lt_of_not_ge hb)).symm

theorem sigma4_exact_local_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N)
    {e : Option ((_chi : Character q) × ℂ)} (hloc : LocalC1Data q e) :
    sigma4 N q = selectedBill N q e + primedSigma4 N q e := by
  rw [sigma4_eq_low_family hN hq1]
  have hsum : (∑ chi : Character q, ∑ rho ∈ zeroValues chi (1 / 2) lowHeight,
      (analyticOrderNatAt chi.LFunction rho : ℝ) *
        (lowCoefficient rho.re * (N : ℝ) ^ (rho.re - 1))) =
      ∑ z ∈ rectangleZeros q (1 / 2) lowHeight,
        (analyticOrderNatAt z.1.LFunction z.2 : ℝ) *
          (lowCoefficient z.2.re * (N : ℝ) ^ (z.2.re - 1)) := by
    rw [rectangleZeros, Finset.sum_sigma]
  rw [hsum]
  cases e with
  | none => simp [selectedBill, primedSigma4, primedZeros]
  | some z =>
    have hz := hloc.selected_mem z rfl
    have hf : primedZeros q (some z) = (rectangleZeros q (1 / 2) lowHeight).erase z := by
      ext w
      simp [primedZeros, Finset.mem_erase, and_comm]
    have hi := Finset.sum_erase_add (s := rectangleZeros q (1 / 2) lowHeight)
      (f := fun w => (analyticOrderNatAt w.1.LFunction w.2 : ℝ) *
        (lowCoefficient w.2.re * (N : ℝ) ^ (w.2.re - 1))) hz
    have hw : (N : ℝ) * (lowCoefficient z.2.re * (N : ℝ) ^ (z.2.re - 1)) =
        lowCoefficient z.2.re * (N : ℝ) ^ z.2.re :=
      WeightedLowZeros.weight_mul_endpoint (nat_pos_of_exp_le hN) z.2.re
    unfold primedSigma4
    rw [hf, ← hi]
    simp only [selectedBill]
    have hm := congrArg (fun v : ℝ => (Real.sqrt q / q.totient) *
      (analyticOrderNatAt z.1.LFunction z.2 : ℝ) * v) hw
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hm]

theorem selectedBill_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    {e : Option ((_chi : Character q) × ℂ)} (hloc : LocalC1Data q e) :
    selectedBill N q e ≤ (0.11585 : ℝ) * N / sourceL N := by
  cases e with
  | none =>
    have hL := sourceL_ge_3100 hN
    simp only [selectedBill]
    positivity
  | some z =>
    have hz := mem_zeroValues.mp (rectangle_mem.mp (hloc.selected_mem z rfl))
    simp only [selectedBill, hloc.selected_simple z rfl, Nat.cast_one, one_mul]
    have h := equation_5_21_original hN hq htotient hz.2.2 hz.2.1.2.1
    nlinarith only [h]

theorem actual_simple_lowKernel_original {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ zeroValues chi (1 / 2) lowHeight)
    (hsimple : analyticOrderNatAt chi.LFunction rho = 1) :
    (Real.sqrt q / q.totient) *
      ((analyticOrderNatAt chi.LFunction rho : ℝ) * lowKernel N rho) ≤
        (0.11585 : ℝ) * N / sourceL N := by
  have hz := mem_zeroValues.mp hr
  rw [hsimple, Nat.cast_one, one_mul]
  have h := equation_5_21_original hN hq htotient hz.2.2 hz.2.1.2.1
  simpa only [lowKernel, lowCoefficient, mul_assoc] using h

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523
