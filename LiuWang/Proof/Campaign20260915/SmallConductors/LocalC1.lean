import LiuWang.Proof.Campaign20260915.SmallConductors.Through986
import LiuWang.Proof.Campaign20260915.OriginalRegion.SourceFreeConsumers
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.LocalSplit

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.Campaign20260915.SmallConductors

theorem quadratic_values_real {q : ℕ} (chi : Character q) (hsq : chi ^ 2 = 1) :
    ∀ n, (chi n).im = 0 := by
  intro n
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsq n with h | h | h <;> simp [h]

theorem localC1Data_exists {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    ∃ e : Option ((_chi : Character q) × ℂ), Source521523.LocalC1Data q e := by
  classical
  have hd := Source525526.theorem_two_low_domain hN hq
  have ho := Source525526.last_interval_order hN hq
  obtain ⟨e, he, hc⟩ := OriginalRegion.source_free_original_option hd.1 hd.2.1
  let toSigma : Character q × ℂ → ((_chi : Character q) × ℂ) :=
    fun z => ⟨z.1, z.2⟩
  let selected := e.map toSigma
  have hmap (z : (_chi : Character q) × ℂ) :
      selected = some z ↔ e = some (z.1, z.2) := by
    constructor
    · intro hz
      simpa [selected, toSigma, Function.comp_def] using
        congrArg (Option.map fun w : (_chi : Character q) × ℂ => (w.1, w.2)) hz
    · intro hz
      simpa [selected, toSigma] using congrArg (Option.map toSigma) hz
  have hclass (z : (_chi : Character q) × ℂ) (hz : selected = some z) :
      z.1 ≠ 1 ∧ z.1 ^ 2 = 1 ∧ z.2.im = 0 ∧
        analyticOrderNatAt z.1.LFunction z.2 = 1 :=
    hc (z.1, z.2) ((hmap z).mp hz)
  have hs (z : (_chi : Character q) × ℂ) (hz : selected = some z) :
      Source525526.lastUpper q < z.2.re ∧ z.2.re < 1 ∧
        |z.2.im| ≤ lowHeight ∧ z.1.LFunction z.2 = 0 := by
    simpa only [Source525526.lastUpper, hd.2.2] using
      (he z.1 z.2).mpr ((hmap z).mp hz)
  refine ⟨selected, ?_⟩
  constructor
  · intro z hz
    have hh := hs z hz
    apply Source521523.rectangle_mem.mpr
    exact mem_zeroValues.mpr ⟨hh.2.2.2, ⟨by linarith [ho.1, ho.2.1],
      hh.2.1, hh.2.2.1⟩, by linarith [ho.1, ho.2.1]⟩
  · exact fun z hz => (hs z hz).1
  · exact fun z hz => (hclass z hz).2.2.1
  · exact fun z hz => (hclass z hz).2.2.2
  · exact fun z hz => (hclass z hz).1
  · exact fun z hz => quadratic_values_real z.1 (hclass z hz).2.1
  · intro z hz
    let : NeZero z.1.conductor := ⟨z.1.conductor_ne_zero⟩
    have hh := hs z hz
    have hclass := hclass z hz
    have hp := z.1.primitiveCharacter_isPrimitive
    have hn := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one
      z.1 hclass.1
    have hsq := BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one
      z.1 hclass.2.1
    have hzero := primitive_LFunction_eq_zero_of_LFunction_eq_zero z.1 hclass.1
      (by linarith [ho.1, ho.2.1]) hh.2.2.2
    have hle : (z.1.conductor : ℝ) ≤ (q : ℝ) * lowHeight :=
      (by exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level z.1 :
        (z.1.conductor : ℝ) ≤ q).trans hd.2.1
    refine ⟨hp, hn, quadratic_values_real _ hsq, hzero, ?_, hle⟩
    have hr : (z.2.re : ℂ) = z.2 := by apply Complex.ext <;> simp [hclass.2.2.1]
    by_contra h
    exact primitive_le_986_original_region (by omega) z.1.primitiveCharacter
      hp hn hsq (by linarith [hd.1]) hle hh.1.le
      (by simpa only [hr] using hzero)
  · intro chi rho hz _h0 h1 ht hr
    apply (hmap ⟨chi, rho⟩).mpr
    apply (he chi rho).mp
    exact ⟨hr, h1, by simpa only [hd.2.2] using ht, hz⟩

#print axioms localC1Data_exists

end LiuWang.Proof.Campaign20260915.SmallConductors
