import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Family
import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.ClosedHeight

/-! # 全x>=10完整R40/3，及同原P/PT窗口的更宽实际消费者 -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces
open LiuWang.Proof.Parameters

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation

theorem single_modulus {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) :
    Subsingleton (countedZeros x q) ∧
      ∀ (chi : DirichletCharacter ℂ q) (rho : ℂ),
        1-3/(40*Real.log x) < rho.re → |rho.im| ≤ x/(q : ℝ) →
          (chi ≠ 1 ∨ rho ≠ 1) → chi.LFunction rho=0 →
            chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 :=
  ⟨countedZeros_subsingleton hx hq, fun chi _ hr ht hp hz =>
    zero_real_quadratic_simple hx hq chi hr ht hp hz⟩

theorem family_from_actual_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1-3/(40*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ x ∧
      d.modulus=chi.conductor ∧ inducedAt d q=chi ∧ datumL d rho=0 ∧
      rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1-3/(40*Real.log x) < tau.re → |tau.im| ≤ x/(r : ℝ) →
            (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau=0 →
              tau=rho ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧
                inducedAt d r=psi ∧ analyticOrderNatAt psi.LFunction tau=1 := by
  obtain ⟨d, hd, hc, hi, hdz, hir, hm, hall⟩ := family_fixed_source hx hq chi ⟨hr, ht⟩ hpole hz
  exact ⟨d, hd, hc, hi, hdz, hir, hm, fun r _ hr psi tau hb ht =>
    hall r hr psi tau ⟨hb, ht⟩⟩

theorem region_fourteen_subset {x : ℝ} {q : ℕ} (hx : 10 ≤ x) {rho : ℂ}
    (hr : LowOrderClosure.region x q rho) : region x q rho := by
  have hL : 0 < Real.log x := by linarith [RealClosure.log_scale_ge_34_15 hx]
  refine ⟨?_, hr.2⟩
  have hh : 1/(14*Real.log x) ≤ 3/(40*Real.log x) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  linarith [hr.1]

theorem sourceP_ge_ten {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) : 10 ≤ sourceP N := by
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2000) (sourceL_ge_2000 hN) (n := 3)
  exact (by norm_num : (10 : ℝ) ≤ 2000^3).trans hh

theorem region_sourceP_iff {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (q : ℕ) (rho : ℂ) :
    region (sourceP N) q rho ↔
      1-1/(40*Real.log (Real.log (N : ℝ))) < rho.re ∧
        |rho.im| ≤ (Real.log (N : ℝ))^3/(q : ℝ) := by
  have hL : 0 < Real.log (sourceL N) := Real.log_pos (by linarith [sourceL_ge_2000 hN])
  unfold region sourceP sourceL
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have he : 3/(40*(3*Real.log (Real.log (N : ℝ))))=1/(40*Real.log (Real.log (N : ℝ))) := by
    field_simp
  rw [he]

theorem sourceP_zero_real_simple {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ (Real.log (N : ℝ))^3)
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1-1/(40*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ (Real.log (N : ℝ))^3/(q : ℝ))
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 := by
  have hw := (region_sourceP_iff hN q rho).mpr ⟨hr, ht⟩
  exact zero_real_quadratic_simple (sourceP_ge_ten hN) hq chi hw.1 hw.2 hpole hz

theorem sourceP_single_modulus {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    Subsingleton (countedZeros (sourceP N) q) :=
  countedZeros_subsingleton (sourceP_ge_ten hN) hq

theorem sourceP_fixed_family {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1-1/(40*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ sourceP N/(q : ℝ))
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ sourceP N ∧
      d.modulus=chi.conductor ∧ inducedAt d q=chi ∧ datumL d rho=0 ∧
      rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ sourceP N →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1-1/(40*Real.log (Real.log (N : ℝ))) < tau.re →
            |tau.im| ≤ sourceP N/(r : ℝ) → (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau=0 →
              tau=rho ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧
                inducedAt d r=psi ∧ analyticOrderNatAt psi.LFunction tau=1 := by
  obtain ⟨d, hd, hc, hi, hdz, hir, hm, hall⟩ := family_fixed_source (sourceP_ge_ten hN) hq chi
    ((region_sourceP_iff hN q rho).mpr ⟨hr, ht⟩) hpole hz
  exact ⟨d, hd, hc, hi, hdz, hir, hm, fun r _ hr psi tau hb ht =>
    hall r hr psi tau ((region_sourceP_iff hN r tau).mpr ⟨hb, ht⟩)⟩

theorem region_sourcePT_of_window {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) {rho : ℂ}
    (hr : 1-1/(240*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ sourceT N) : region (sourceP N*sourceT N) q rho := by
  constructor
  · rw [ApplicationScale.log_sourcePT hN]
    have he : 3/(40*(18*Real.log (Real.log (N : ℝ))))=
        1/(240*Real.log (Real.log (N : ℝ))) := by field_simp; ring
    rwa [he]
  · apply (le_div_iff₀ (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q)).mpr
    calc
      |rho.im| * (q : ℝ) ≤ sourceT N*sourceP N :=
        mul_le_mul ht hq (by positivity) (sourceT_pos hN).le
      _ = sourceP N*sourceT N := mul_comm _ _

theorem sourcePT_ge_ten {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    10 ≤ sourceP N*sourceT N :=
  (sourceP_ge_ten hN).trans (le_mul_of_one_le_right (sourceP_pos hN).le
    (one_le_pow₀ (one_le_sourceL hN)))

theorem original_closed_height_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ (Real.log (N : ℝ))^3)
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1-1/(240*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ (Real.log (N : ℝ))^15)
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 := by
  have hw := region_sourcePT_of_window hN hq hr ht
  exact zero_real_quadratic_simple (sourcePT_ge_ten hN) (ApplicationScale.sourcePT_paid hN hq).2
    chi hw.1 hw.2 hpole hz

theorem original_closed_height_family {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1-1/(240*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ sourceT N) (hpole : chi ≠ 1 ∨ rho ≠ 1)
    (hz : chi.LFunction rho=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ sourceP N ∧
      d.modulus=chi.conductor ∧ inducedAt d q=chi ∧ datumL d rho=0 ∧
      rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ sourceP N →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1-1/(240*Real.log (Real.log (N : ℝ))) < tau.re →
            |tau.im| ≤ sourceT N → (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau=0 →
              tau=rho ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧
                inducedAt d r=psi ∧ analyticOrderNatAt psi.LFunction tau=1 := by
  obtain ⟨d, _, hd, hi, hz', hr', hm, hall⟩ := family_fixed_source
    (sourcePT_ge_ten hN) (ApplicationScale.sourcePT_paid hN hq).2 chi
    (region_sourcePT_of_window hN hq hr ht) hpole hz
  refine ⟨d, ?_, hd, hi, hz', hr', hm, ?_⟩
  · rw [hd]
    exact (show (chi.conductor : ℝ) ≤ q by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi).trans hq
  · intro r _ hr psi tau hb ht
    exact hall r (ApplicationScale.sourcePT_paid hN hr).2 psi tau
      (region_sourcePT_of_window hN hr hb ht)

theorem original_closed_height_unique {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    Subsingleton (Σ z : {z : DirichletCharacter ℂ q × ℂ //
      1-1/(240*Real.log (Real.log (N : ℝ))) < z.2.re ∧
        |z.2.im| ≤ sourceT N ∧ (z.1 ≠ 1 ∨ z.2 ≠ 1) ∧ z.1.LFunction z.2=0},
      Fin (analyticOrderNatAt z.val.1.LFunction z.val.2)) := by
  refine ⟨?_⟩
  rintro ⟨z, i⟩ ⟨w, j⟩
  have he := single_modulus_unique (sourcePT_ge_ten hN) (ApplicationScale.sourcePT_paid hN hq).2
    z.val.1 w.val.1
    (region_sourcePT_of_window hN hq z.property.1 z.property.2.1)
    (region_sourcePT_of_window hN hq w.property.1 w.property.2.1)
    z.property.2.2.1 w.property.2.2.1 z.property.2.2.2 w.property.2.2.2
  have hzw : z=w := Subtype.ext (Prod.ext he.1 he.2)
  subst w
  have hm := (original_closed_height_zero hN hq z.val.1 z.property.1 z.property.2.1
    z.property.2.2.1 z.property.2.2.2).2.2.2
  have hij : i=j := by
    apply Fin.ext
    have hi : i.val < 1 := lt_of_lt_of_le i.isLt hm.le
    have hj : j.val < 1 := lt_of_lt_of_le j.isLt hm.le
    omega
  subst j
  rfl

theorem modulus_one_no_zero {x : ℝ} (hx : 10 ≤ x) {rho : ℂ}
    (hr : 1-3/(40*Real.log x) < rho.re) (ht : |rho.im| ≤ x) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ 1).LFunction rho ≠ 0 :=
  principal_no_zero hx hr (by simpa using ht) hpole

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation
