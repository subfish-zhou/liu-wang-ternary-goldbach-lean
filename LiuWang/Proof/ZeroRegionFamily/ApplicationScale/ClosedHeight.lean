import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Consumer

/-! # 原P模数与闭T零点窗：共同尺度x=P*T，而非误用P/q窄窗 -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces
open LiuWang.Proof.Parameters

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale

theorem log_sourcePT {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    Real.log (sourceP N*sourceT N)=18*Real.log (Real.log (N : ℝ)) := by
  rw [Real.log_mul (sourceP_pos hN).ne' (sourceT_pos hN).ne']
  unfold sourceP sourceT sourceL
  rw [Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  ring

theorem sourcePT_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    20 ≤ Real.log (sourceP N*sourceT N) ∧ (q : ℝ) ≤ sourceP N*sourceT N := by
  have hT : 1 ≤ sourceT N := one_le_pow₀ (one_le_sourceL hN)
  constructor
  · rw [Real.log_mul (sourceP_pos hN).ne' (sourceT_pos hN).ne']
    linarith [log_sourceP_ge_twenty hN, Real.log_nonneg hT]
  · exact hq.trans (le_mul_of_one_le_right (sourceP_pos hN).le hT)

theorem region_sourcePT_of_window {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) {rho : ℂ}
    (hr : 1-1/(252*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ sourceT N) :
    LowOrderClosure.region (sourceP N*sourceT N) q rho := by
  constructor
  · rw [log_sourcePT hN]
    convert hr using 1
    ring
  · apply (le_div_iff₀ (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q)).mpr
    calc
      |rho.im| * (q : ℝ) ≤ sourceT N*sourceP N :=
        mul_le_mul ht hq (by positivity) (sourceT_pos hN).le
      _ = sourceP N*sourceT N := mul_comm _ _

theorem original_closed_height_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ (Real.log (N : ℝ))^3)
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1-1/(252*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ (Real.log (N : ℝ))^15)
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 :=
  zero_real_quadratic_simple (sourcePT_paid hN hq).1 (sourcePT_paid hN hq).2 chi
    (region_sourcePT_of_window hN hq hr ht) hpole hz

theorem original_closed_height_unique {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    Subsingleton (Σ z : {z : DirichletCharacter ℂ q × ℂ //
      1-1/(252*Real.log (Real.log (N : ℝ))) < z.2.re ∧
        |z.2.im| ≤ sourceT N ∧ (z.1 ≠ 1 ∨ z.2 ≠ 1) ∧ z.1.LFunction z.2=0},
      Fin (analyticOrderNatAt z.val.1.LFunction z.val.2)) := by
  refine ⟨?_⟩
  rintro ⟨z, i⟩ ⟨w, j⟩
  have he := single_modulus_unique (sourcePT_paid hN hq).1 (sourcePT_paid hN hq).2
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

theorem original_closed_height_family {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1-1/(252*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ sourceT N) (hpole : chi ≠ 1 ∨ rho ≠ 1)
    (hz : chi.LFunction rho=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ sourceP N ∧
      d.modulus=chi.conductor ∧ inducedAt d q=chi ∧ datumL d rho=0 ∧
      rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ sourceP N →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1-1/(252*Real.log (Real.log (N : ℝ))) < tau.re →
            |tau.im| ≤ sourceT N → (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau=0 →
              tau=rho ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧
                inducedAt d r=psi ∧ analyticOrderNatAt psi.LFunction tau=1 := by
  obtain ⟨d, _, hd, hi, hz', hr', hm, hall⟩ := family_fixed_source
    (sourcePT_paid hN hq).1 (sourcePT_paid hN hq).2 chi
    (region_sourcePT_of_window hN hq hr ht) hpole hz
  refine ⟨d, ?_, hd, hi, hz', hr', hm, ?_⟩
  · rw [hd]
    exact (show (chi.conductor : ℝ) ≤ q by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi).trans hq
  · intro r _ hr psi tau hb ht
    exact hall r (sourcePT_paid hN hr).2 psi tau (region_sourcePT_of_window hN hr hb ht)

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale
