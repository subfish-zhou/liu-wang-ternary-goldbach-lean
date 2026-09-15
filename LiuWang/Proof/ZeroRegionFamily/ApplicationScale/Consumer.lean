import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Family
import LiuWang.Proof.Parameters.Main

/-! # 完整R14首次覆盖原圆法P=(log N)^3，N>=exp2000 -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces
open LiuWang.Proof.Parameters

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale

theorem single_modulus_fourteen {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 20 ≤ Real.log x) (hq : (q : ℝ) ≤ x) :
    Subsingleton (LowOrderClosure.countedZeros x q) ∧
      ∀ (chi : DirichletCharacter ℂ q) (rho : ℂ),
        1-1/(14*Real.log x) < rho.re → |rho.im| ≤ x/(q : ℝ) →
          (chi ≠ 1 ∨ rho ≠ 1) → chi.LFunction rho=0 →
            chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 :=
  ⟨countedZeros_subsingleton hx hq,
    fun chi _ hr ht hp hz => zero_real_quadratic_simple hx hq chi ⟨hr, ht⟩ hp hz⟩

theorem log_sourceP_ge_twenty {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    20 ≤ Real.log (sourceP N) := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2^10)
    (show (2 : ℝ)^10 ≤ sourceL N by linarith [sourceL_ge_2000 hN])
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  rw [sourceP, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith [Real.log_two_gt_d9]

theorem region_sourceP_iff (N q : ℕ) (rho : ℂ) :
    LowOrderClosure.region (sourceP N) q rho ↔
      1-1/(42*Real.log (Real.log (N : ℝ))) < rho.re ∧
        |rho.im| ≤ (Real.log (N : ℝ))^3/(q : ℝ) := by
  unfold LowOrderClosure.region sourceP sourceL
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  ring_nf

theorem sourceP_single_modulus {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    Subsingleton (LowOrderClosure.countedZeros (sourceP N) q) :=
  countedZeros_subsingleton (log_sourceP_ge_twenty hN) hq

theorem sourceP_zero_real_simple {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ (Real.log (N : ℝ))^3)
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1-1/(42*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ (Real.log (N : ℝ))^3/(q : ℝ))
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    chi ≠ 1 ∧ chi^2=1 ∧ rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 :=
  zero_real_quadratic_simple (log_sourceP_ge_twenty hN) hq chi
    ((region_sourceP_iff N q rho).mpr ⟨hr, ht⟩) hpole hz

theorem sourceP_fixed_family {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ (Real.log (N : ℝ))^3)
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1-1/(42*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ (Real.log (N : ℝ))^3/(q : ℝ))
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ (Real.log (N : ℝ))^3 ∧
      d.modulus=chi.conductor ∧ inducedAt d q=chi ∧ datumL d rho=0 ∧
      rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ (Real.log (N : ℝ))^3 →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1-1/(42*Real.log (Real.log (N : ℝ))) < tau.re →
            |tau.im| ≤ (Real.log (N : ℝ))^3/(r : ℝ) →
              (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau=0 →
                tau=rho ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧
                  inducedAt d r=psi ∧ analyticOrderNatAt psi.LFunction tau=1 := by
  obtain ⟨d, hd, hc, hi, hdz, hir, hm, hall⟩ := family_fixed_source
    (log_sourceP_ge_twenty hN) hq chi ((region_sourceP_iff N q rho).mpr ⟨hr, ht⟩) hpole hz
  exact ⟨d, hd, hc, hi, hdz, hir, hm, fun r _ hq psi tau hr ht =>
    hall r hq psi tau ((region_sourceP_iff N r tau).mpr ⟨hr, ht⟩)⟩

theorem sourceP_unique_datum {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1-1/(42*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ (Real.log (N : ℝ))^3/(q : ℝ))
    (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    ∃! d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ sourceP N ∧ datumL d rho=0 :=
  unique_datum_of_actual_zero (log_sourceP_ge_twenty hN) hq chi
    ((region_sourceP_iff N q rho).mpr ⟨hr, ht⟩) hpole hz

theorem sourceP_principal_no_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {rho : ℂ}
    (hr : 1-1/(42*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ (Real.log (N : ℝ))^3/(q : ℝ)) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction rho ≠ 0 := by
  have hw := (region_sourceP_iff N q rho).mpr ⟨hr, ht⟩
  exact principal_no_zero_fourteen (by linarith [log_sourceP_ge_twenty hN]) hw.1 hw.2 hpole

theorem sourceP_modulus_one_no_zero {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) {rho : ℂ}
    (hr : 1-1/(42*Real.log (Real.log (N : ℝ))) < rho.re)
    (ht : |rho.im| ≤ (Real.log (N : ℝ))^3) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ 1).LFunction rho ≠ 0 :=
  sourceP_principal_no_zero hN hr (by simpa using ht) hpole

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale
