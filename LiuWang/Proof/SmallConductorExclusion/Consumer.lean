import LiuWang.Proof.SmallConductorExclusion.SmallModuli
import LiuWang.Proof.ZeroRegionFamily.RealClosure.Consumer

/-!
# Excluding certified characters from actual exceptional sources

The finite-prefix criterion is consumed by the frozen R24 theorem for the
original ordinary L-function. The modulus is its actual primitive conductor.
All nonprincipal characters of conductor three and four are covered. No
assertion that every conductor below 987 satisfies the certificate is made.
-/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.SmallConductorExclusion

def CertifiedSmallSource (d : PrimitiveQuadraticDatum) : Prop :=
  letI : NeZero d.modulus := ⟨d.modulus_ne⟩
  d.modulus < 987 ∧ PeriodPrefixNonnegative d.character

theorem datumL_ne_zero_of_periodPrefix (d : PrimitiveQuadraticDatum)
    (hcert : letI : NeZero d.modulus := ⟨d.modulus_ne⟩
      PeriodPrefixNonnegative d.character)
    {sigma : ℝ} (hs : 0 < sigma) : datumL d (sigma : ℂ) ≠ 0 := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  exact LFunction_ne_zero_of_periodPrefix d.character d.ne_one hcert hs

theorem certified_source_original_region_ne_zero (d : PrimitiveQuadraticDatum)
    (hcert : CertifiedSmallSource d) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    datumL d (beta : ℂ) ≠ 0 := by
  have hlog := Sharp.log_scale_ge hx
  have hd : 0 < 9.645908801 * Real.log x := by nlinarith
  have hw : 1 / (9.645908801 * Real.log x) ≤ 1 / 2 :=
    (div_le_iff₀ hd).mpr (by nlinarith)
  exact datumL_ne_zero_of_periodPrefix d hcert.2 (by linarith)

theorem chiFour_isPrimitive : chiFour.IsPrimitive := by
  have hlow := BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one
    chiFour chiFour_ne_one
  have hhigh := BombieriVinogradov.DirichletCharacter.conductor_le_level chiFour
  have hd := chiFour.conductor_dvd_level
  change chiFour.conductor = 4
  have hc : chiFour.conductor = 3 ∨ chiFour.conductor = 4 := by omega
  rcases hc with hc | hc
  · norm_num [hc] at hd
  · exact hc

def datumFour : PrimitiveQuadraticDatum where
  modulus := 4
  modulus_ne := by decide
  character := chiFour
  isPrimitive := chiFour_isPrimitive
  square_eq_one := chiFour_square
  ne_one := chiFour_ne_one

theorem datumFour_certified : CertifiedSmallSource datumFour :=
  ⟨by decide, periodPrefix_four chiFour chiFour_ne_one⟩

theorem certifiedSmallSource_nonempty :
    ∃ d : PrimitiveQuadraticDatum, CertifiedSmallSource d ∧
      ∀ sigma : ℝ, 0 < sigma → datumL d (sigma : ℂ) ≠ 0 :=
  ⟨datumFour, datumFour_certified,
    fun _ hs => datumL_ne_zero_of_periodPrefix datumFour datumFour_certified.2 hs⟩

theorem datum_modulus_three_or_four_certified (d : PrimitiveQuadraticDatum)
    (hd : d.modulus = 3 ∨ d.modulus = 4) : CertifiedSmallSource d := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  refine ⟨by omega, ?_⟩
  rcases hd with hd | hd
  · have h : ∀ (q : ℕ) [NeZero q], q = 3 →
        ∀ chi : DirichletCharacter ℂ q, chi ≠ 1 → PeriodPrefixNonnegative chi := by
      intro q _ hq
      subst q
      exact periodPrefix_three
    exact h d.modulus hd d.character d.ne_one
  · have h : ∀ (q : ℕ) [NeZero q], q = 4 →
        ∀ chi : DirichletCharacter ℂ q, chi ≠ 1 → PeriodPrefixNonnegative chi := by
      intro q _ hq
      subst q
      exact periodPrefix_four
    exact h d.modulus hd d.character d.ne_one

theorem actual_source_not_certified {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : RealClosure.region x q rho) (hp : chi ≠ 1 ∨ rho ≠ 1)
    (hz : chi.LFunction rho = 0)
    (d : PrimitiveQuadraticDatum) (hdz : datumL d rho = 0) :
    ¬CertifiedSmallSource d := by
  intro hcert
  have hi := (RealClosure.zero_real_quadratic_simple hx hq chi hr hp hz).2.2.1
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  have hpos : 0 < rho.re := by linarith [RealClosure.region_re_half hx hr]
  exact datumL_ne_zero_of_periodPrefix d hcert.2 hpos (by simpa only [he] using hdz)

theorem actual_source_modulus_ge_five {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hr : RealClosure.region x q rho) (hp : chi ≠ 1 ∨ rho ≠ 1)
    (hz : chi.LFunction rho = 0)
    (d : PrimitiveQuadraticDatum) (hdz : datumL d rho = 0) : 5 ≤ d.modulus := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have hlow := BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one
    d.character d.ne_one
  rw [d.isPrimitive] at hlow
  by_contra h
  exact actual_source_not_certified hx hq chi hr hp hz d hdz
    (datum_modulus_three_or_four_certified d (by omega))

theorem family_twentyfour_excludes_certified_sources
    {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (rho : ℂ)
    (hr : 1 - 1 / (24 * Real.log x) < rho.re) (ht : |rho.im| ≤ x / (q : ℝ))
    (hp : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho = 0) :
    ∃ d : PrimitiveQuadraticDatum, 5 ≤ d.modulus ∧ (d.modulus : ℝ) ≤ x ∧
      d.modulus = chi.conductor ∧ inducedAt d q = chi ∧ datumL d rho = 0 ∧
      ¬CertifiedSmallSource d ∧ rho.im = 0 ∧
      analyticOrderNatAt chi.LFunction rho = 1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1 - 1 / (24 * Real.log x) < tau.re → |tau.im| ≤ x / (r : ℝ) →
          (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau = 0 →
            tau = rho ∧ d.modulus = psi.conductor ∧ d.modulus ∣ r ∧
              inducedAt d r = psi ∧ analyticOrderNatAt psi.LFunction tau = 1 := by
  obtain ⟨d, hd, hdc, hdi, hdz, hi, ho, hall⟩ :=
    RealClosure.family_twentyfour_from_actual_zero hx hq chi rho hr ht hp hz
  exact ⟨d, actual_source_modulus_ge_five hx hq chi ⟨hr, ht⟩ hp hz d hdz,
    hd, hdc, hdi, hdz, actual_source_not_certified hx hq chi ⟨hr, ht⟩ hp hz d hdz,
    hi, ho, hall⟩

theorem ordinary_LFunction_ne_zero_of_conductor_le_four
    {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (hc : chi.conductor ≤ 4) {rho : ℂ}
    (hr : 1 - 1 / (24 * Real.log x) < rho.re) (ht : |rho.im| ≤ x / (q : ℝ))
    (hp : chi ≠ 1 ∨ rho ≠ 1) : chi.LFunction rho ≠ 0 := by
  intro hz
  obtain ⟨d, hd, _, hdc, _⟩ :=
    family_twentyfour_excludes_certified_sources hx hq chi rho hr ht hp hz
  omega

end LiuWang.Proof.SmallConductorExclusion
