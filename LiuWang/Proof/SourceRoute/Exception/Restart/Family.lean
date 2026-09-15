import LiuWang.Proof.SourceRoute.Exception.Restart.PrincipalSource

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.SourceRoute.Exception.Restart

theorem induced_source_zero (d : PrimitiveQuadraticDatum) {q : ℕ} [NeZero q]
    (hd : d.modulus ∣ q) {rho : ℂ} (hz : datumL d rho = 0) :
    (inducedAt d q).LFunction rho = 0 := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  rw [inducedAt, dif_pos hd,
    DirichletCharacter.LFunction_changeLevel hd d.character (Or.inl d.ne_one)]
  change datumL d rho * _ = 0
  rw [hz, zero_mul]

theorem primitive_induction_trans (d : PrimitiveQuadraticDatum)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hd : d.modulus ∣ chi.conductor)
    (he : inducedAt d chi.conductor = chi.primitiveCharacter) :
    inducedAt d q = chi := by
  have hh := congrArg (DirichletCharacter.changeLevel chi.conductor_dvd_level) he
  rw [inducedAt, dif_pos hd, ← DirichletCharacter.changeLevel_trans,
    chi.changeLevel_primitiveCharacter] at hh
  simpa only [inducedAt, dif_pos (hd.trans chi.conductor_dvd_level)] using hh

theorem fixed_source_nonprincipal_induced (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hzb : datumL d (beta : ℂ) = 0) {q : ℕ} [NeZero q]
    (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re)
    (ht : |rho.im| ≤ x / q) (hz : chi.LFunction rho = 0) : chi = inducedAt d q := by
  by_contra hne
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
  have hrd : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hheight : |rho.im| ≤ x / chi.conductor :=
    ht.trans (div_le_div_of_nonneg_left (by linarith)
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero chi.conductor_ne_zero)) hrd)
  have hp := primitive_pair_nonprincipal_of_not_induced d chi hne
  have hm : pairCharacter d.character chi.primitiveCharacter⁻¹ ≠ 1 := by
    intro hh
    obtain ⟨hd, he⟩ := pair_principal_forces_induction d chi.primitiveCharacter⁻¹ hh
    have hi := congrArg (fun c : DirichletCharacter ℂ chi.conductor => c⁻¹) he
    rw [induced_inverse, inv_inv] at hi
    exact hne (primitive_induction_trans d chi hd hi).symm
  exact mixed_sources_exclusion d hx hdx (hrd.trans hq) chi.primitiveCharacter
    hpr chi.primitiveCharacter_isPrimitive hp hm hb hzb hr hheight
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc
      (by linarith [original_re_half hx hr]) hz)

theorem original_gap_at_conductor {x b : ℝ} {r : ℕ}
    (hx : 10 ≤ x) (hr : 3 ≤ r) (hrx : (r : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ b) :
    1 - b < 1 / (3 * Real.log r) := by
  have hlog := log_level_gt_one hr
  have hlx := log_scale_ge hx
  have hl := Real.log_le_log (by exact_mod_cast (show 0 < r by omega)) hrx
  have hw : 1 / (9.645908801 * Real.log x) < 1 / (3 * Real.log r) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

theorem fixed_source_characterization (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hzb : datumL d (beta : ℂ) = 0) {q : ℕ} [NeZero q]
    (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re)
    (ht : |rho.im| ≤ x / q) (hpole : chi ≠ 1 ∨ rho ≠ 1)
    (hz : chi.LFunction rho = 0) :
    chi ≠ 1 ∧ d.modulus = chi.conductor ∧ d.modulus ∣ q ∧
      chi = inducedAt d q ∧ rho = (beta : ℂ) ∧ analyticOrderNatAt chi.LFunction rho = 1 := by
  have hrpos : 0 < rho.re := by linarith [original_re_half hx hr]
  have hbpos : 0 < beta := by linarith [original_re_half hx hb]
  have hc : chi ≠ 1 := by
    intro he
    subst chi
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
    exact fixed_source_zeta_exclusion d hx hdx hb hzb hr
      (ht.trans (div_le_self (by linarith) hq1))
      ((PrincipalPsi.principal_zero_iff_zeta_zero hrpos
        (hpole.resolve_left (by simp))).mp hz)
  have he := fixed_source_nonprincipal_induced d hx hdx hb hzb hq chi hc hr ht hz
  have hdq : d.modulus ∣ q := by
    by_contra hd
    rw [inducedAt, dif_neg hd] at he
    exact hc he
  have hcs : chi ^ 2 = 1 := by
    rw [he, inducedAt, dif_pos hdq, ← map_pow, d.square_eq_one, map_one]
  have hbeta : chi.LFunction (beta : ℂ) = 0 := by
    rw [he]
    exact induced_source_zero d hdq hzb
  have hrd : (chi.conductor : ℝ) ≤ x :=
    (show (chi.conductor : ℝ) ≤ q by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi).trans hq
  have hsource : primitiveSource chi hc hcs = d :=
    real_sources_unique_original _ d hx hrd hdx hb hb
      (primitiveSource_zero chi hc hcs (by simpa using hbpos) hbeta) hzb
  have hmod : d.modulus = chi.conductor :=
    (congrArg PrimitiveQuadraticDatum.modulus hsource).symm
  have hdz := primitiveSource_zero chi hc hcs hrpos hz
  rw [hsource] at hdz
  have hheight : |rho.im| ≤ x / d.modulus :=
    ht.trans (div_le_div_of_nonneg_left (by linarith)
      (Nat.cast_pos.mpr d.modulus_pos) (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) hdq))
  have hi : rho.im = 0 := by
    by_contra hh
    exact fixed_source_nonreal_exclusion d hx hdx hb hzb hr hheight hh hdz
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have hdr := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one d.character d.ne_one
  have hgr := original_gap_at_conductor hx hdr hdx hr
  have hgb := original_gap_at_conductor hx hdr hdx hb
  have hzsame := primitive_real_zeros_unique d.ne_one d.isPrimitive hrpos
    (by simpa using hbpos) hdz hzb hi (by simp) hgr (by simpa using hgb)
  refine ⟨hc, hmod, hdq, he, hzsame, real_zero_simple hc hrpos hz hi ?_⟩
  simpa only [← hmod] using hgr

theorem fixed_source_zero_iff (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hzb : datumL d (beta : ℂ) = 0) {q : ℕ} [NeZero q]
    (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re)
    (ht : |rho.im| ≤ x / q) (hpole : chi ≠ 1 ∨ rho ≠ 1) :
    chi.LFunction rho = 0 ↔
      d.modulus ∣ q ∧ chi = inducedAt d q ∧ rho = (beta : ℂ) := by
  constructor
  · intro hz
    obtain ⟨_, _, hd, he, hz, _⟩ :=
      fixed_source_characterization d hx hdx hb hzb hq chi hr ht hpole hz
    exact ⟨hd, he, hz⟩
  · rintro ⟨hd, rfl, rfl⟩
    exact induced_source_zero d hd hzb

theorem fixed_source_noninducing_no_zero (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hzb : datumL d (beta : ℂ) = 0) {q : ℕ} [NeZero q]
    (hq : (q : ℝ) ≤ x) (hdq : ¬d.modulus ∣ q) (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re)
    (ht : |rho.im| ≤ x / q) (hpole : chi ≠ 1 ∨ rho ≠ 1) : chi.LFunction rho ≠ 0 :=
  fun hz => hdq ((fixed_source_zero_iff d hx hdx hb hzb hq chi hr ht hpole).mp hz).1

end LiuWang.Proof.SourceRoute.Exception.Restart
