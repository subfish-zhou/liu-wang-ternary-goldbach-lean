import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1Reduction

/-! Ordinary analytic multiplicity transported between two actual nonprincipal inducing levels. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem t1_LFunction_eq_of_coefficients {d e : ℕ} [NeZero d] [NeZero e]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (hc : chi ≠ 1) (hp : psi ≠ 1)
    (hcoeff : ∀ n : ℕ, chi n = psi n) : chi.LFunction = psi.LFunction := by
  have hca : AnalyticOnNhd ℂ chi.LFunction (Set.univ : Set ℂ) :=
    (chi.differentiable_LFunction hc).differentiableOn.analyticOnNhd isOpen_univ
  have hpa : AnalyticOnNhd ℂ psi.LFunction (Set.univ : Set ℂ) :=
    (psi.differentiable_LFunction hp).differentiableOn.analyticOnNhd isOpen_univ
  have hhalf : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  have he : chi.LFunction =ᶠ[nhds (2 : ℂ)] psi.LFunction := by
    filter_upwards [hhalf] with z hz
    rw [chi.LFunction_eq_LSeries hz, psi.LFunction_eq_LSeries hz]
    congr 1
    exact funext hcoeff
  exact AnalyticOnNhd.eq_of_eventuallyEq hca hpa he

theorem t1_primitive_LFunction_eq_of_lift {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    [NeZero chi.conductor] [NeZero psi.conductor]
    (hc : chi ≠ 1) (hp : psi ≠ 1) (hd : d ∣ q) (he : e ∣ q)
    (hlift : chi.changeLevel hd = psi.changeLevel he) :
    chi.primitiveCharacter.LFunction = psi.primitiveCharacter.LFunction := by
  apply t1_LFunction_eq_of_coefficients _ _
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one psi hp)
  intro n
  have h1 := DirichletCharacter.primitiveCharacter_changeLevel_apply hd chi (n : ℤ)
  have h2 := DirichletCharacter.primitiveCharacter_changeLevel_apply he psi (n : ℤ)
  rw [hlift] at h1
  simpa only [Int.cast_natCast] using h1.symm.trans h2

theorem t1_order_eq_of_lift {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hc : chi ≠ 1) (hp : psi ≠ 1) (hd : d ∣ q) (he : e ∣ q)
    (hlift : chi.changeLevel hd = psi.changeLevel he)
    {rho : ℂ} (hr : 0 < rho.re) :
    analyticOrderNatAt chi.LFunction rho = analyticOrderNatAt psi.LFunction rho := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let : NeZero psi.conductor := ⟨psi.conductor_ne_zero⟩
  rw [analyticOrderNatAt_LFunction_eq_primitive chi hc hr,
    analyticOrderNatAt_LFunction_eq_primitive psi hp hr,
    t1_primitive_LFunction_eq_of_lift chi psi hc hp hd he hlift]

theorem t1_lifted_slot_selected {d q : ℕ} [NeZero d] [NeZero q]
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1) (hd : d ∣ q)
    {alpha y sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p : ZeroSlots q alpha y) (hp : chi.changeLevel hd = p.character) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t +
      reflectedKernel sigma t p.value ≤
      stechkinConductorCoeff * (Real.log d + Real.log (max 1 |t|) - Real.log Real.pi) +
        4 / 15 + 941 / 1600 := by
  have hpc : p.character ≠ 1 := by
    intro he
    apply hc
    apply DirichletCharacter.changeLevel_injective hd
    rw [map_one, hp, he]
  have hlift : chi.changeLevel hd = p.character.changeLevel (dvd_refl q) := by simpa using hp
  have hz := mem_strictZeroValues.mp p.zero_mem
  have he := t1_order_eq_of_lift chi p.character hc hpc hd (dvd_refl q) hlift hz.2.1
  have hm : (1 : ℝ) ≤ analyticOrderNatAt chi.LFunction p.value := by
    rw [he]
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) p.index_lt)
  have hk : 0 ≤ reflectedKernel sigma t p.value :=
    dampedZeroKernel_pair_nonneg hs t ⟨hz.2.1.le, hz.2.2.2.1.le⟩
  have hh := nonprincipal_ordinary_selected_bound chi hc hs hs1 t {p.value}
    (fun z hz' => by simpa only [Finset.mem_singleton.mp hz'] using ha.trans_lt hz.2.2.1)
  simp only [Finset.sum_singleton] at hh
  have hbad := general_badPrimeCost chi hs hs1
  nlinarith only [hh, hbad, hm, hk]

theorem t1_triple_principal_selected {d e f q : ℕ}
    [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) (hd : d ∣ q) (he : e ∣ q) (hf : f ∣ q)
    {alpha y sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p : ZeroSlots q alpha y) (hp : eta.changeLevel hf = p.character) (hn : p.character ≠ 1)
    (htriple : chi.changeLevel hd * psi.changeLevel he * eta.changeLevel hf = 1) (t : ℝ) :
    dampedLogDeriv (t1Product chi psi) sigma (stechkinSigma sigma) stechkinK t +
      reflectedKernel sigma t (conj p.value) ≤
      stechkinConductorCoeff *
        (Real.log (Nat.lcm d e) + Real.log (max 1 |t|) - Real.log Real.pi) + 4 / 15 + 941 / 1600 := by
  have hpair : (t1Product chi psi).changeLevel (Nat.lcm_dvd hd he) = p.character⁻¹ := by
    rw [t1Product_changeLevel chi psi hd he, ← hp]
    exact mul_eq_one_iff_eq_inv.mp htriple
  have hpc : t1Product chi psi ≠ 1 := by
    intro hh
    rw [hh, map_one] at hpair
    exact (inv_ne_one.mpr hn) hpair.symm
  have hp' : (t1Product chi psi).changeLevel (Nat.lcm_dvd hd he) = (conjugateSlot p).character := by
    rw [conjugateSlot_character]
    exact hpair
  have hh := t1_lifted_slot_selected (t1Product chi psi) hpc (Nat.lcm_dvd hd he)
    hs hs1 ha (conjugateSlot p) hp' t
  simpa only [conjugateSlot_value] using hh

end LiuWang.Proof.MultiZeroRepulsion.Continuation
