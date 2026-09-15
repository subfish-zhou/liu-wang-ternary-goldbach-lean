import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal.Permutations

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts

theorem product_changeLevel {d e q : ℕ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hd : d ∣ q) (he : e ∣ q) :
    (lwdProduct chi psi).changeLevel (Nat.lcm_dvd hd he) =
      chi.changeLevel hd * psi.changeLevel he := by
  rw [product_eq_lifted, map_mul, ← DirichletCharacter.changeLevel_trans,
    ← DirichletCharacter.changeLevel_trans]

theorem product_principal_iff {d e q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hd : d ∣ q) (he : e ∣ q) :
    lwdProduct chi psi = 1 ↔ chi.changeLevel hd * psi.changeLevel he = 1 := by
  rw [← product_changeLevel chi psi hd he, DirichletCharacter.changeLevel_eq_one_iff]

theorem triple_principal_iff {d e f q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) (hd : d ∣ q) (he : e ∣ q) (hf : f ∣ q) :
    lwdProduct (lwdProduct chi psi) eta = 1 ↔
      chi.changeLevel hd * psi.changeLevel he * eta.changeLevel hf = 1 := by
  rw [product_principal_iff _ _ (Nat.lcm_dvd hd he) hf,
    product_changeLevel chi psi hd he]

theorem product_principal_comm {d e : ℕ} [NeZero d] [NeZero e]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) :
    lwdProduct chi psi = 1 ↔ lwdProduct psi chi = 1 := by
  rw [product_principal_iff chi psi (Nat.dvd_mul_right d e) (Nat.dvd_mul_left e d),
    product_principal_iff psi chi (Nat.dvd_mul_left e d) (Nat.dvd_mul_right d e)]
  rw [mul_comm (chi.changeLevel (Nat.dvd_mul_right d e))
    (psi.changeLevel (Nat.dvd_mul_left e d))]

theorem triple_principal_no_pair {d e f q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) (hd : d ∣ q) (he : e ∣ q) (hf : f ∣ q)
    (hc : chi ≠ 1) (hp : psi ≠ 1) (ht : eta ≠ 1)
    (hm : lwdProduct (lwdProduct chi psi) eta = 1) :
    lwdProduct chi psi ≠ 1 ∧ lwdProduct chi eta ≠ 1 ∧ lwdProduct psi eta ≠ 1 := by
  have hm' := (triple_principal_iff chi psi eta hd he hf).mp hm
  have hc' : chi.changeLevel hd ≠ 1 := fun h => hc ((DirichletCharacter.changeLevel_eq_one_iff _).mp h)
  have hp' : psi.changeLevel he ≠ 1 := fun h => hp ((DirichletCharacter.changeLevel_eq_one_iff _).mp h)
  have ht' : eta.changeLevel hf ≠ 1 := fun h => ht ((DirichletCharacter.changeLevel_eq_one_iff _).mp h)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [(product_principal_iff chi psi hd he).mp h, one_mul] at hm'
    exact ht' hm'
  · intro h
    rw [mul_right_comm, (product_principal_iff chi eta hd hf).mp h, one_mul] at hm'
    exact hp' hm'
  · intro h
    rw [mul_assoc, (product_principal_iff psi eta he hf).mp h, mul_one] at hm'
    exact hc' hm'

theorem primitive_lift_values {d : ℕ} [NeZero d]
    (chi : DirichletCharacter ℂ d) (hp : chi.IsPrimitive) (n : ℕ) :
    chi.primitiveCharacter n = chi n := by
  suffices chi.primitiveCharacter (n : ℤ) = chi (n : ℤ) by
    simpa only [Int.cast_natCast] using this
  by_cases hc : IsCoprime (n : ℤ) (d : ℤ)
  · exact chi.primitiveCharacter_apply_of_isCoprime hc
  · have hp' : chi.conductor = d := hp
    rw [(DirichletCharacter.apply_eq_zero_iff ..).mpr hc,
      (DirichletCharacter.apply_eq_zero_iff ..).mpr (by simpa only [hp'] using hc)]

theorem common_lift_primitive_values {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hd : d ∣ q) (he : e ∣ q) (h : chi.changeLevel hd = psi.changeLevel he) (n : ℕ) :
    chi.primitiveCharacter n = psi.primitiveCharacter n := by
  have hh := congrArg (fun c : DirichletCharacter ℂ q => c.primitiveCharacter (n : ℤ)) h
  have h1 := DirichletCharacter.primitiveCharacter_changeLevel_apply hd chi (n : ℤ)
  have h2 := DirichletCharacter.primitiveCharacter_changeLevel_apply he psi (n : ℤ)
  simpa only [Int.cast_natCast] using h1.symm.trans (hh.trans h2)

theorem triple_pair_primitive_values {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) (hd : d ∣ q) (he : e ∣ q) (hf : f ∣ q)
    (hp : eta.IsPrimitive) (hm : lwdProduct (lwdProduct chi psi) eta = 1) (n : ℕ) :
    (lwdProduct chi psi).primitiveCharacter n = eta⁻¹ n := by
  have h := (mul_eq_one_iff_eq_inv).mp ((triple_principal_iff chi psi eta hd he hf).mp hm)
  rw [← product_changeLevel chi psi hd he, ← map_inv] at h
  exact (common_lift_primitive_values _ _ (Nat.lcm_dvd hd he) hf h n).trans
    (primitive_lift_values eta⁻¹ (BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hp) n)

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts
