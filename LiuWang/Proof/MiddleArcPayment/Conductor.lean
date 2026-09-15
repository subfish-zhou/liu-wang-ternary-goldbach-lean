import LiuWang.Proof.ArcGeometry.Main
import LiuWang.Proof.CompleteExpansion.Consumer
import LiuWang.Proof.DirichletZeroCount.Consumer

/-!
# Fixed-modulus conductor packets for the literal middle arc

The primitive transport is only in the open critical strip. Euler-factor
zeros are not inserted there, and the finite bad-prime error remains in the
complete expansion. No exceptional zero or analytic multiplicity is removed.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.CompleteExpansion

namespace LiuWang.Proof.MiddleArcPayment

theorem zeroValues_eq_countValues {q : ℕ} [NeZero q] (chi : Character q) (T : ℝ) :
    CompleteExpansion.zeroValues chi T =
      DirichletZeroCount.zeroValues chi (1 / 2) T := by
  ext rho
  rw [CompleteExpansion.mem_zeroValues, DirichletZeroCount.mem_zeroValues]
  tauto

theorem zeroValueSum_eq_primitive {q : ℕ} [NeZero q] (chi : Character q)
    [NeZero chi.conductor] (hc : chi ≠ 1) (N : ℕ) (T eta : ℝ) :
    zeroValueSum chi N T eta = zeroValueSum chi.primitiveCharacter N T eta := by
  unfold zeroValueSum
  rw [zeroValues_eq_countValues, zeroValues_eq_countValues,
    DirichletZeroCount.zeroValues_eq_primitive chi hc]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [BombieriVinogradov.SiegelWalfisz.analyticOrderNatAt_LFunction_eq_primitive
    chi hc (DirichletZeroCount.mem_zeroValues.mp hrho).2.1.1]

theorem zeroValueSum_principal_eq_zeta (q : ℕ) [NeZero q] (N : ℕ) (T eta : ℝ) :
    zeroValueSum (1 : Character q) N T eta =
      zeroValueSum (1 : Character 1) N T eta := by
  unfold zeroValueSum
  rw [zeroValues_eq_countValues, zeroValues_eq_countValues,
    DirichletZeroCount.zeroValues_principal_eq_zeta]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hr := (DirichletZeroCount.mem_zeroValues.mp hrho).2.1
  have h1 : rho ≠ 1 := by intro h; simp [h] at hr
  rw [PrincipalPsi.analyticOrderNatAt_principal_eq_zeta hr.1 h1,
    DirichletCharacter.LFunction_modOne_eq]

def primitiveSourceSum {q : ℕ} [NeZero q] (chi : Character q)
    (N : ℕ) (T eta : ℝ) : ℂ :=
  if chi = 1 then zeroValueSum (1 : Character 1) N T eta
  else
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    zeroValueSum chi.primitiveCharacter N T eta

theorem zeroValueSum_eq_primitiveSource {q : ℕ} [NeZero q] (chi : Character q)
    (N : ℕ) (T eta : ℝ) :
    zeroValueSum chi N T eta = primitiveSourceSum chi N T eta := by
  unfold primitiveSourceSum
  split_ifs with hc
  · subst chi
    exact zeroValueSum_principal_eq_zeta q N T eta
  · let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    exact zeroValueSum_eq_primitive chi hc N T eta

def conductorCharacters (q d : ℕ) [NeZero q] : Finset (Character q) :=
  Finset.univ.filter (fun chi => chi.conductor = d)

theorem sum_conductorCharacters {q : ℕ} [NeZero q] {A : Type*} [AddCommMonoid A]
    (f : Character q → A) :
    (∑ d ∈ q.divisors, ∑ chi ∈ conductorCharacters q d, f chi) =
      ∑ chi : Character q, f chi := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun (chi : Character q) (_ : chi ∈ Finset.univ) =>
      Nat.mem_divisors.mpr ⟨chi.conductor_dvd_level, NeZero.ne q⟩) f

def conductorPacket (q d N a : ℕ) [NeZero q] (eta : ℝ) : ℂ :=
  ∑ chi ∈ conductorCharacters q d, G a chi * primitiveSourceSum chi N (sourceT N) eta

theorem zeroPacket_eq_conductors {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ)
    (haq : Nat.Coprime a q) :
    zeroPacket q N a eta =
      (q.totient : ℂ)⁻¹ * ∑ d ∈ q.divisors, conductorPacket q d N a eta := by
  rw [zeroPacket_eq_all_values N a eta haq]
  simp_rw [zeroValueSum_eq_primitiveSource]
  rw [← sum_conductorCharacters]
  rfl

theorem complete_conductor_error {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
      (q.totient : ℂ)⁻¹ * ∑ d ∈ q.divisors, conductorPacket q d N a eta‖ ≤
        errorBound q N a eta := by
  rw [← zeroPacket_eq_conductors N a eta hi.2.2]
  exact complete_error_function hN hi hq eta

theorem M3_fixed_witness {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (ha : alpha ∈ M3 N) :
    ∃ (q a : ℕ) (eta : ℝ) (hq : 0 < q),
      letI : NeZero q := ⟨hq.ne'⟩
      sourceL N ^ 3 < (q : ℝ) ∧
      (q : ℝ) ≤ sourceL N ^ 6 ∧ sourceIndex a q ∧
      alpha = rationalCenter a q + eta ∧
      |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N) ∧
      ‖S N alpha - principalCoefficient q * J N eta +
        (q.totient : ℂ)⁻¹ * ∑ d ∈ q.divisors, conductorPacket q d N a eta‖ ≤
          errorBound q N a eta := by
  obtain ⟨q, a, eta, hq0, hq1, hi, he, heta⟩ := ArcGeometry.M3_eta_range ha
  let : NeZero q := ⟨(ArcGeometry.sourceIndex_den_pos hi).ne'⟩
  refine ⟨q, a, eta, ArcGeometry.sourceIndex_den_pos hi, hq0, hq1, hi, he, ?_, ?_⟩
  · rwa [← approximationRadius_eq hN (ArcGeometry.sourceIndex_den_pos hi)]
  · rw [he]
    exact complete_conductor_error hN hi hq1 eta

end LiuWang.Proof.MiddleArcPayment
