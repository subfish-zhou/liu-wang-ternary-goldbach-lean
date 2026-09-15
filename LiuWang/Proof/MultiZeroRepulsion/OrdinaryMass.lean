import LiuWang.Proof.MultiZeroRepulsion.SelectedMass
import LiuWang.Proof.PrincipalPsi.Quantitative.XiBridge

/-! Actual ordinary-L analytic multiplicities, including imprimitive and principal characters. -/

set_option autoImplicit false
noncomputable section
open Complex Complex.Hadamard
open scoped Classical ComplexConjugate
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion

def valueFibers (f : ℂ → ℂ) (v : Finset ℂ) : Finset (divisorZeroIndex₀ f Set.univ) :=
  v.biUnion (divisorZeroIndex₀_fiberFinset f)

theorem mem_valueFibers {f : ℂ → ℂ} {v : Finset ℂ} {p : divisorZeroIndex₀ f Set.univ} :
    p ∈ valueFibers f v ↔ divisorZeroIndex₀_val p ∈ v := by
  simp [valueFibers]

theorem sum_valueFibers {f : ℂ → ℂ} (hf : Differentiable ℂ f) (v : Finset ℂ)
    (h0 : ∀ z ∈ v, z ≠ 0) (w : ℂ → ℝ) :
    (∑ p ∈ valueFibers f v, w (divisorZeroIndex₀_val p)) =
      ∑ z ∈ v, (analyticOrderNatAt f z : ℝ) * w z := by
  unfold valueFibers
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro z hz
    calc
      _ = ∑ _p ∈ divisorZeroIndex₀_fiberFinset f z, w z := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(mem_divisorZeroIndex₀_fiberFinset f z p).mp hp]
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul,
          divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt hf (h0 z hz)]
  · intro z _ r _ hzr
    change Disjoint (divisorZeroIndex₀_fiberFinset f z) (divisorZeroIndex₀_fiberFinset f r)
    rw [Finset.disjoint_left]
    intro p hp hpr
    exact hzr (((mem_divisorZeroIndex₀_fiberFinset f z p).mp hp).symm.trans
      ((mem_divisorZeroIndex₀_fiberFinset f r p).mp hpr))

def reflectedKernel (sigma t : ℝ) (rho : ℂ) : ℝ :=
  dampedZeroKernel sigma t rho + dampedZeroKernel sigma t (1 - conj rho)

theorem primitive_ordinary_mass_le {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {sigma : ℝ} (hs : 1 < sigma)
    (t : ℝ) (v : Finset ℂ) (hr : ∀ rho ∈ v, 1 / 2 < rho.re) :
    (∑ rho ∈ v, (analyticOrderNatAt chi.LFunction rho : ℝ) * reflectedKernel sigma t rho) ≤
      primitiveZeroSum chi sigma t := by
  have hh := primitive_selected_mass_le hc hp hs t
    (valueFibers (symmetricCompletedLFunction chi) v)
    (fun p hp => hr _ (mem_valueFibers.mp hp))
  change (∑ p ∈ valueFibers (symmetricCompletedLFunction chi) v,
    reflectedKernel sigma t (divisorZeroIndex₀_val p)) ≤ _ at hh
  rw [sum_valueFibers (differentiable_symmetricCompletedLFunction hc) v
    (fun z hz he => by have := hr z hz; norm_num [he] at this) (reflectedKernel sigma t)] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro rho hrv
  rw [analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction hc (by linarith [hr rho hrv])]

theorem nonprincipal_ordinary_selected_bound {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t : ℝ)
    (v : Finset ℂ) (hr : ∀ rho ∈ v, 1 / 2 < rho.re) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t +
      (∑ rho ∈ v, (analyticOrderNatAt chi.LFunction rho : ℝ) * reflectedKernel sigma t rho) ≤
      stechkinConductorCoeff *
        (Real.log chi.conductor + Real.log (max 1 |t|) - Real.log Real.pi) +
          4 / 15 + badPrimeCost chi sigma := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hh := primitive_ordinary_mass_le
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
    chi.primitiveCharacter_isPrimitive hs t v hr
  have hm : (∑ rho ∈ v,
      (analyticOrderNatAt chi.LFunction rho : ℝ) * reflectedKernel sigma t rho) =
      ∑ rho ∈ v, (analyticOrderNatAt chi.primitiveCharacter.LFunction rho : ℝ) *
        reflectedKernel sigma t rho := by
    apply Finset.sum_congr rfl
    intro rho hrv
    rw [analyticOrderNatAt_LFunction_eq_primitive chi hc (by linarith [hr rho hrv])]
  rw [hm]
  linarith [imprimitive_full_zero_sum_bound chi hc hs hs1 t]

theorem principal_ordinary_mass_le (q : ℕ) [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (t : ℝ) (v : Finset ℂ)
    (hr : ∀ rho ∈ v, 1 / 2 < rho.re ∧ rho.re < 1) :
    (∑ rho ∈ v, (analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction rho : ℝ) *
      reflectedKernel sigma t rho) ≤ zetaZeroSum sigma t := by
  have hh := xi_selected_mass_le hs t (valueFibers riemannXi v)
    (fun p hp => (hr _ (mem_valueFibers.mp hp)).1)
  change (∑ p ∈ valueFibers riemannXi v,
    reflectedKernel sigma t (divisorZeroIndex₀_val p)) ≤ _ at hh
  rw [sum_valueFibers differentiable_riemannXi v
    (fun z hz he => by have := (hr z hz).1; norm_num [he] at this) (reflectedKernel sigma t)] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro rho hrv
  rw [PrincipalPsi.Quantitative.analyticOrderNatAt_xi_eq_principal
    (q := q) (by linarith [(hr rho hrv).1]) (by
      intro he; have := (hr rho hrv).2; simp [he] at this)]

theorem principal_ordinary_selected_bound (q : ℕ) [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t : ℝ) (v : Finset ℂ)
    (hr : ∀ rho ∈ v, 1 / 2 < rho.re ∧ rho.re < 1) :
    dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma (stechkinSigma sigma) stechkinK t +
      (∑ rho ∈ v, (analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction rho : ℝ) *
        reflectedKernel sigma t rho) ≤
      poleDifference sigma t + stechkinConductorCoeff * (Real.log (max 1 |t|) - Real.log Real.pi) +
        23 / 40 - 11 * stechkinK / 30 + principalPrimeCost q sigma := by
  linarith [principal_ordinary_mass_le q hs t v hr,
    principal_full_zero_sum_bound (q := q) hs hs1 t]

end LiuWang.Proof.MultiZeroRepulsion
