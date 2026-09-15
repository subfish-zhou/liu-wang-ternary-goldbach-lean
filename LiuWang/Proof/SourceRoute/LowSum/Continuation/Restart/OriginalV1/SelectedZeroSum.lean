import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.OffHeight

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1

theorem lwd_2_16_primitive {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15) (t : ℝ)
    (v w : Finset ℂ) (hvw : Disjoint v w)
    (hv : ∀ rho ∈ v, 1 / 2 < rho.re ∧ rho.re < 1 ∧ rho.im = t)
    (hw : ∀ rho ∈ w, 1 / 2 < rho.re ∧ rho.re < 1 ∧ |t - rho.im| ≤ 1) :
    (∑ rho ∈ v, (analyticOrderNatAt chi.LFunction rho : ℝ) / (sigma - rho.re)) +
      (∑ rho ∈ w, (analyticOrderNatAt chi.LFunction rho : ℝ) *
        MultiZeroRepulsion.Continuation.realKernel (sigma - rho.re) (t - rho.im)) -
      (5 + Real.sqrt 5) / 10 * (∑ rho ∈ w, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      primitiveZeroSum chi sigma t := by
  apply (lwd_2_16_mass chi hs hs1 t v w hvw
    (fun rho h => ⟨(hv rho h).1.le, (hv rho h).2⟩)
    (fun rho h => ⟨(hw rho h).1.le, (hw rho h).2⟩)).trans
  apply primitive_ordinary_mass_le hc hp hs
  intro rho h
  rcases Finset.mem_union.mp h with h | h
  · exact (hv rho h).1
  · exact (hw rho h).1

theorem lwd_2_16_principal (q : ℕ) [NeZero q]
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15) (t : ℝ)
    (v w : Finset ℂ) (hvw : Disjoint v w)
    (hv : ∀ rho ∈ v, 1 / 2 < rho.re ∧ rho.re < 1 ∧ rho.im = t)
    (hw : ∀ rho ∈ w, 1 / 2 < rho.re ∧ rho.re < 1 ∧ |t - rho.im| ≤ 1) :
    (∑ rho ∈ v, (analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction rho : ℝ) /
      (sigma - rho.re)) +
      (∑ rho ∈ w, (analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction rho : ℝ) *
        MultiZeroRepulsion.Continuation.realKernel (sigma - rho.re) (t - rho.im)) -
      (5 + Real.sqrt 5) / 10 *
        (∑ rho ∈ w, (analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction rho : ℝ)) ≤
      zetaZeroSum sigma t := by
  apply (lwd_2_16_mass (1 : DirichletCharacter ℂ q) hs hs1 t v w hvw
    (fun rho h => ⟨(hv rho h).1.le, (hv rho h).2⟩)
    (fun rho h => ⟨(hw rho h).1.le, (hw rho h).2⟩)).trans
  apply principal_ordinary_mass_le q hs
  intro rho h
  rcases Finset.mem_union.mp h with h | h
  · exact ⟨(hv rho h).1, (hv rho h).2.1⟩
  · exact ⟨(hw rho h).1, (hw rho h).2.1⟩

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1
