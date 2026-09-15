import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.ZeroTransport

/-! The explicitly supplied primitive chi1 (mod q1) in LWD (2.8), not a modulus substitution. -/

set_option autoImplicit false
noncomputable section

open Complex

namespace LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1

theorem parityShift_primitive {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    parityShift chi.primitiveCharacter = parityShift chi := by
  have he := chi.primitiveCharacter_apply_of_isCoprime (a := -1) ⟨-1, 0, by ring⟩
  simp only [Int.cast_neg, Int.cast_one] at he
  unfold parityShift
  rw [he]

theorem parityShift_changeLevel {q1 q : ℕ} (chi1 : DirichletCharacter ℂ q1) (hd : q1 ∣ q) :
    parityShift (chi1.changeLevel hd) = parityShift chi1 := by
  have he := DirichletCharacter.changeLevel_eq_cast_of_dvd' chi1 hd
    (a := -1) ⟨-1, 0, by ring⟩
  simp only [Int.cast_neg, Int.cast_one] at he
  unfold parityShift
  rw [he]

theorem induced_conductor {q1 q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (chi1 : DirichletCharacter ℂ q1)
    (hp : chi1.IsPrimitive) (hd : q1 ∣ q) (he : chi1.changeLevel hd = chi) :
    chi.conductor = q1 := by
  rw [← he, DirichletCharacter.conductor_changeLevel]
  exact hp

theorem l25_induced_of_gamma_estimate {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi : DirichletCharacter ℂ q) (chi1 : DirichletCharacter ℂ q1)
    (hc : chi ≠ 1) (hp : chi1.IsPrimitive) (hd : q1 ∣ q)
    (he : chi1.changeLevel hd = chi) {sigma : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (t : ℝ)
    (hgamma : gammaTerm (parityShift chi1) sigma t ≤
      kappa * Real.log (max 1 |t|) + 0.3918) :
    f chi sigma t ≤ kappa * Real.log ((q1 : ℝ) * max 1 |t|) -
      kappa * Real.log Real.pi + 0.3918 - zeroSum chi sigma t + badS q1 q sigma := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpar : parityShift chi.primitiveCharacter = parityShift chi1 := by
    rw [parityShift_primitive, ← he, parityShift_changeLevel]
  have hh := l25_imprimitive_of_gamma_estimate chi hc hs t (by simpa only [hpar] using hgamma)
  rwa [induced_conductor chi chi1 hp hd he] at hh

end LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
