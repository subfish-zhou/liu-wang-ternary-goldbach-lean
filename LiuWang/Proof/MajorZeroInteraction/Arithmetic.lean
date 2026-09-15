import LiuWang.Proof.MajorArcApproximation.Consumer

/-! Arithmetic contraction is performed before any absolute-value estimate. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorArcApproximation

namespace LiuWang.Proof.MajorZeroInteraction

def phaseCoefficient {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : ℂ :=
  ∑ a ∈ numerators q,
    chi (a : ZMod q) * charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ))

theorem phaseCoefficient_eq_gauss {q : ℕ} [NeZero q]
    (N : ℕ) (chi : Character q) :
    phaseCoefficient N chi =
      gaussSum chi (ZMod.stdAddChar.mulShift (-(N : ZMod q))) := by
  have hf : (fun a : ℕ => chi (a : ZMod q) *
      ZMod.stdAddChar (-(a : ZMod q) * (N : ZMod q))) q =
      (fun a : ℕ => chi (a : ZMod q) *
        ZMod.stdAddChar (-(a : ZMod q) * (N : ZMod q))) 0 := by simp
  rw [phaseCoefficient, numerators, Finset.sum_filter]
  simp_rw [← stdAddChar_negative_phase]
  have he (a : ℕ) :
      (if Nat.Coprime a q then
        chi (a : ZMod q) * ZMod.stdAddChar (-(a : ZMod q) * (N : ZMod q))
       else 0) =
        chi (a : ZMod q) * ZMod.stdAddChar (-(a : ZMod q) * (N : ZMod q)) := by
    by_cases ha : Nat.Coprime a q
    · simp [ha]
    · have hu : ¬ IsUnit (a : ZMod q) := by
        simpa only [ZMod.isUnit_iff_coprime] using ha
      simp [ha, chi.map_nonunit hu]
  simp_rw [he]
  rw [sum_Icc_eq_sum_range_of_endpoint (NeZero.pos q) _ hf,
    ← SingularSeries.sum_zmod_eq_sum_range
      (fun a : ZMod q => chi a * ZMod.stdAddChar (-a * (N : ZMod q)))]
  unfold gaussSum
  apply Finset.sum_congr rfl
  intro a _
  simp only [AddChar.mulShift_apply]
  congr 2
  ring

theorem phaseCoefficient_principal {q : ℕ} [NeZero q] (N : ℕ) :
    phaseCoefficient N (1 : Character q) = ramanujan N q := by
  apply Finset.sum_congr rfl
  intro a ha
  have hu := (ZMod.isUnit_iff_coprime a q).mpr (mem_numerators.mp ha).2.2
  rw [MulChar.one_apply hu, one_mul]

theorem phaseCoefficient_vanishes {q : ℕ} [NeZero q] {N : ℕ}
    (hN : q ∣ N) {chi : Character q} (hc : chi ≠ 1) :
    phaseCoefficient N chi = 0 := by
  rw [phaseCoefficient_eq_gauss]
  have hn : (N : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff N q).mpr hN
  simpa [gaussSum, hn, AddChar.mulShift_apply] using MulChar.sum_eq_zero_of_ne_one hc

theorem norm_phaseCoefficient_le_totient {q : ℕ} [NeZero q]
    (N : ℕ) (chi : Character q) :
    ‖phaseCoefficient N chi‖ ≤ (q.totient : ℝ) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a ∈ numerators q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [norm_mul, SingularIntegral.charReal_norm, mul_one] using
        chi.norm_le_one (a : ZMod q)
    _ = _ := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, numerators,
        SingularSeries.reducedResidues] using
        congrArg (Nat.cast (R := ℝ)) (reducedResidues_card q)

theorem norm_phaseCoefficient_le_conductor {q : ℕ} [NeZero q] {N : ℕ}
    (hN : Nat.Coprime N q) (chi : Character q) :
    ‖phaseCoefficient N chi‖ ≤ Real.sqrt chi.conductor := by
  rw [phaseCoefficient_eq_gauss]
  have he := gaussSum_mulShift_eq chi ZMod.stdAddChar (-(ZMod.unitOfCoprime N hN))
  rw [show (-(N : ZMod q)) =
    ((-(ZMod.unitOfCoprime N hN) : (ZMod q)ˣ) : ZMod q) by simp, he, norm_mul]
  rw [(chi⁻¹ : Character q).unit_norm_eq_one, one_mul]
  exact norm_gaussSum_le_sqrt_conductor chi

def arithmeticWeight {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : ℝ :=
  if chi = 1 then ‖ramanujan N q‖
  else if q ∣ N then 0
  else if Nat.Coprime N q then min (q.totient : ℝ) (Real.sqrt chi.conductor)
  else (q.totient : ℝ)

theorem norm_phaseCoefficient_le_weight {q : ℕ} [NeZero q]
    (N : ℕ) (chi : Character q) :
    ‖phaseCoefficient N chi‖ ≤ arithmeticWeight N chi := by
  unfold arithmeticWeight
  split_ifs with hc hd hn
  · subst chi
    rw [phaseCoefficient_principal]
  · rw [phaseCoefficient_vanishes hd hc, norm_zero]
  · exact le_min (norm_phaseCoefficient_le_totient N chi)
      (norm_phaseCoefficient_le_conductor hn chi)
  · exact norm_phaseCoefficient_le_totient N chi

theorem arithmeticWeight_le_totient {q : ℕ} [NeZero q]
    (N : ℕ) (chi : Character q) :
    arithmeticWeight N chi ≤ (q.totient : ℝ) := by
  unfold arithmeticWeight
  split_ifs
  · exact norm_ramanujan_le_totient N q
  · positivity
  · exact min_le_left _ _
  · rfl

def characterConvolution {q : ℕ} [NeZero q]
    (f g : Character q → ℂ) (chi : Character q) : ℂ :=
  ∑ psi : Character q, f psi * g (psi⁻¹ * chi)

def characterEvaluation {q : ℕ} [NeZero q]
    (f : Character q → ℂ) (a : ℕ) : ℂ :=
  ∑ chi : Character q, chi (a : ZMod q) * f chi

theorem evaluate_convolution {q : ℕ} [NeZero q]
    (f g : Character q → ℂ) (a : ℕ) :
    characterEvaluation (characterConvolution f g) a =
      characterEvaluation f a * characterEvaluation g a := by
  unfold characterEvaluation characterConvolution
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro psi _
  symm
  apply Fintype.sum_equiv (Equiv.mulLeft psi)
  intro chi
  change _ = (psi * chi) (a : ZMod q) * (f psi * g (psi⁻¹ * (psi * chi)))
  simp only [inv_mul_cancel_left, MulChar.mul_apply]
  ring

end LiuWang.Proof.MajorZeroInteraction
