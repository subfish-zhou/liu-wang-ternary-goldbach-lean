import LiuWang.Proof.MajorZeroInteraction.Arithmetic
import LiuWang.Proof.CircleLowerBound.Main

/-! The three signed terms share a character component and an integral.
Only after both contractions do we pay its arithmetic-weighted norm. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorArcApproximation

namespace LiuWang.Proof.MajorZeroInteraction

def zeroCoefficient {q : ℕ} [NeZero q] (N : ℕ) (eta : ℝ)
    (chi : Character q) : ℂ :=
  (q.totient : ℂ)⁻¹ * gaussSum chi⁻¹ ZMod.stdAddChar *
    zeroValueSum chi N (sourceT N) eta

theorem packet_eq_evaluation {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ)
    (ha : Nat.Coprime a q) :
    packet N a q eta = characterEvaluation (zeroCoefficient (q := q) N eta) a := by
  rw [packet_eq, zeroPacket_eq_all_values N a eta ha]
  unfold characterEvaluation zeroCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chi _
  rw [G_eq_char_mul_gaussSum ha]
  ring

def signedCoefficient {q : ℕ} [NeZero q] (N : ℕ) (eta : ℝ)
    (chi : Character q) : ℂ :=
  -3 * (principalCoefficient q * J N eta)^2 * zeroCoefficient N eta chi +
    3 * (principalCoefficient q * J N eta) *
      characterConvolution (zeroCoefficient N eta) (zeroCoefficient N eta) chi -
    characterConvolution
      (characterConvolution (zeroCoefficient N eta) (zeroCoefficient N eta))
      (zeroCoefficient N eta) chi

theorem interaction_eq_evaluation {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ)
    (ha : Nat.Coprime a q) :
    interactionKernel N a q eta =
      characterEvaluation (signedCoefficient (q := q) N eta) a := by
  have he : characterEvaluation (signedCoefficient (q := q) N eta) a =
      -3 * (principalCoefficient q * J N eta)^2 *
        characterEvaluation (zeroCoefficient (q := q) N eta) a +
      3 * (principalCoefficient q * J N eta) *
        characterEvaluation
          (characterConvolution (zeroCoefficient (q := q) N eta) (zeroCoefficient N eta)) a -
      characterEvaluation
        (characterConvolution
          (characterConvolution (zeroCoefficient (q := q) N eta) (zeroCoefficient N eta))
          (zeroCoefficient N eta)) a := by
    unfold characterEvaluation signedCoefficient
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 2 <;> apply Finset.sum_congr rfl <;> intro chi _ <;> ring
  rw [he]
  simp only [evaluate_convolution, ← packet_eq_evaluation N a eta ha]
  unfold interactionKernel
  ring

theorem continuous_zeroCoefficient {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) : Continuous (fun eta => zeroCoefficient N eta chi) := by
  unfold zeroCoefficient zeroValueSum
  exact continuous_const.mul (continuous_finsetSum _ fun rho _ =>
    continuous_const.mul (SingularIntegral.Jrho_continuous hN rho))

theorem continuous_signedCoefficient {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) : Continuous (fun eta => signedCoefficient N eta chi) := by
  have hz := continuous_zeroCoefficient (q := q) hN
  have hc (psi : Character q) :
      Continuous (fun eta =>
        characterConvolution (zeroCoefficient N eta) (zeroCoefficient N eta) psi) := by
    exact continuous_finsetSum _ fun tau _ => (hz tau).mul (hz (tau⁻¹ * psi))
  have ht : Continuous (fun eta =>
      characterConvolution
        (characterConvolution (zeroCoefficient N eta) (zeroCoefficient N eta))
        (zeroCoefficient N eta) chi) := by
    exact continuous_finsetSum _ fun psi _ => (hc psi).mul (hz (psi⁻¹ * chi))
  unfold signedCoefficient
  exact (((continuous_const.mul ((continuous_const.mul (continuous_J hN)).pow 2)).mul
    (hz chi)).add ((continuous_const.mul (continuous_const.mul (continuous_J hN))).mul
      (hc chi))).sub ht

def signedArcCoefficient {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : ℂ :=
  ∫ eta in -deltaRadius N q..deltaRadius N q,
    signedCoefficient N eta chi * charReal (-(N : ℝ) * eta)

theorem signed_coefficient_integrable {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) :
    IntervalIntegrable
      (fun eta => signedCoefficient N eta chi * charReal (-(N : ℝ) * eta))
      volume (-deltaRadius N q) (deltaRadius N q) := by
  have hp : Continuous (fun eta : ℝ => charReal (-(N : ℝ) * eta)) := by
    unfold charReal
    fun_prop
  exact ((continuous_signedCoefficient hN chi).mul hp).intervalIntegrable _ _

theorem arc_interaction_eq_character_sum {N q : ℕ} [NeZero q] (hN : 0 < N) :
    (∑ a ∈ numerators q,
      ∫ eta in -deltaRadius N q..deltaRadius N q,
        interactionKernel N a q eta * arcPhase N a q eta) =
      ∑ chi : Character q, phaseCoefficient N chi * signedArcCoefficient N chi := by
  have he (a : ℕ) (ha : a ∈ numerators q) :
      (∫ eta in -deltaRadius N q..deltaRadius N q,
        interactionKernel N a q eta * arcPhase N a q eta) =
      ∑ chi : Character q,
        (chi (a : ZMod q) * charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ))) *
          signedArcCoefficient N chi := by
    have hi (eta : ℝ) :
        interactionKernel N a q eta * arcPhase N a q eta =
        ∑ chi : Character q,
          (chi (a : ZMod q) * charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ))) *
            (signedCoefficient N eta chi * charReal (-(N : ℝ) * eta)) := by
      rw [interaction_eq_evaluation N a eta (mem_numerators.mp ha).2.2,
        arcPhase_split, characterEvaluation, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro chi _
      ring
    simp_rw [hi]
    rw [intervalIntegral.integral_finsetSum (fun chi _ =>
      (signed_coefficient_integrable hN chi).const_mul _)]
    simp only [intervalIntegral.integral_const_mul, signedArcCoefficient]
  rw [Finset.sum_congr rfl he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro chi _
  rw [phaseCoefficient, Finset.sum_mul]

def signedCost (N q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ chi : Character q, arithmeticWeight N chi * ‖signedArcCoefficient N chi‖

theorem signedCost_eq {q : ℕ} [NeZero q] (N : ℕ) :
    signedCost N q =
      ∑ chi : Character q, arithmeticWeight N chi * ‖signedArcCoefficient N chi‖ := by
  simp only [signedCost, dif_neg (NeZero.ne q)]

theorem norm_arc_interaction_le {N q : ℕ} [NeZero q] (hN : 0 < N) :
    ‖∑ a ∈ numerators q,
      ∫ eta in -deltaRadius N q..deltaRadius N q,
        interactionKernel N a q eta * arcPhase N a q eta‖ ≤ signedCost N q := by
  rw [arc_interaction_eq_character_sum hN, signedCost_eq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro chi _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_phaseCoefficient_le_weight N chi) (norm_nonneg _)

def totalSignedCost (N : ℕ) : ℝ :=
  ∑ q ∈ denominators (sourceP N), signedCost N q

theorem norm_interaction_le_totalSignedCost {N : ℕ} (hN : 0 < N) :
    ‖interactionIntegral N‖ ≤ totalSignedCost N := by
  rw [interactionIntegral, coreIndices, Finset.sum_sigma, totalSignedCost]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  exact norm_arc_interaction_le hN

theorem re_interaction_lower {N : ℕ} (hN : 0 < N) :
    -totalSignedCost N ≤ (interactionIntegral N).re := by
  have he := Complex.re_le_norm (-interactionIntegral N)
  rw [Complex.neg_re, norm_neg] at he
  linarith [norm_interaction_le_totalSignedCost hN]

theorem divisor_arc_only_principal {N q : ℕ} [NeZero q] (hN : 0 < N) (hd : q ∣ N) :
    (∑ a ∈ numerators q,
      ∫ eta in -deltaRadius N q..deltaRadius N q,
        interactionKernel N a q eta * arcPhase N a q eta) =
      ramanujan N q * signedArcCoefficient N (1 : Character q) := by
  rw [arc_interaction_eq_character_sum hN]
  rw [Fintype.sum_eq_single (1 : Character q)]
  · rw [phaseCoefficient_principal]
  · intro chi hc
    rw [phaseCoefficient_vanishes hd hc, zero_mul]

theorem signedCost_divisor {q : ℕ} [NeZero q] {N : ℕ} (hd : q ∣ N) :
    signedCost N q = ‖ramanujan N q‖ * ‖signedArcCoefficient N (1 : Character q)‖ := by
  rw [signedCost_eq, Fintype.sum_eq_single (1 : Character q)]
  · simp [arithmeticWeight]
  · intro chi hc
    simp [arithmeticWeight, hc, hd]

theorem lambdaTripleCount_ge_signedCost {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.48166084 * (N : ℝ)^2 - totalSignedCost N +
      (∫ alpha in M2 N, S N alpha^3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha^3 * charReal (-(N : ℝ) * alpha)).re -
      6760 * (N : ℝ)^2 / sourceL N^4 ≤ lambdaTripleCount N := by
  linarith [CircleLowerBound.lambdaTripleCount_ge_strong hN hodd,
    re_interaction_lower (nat_pos_of_exp_le hN)]

end LiuWang.Proof.MajorZeroInteraction
