import LiuWang.Proof.SourceRoute.MajorOrdinary.PacketBounds

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularSeries LiuWang.Proof.SingularIntegral
open LiuWang.Proof.MajorArcApproximation LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.SourceRoute.MajorOrdinary

def I12Arc (N q : ℕ) : ℂ :=
  ∑ a ∈ numerators q, (-3 * principalCoefficient q ^ 2) *
    ∫ eta in -deltaRadius N q..deltaRadius N q,
      J N eta ^ 2 * packet N a q eta * arcPhase N a q eta

def I13Arc (N q : ℕ) : ℂ :=
  ∑ a ∈ numerators q, (3 * principalCoefficient q) *
    ∫ eta in -deltaRadius N q..deltaRadius N q,
      packet N a q eta ^ 2 * J N eta * arcPhase N a q eta

def I14Arc (N q : ℕ) : ℂ :=
  ∑ a ∈ numerators q, -(∫ eta in -deltaRadius N q..deltaRadius N q,
    packet N a q eta ^ 3 * arcPhase N a q eta)

def I12 (N : ℕ) : ℂ := ∑ q ∈ denominators (sourceP N), I12Arc N q
def I13 (N : ℕ) : ℂ := ∑ q ∈ denominators (sourceP N), I13Arc N q
def I14 (N : ℕ) : ℂ := ∑ q ∈ denominators (sourceP N), I14Arc N q

theorem interactionArc_split {N : ℕ} (hN : 0 < N) (q : ℕ) :
    (∑ a ∈ numerators q, ∫ eta in -deltaRadius N q..deltaRadius N q,
      interactionKernel N a q eta * arcPhase N a q eta) =
        I12Arc N q + I13Arc N q + I14Arc N q := by
  simp only [I12Arc, I13Arc, I14Arc, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hj := continuous_J hN
  have hz := continuous_packet hN a q
  have hp := continuous_arcPhase N a q
  have h1 : IntervalIntegrable (fun eta => (-3 * principalCoefficient q ^ 2) *
      (J N eta ^ 2 * packet N a q eta * arcPhase N a q eta))
      volume (-deltaRadius N q) (deltaRadius N q) :=
    (continuous_const.mul (((hj.pow 2).mul hz).mul hp)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun eta => (3 * principalCoefficient q) *
      (packet N a q eta ^ 2 * J N eta * arcPhase N a q eta))
      volume (-deltaRadius N q) (deltaRadius N q) :=
    (continuous_const.mul (((hz.pow 2).mul hj).mul hp)).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun eta => -(packet N a q eta ^ 3 * arcPhase N a q eta))
      volume (-deltaRadius N q) (deltaRadius N q) :=
    (((hz.pow 3).mul hp).neg).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_neg, ← intervalIntegral.integral_add h1 h2,
    ← intervalIntegral.integral_add (h1.add h2) h3]
  congr 1
  ext eta
  unfold interactionKernel
  ring

theorem interactionIntegral_split {N : ℕ} (hN : 0 < N) :
    interactionIntegral N = I12 N + I13 N + I14 N := by
  simp only [interactionIntegral, coreIndices, Finset.sum_sigma,
    interactionArc_split hN, I12, I13, I14, Finset.sum_add_distrib]

theorem ordinaryIntegral_split {N : ℕ}
    (hnone : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      ∀ chi : Character q, exceptionalValues N chi = ∅) (hN : 0 < N) :
    regularInteractionIntegral N = I12 N + I13 N + I14 N := by
  rw [← interactionIntegral_split hN]
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hq, ha⟩ := Finset.mem_sigma.mp hi
  let : NeZero i.1 := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  congr 1
  ext eta
  rw [(interaction_no_exceptional N i.2 eta (mem_numerators.mp ha).2.2
    (hnone i.1 hq)).2]

def jCubicBound (N : ℕ) : ℝ := (2.994006 / Real.pi) * (N : ℝ) ^ 2

def packetCubicBound (N q : ℕ) [NeZero q] : ℝ :=
  2 * deltaRadius N q * packetBound N q ^ 3

theorem jCubicBound_nonneg (N : ℕ) : 0 ≤ jCubicBound N := by
  unfold jCubicBound
  positivity

theorem packetCubicBound_nonneg {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) : 0 ≤ packetCubicBound N q := by
  unfold packetCubicBound
  exact mul_nonneg (by linarith [deltaRadius_pos hN (NeZero.pos q)])
    (pow_nonneg (packetBound_nonneg N q) 3)

theorem linearMoment_le {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (ha : Nat.Coprime a q) :
    ‖∫ eta in -deltaRadius N q..deltaRadius N q,
      J N eta ^ 2 * packet N a q eta * arcPhase N a q eta‖ ≤
        jCubicBound N ^ (2 / 3 : ℝ) * packetCubicBound N q ^ (1 / 3 : ℝ) := by
  have hd := (deltaRadius_pos hN (NeZero.pos q)).le
  apply (norm_integral_sq_mul_phase_le (continuous_J (nat_pos_of_exp_le hN))
    (continuous_packet (nat_pos_of_exp_le hN) a q)
    (fun eta => charReal_norm _) hd).trans
  exact mul_le_mul
    (Real.rpow_le_rpow (cubicMass_nonneg hd _) (cubicMass_J_source (nat_pos_of_exp_le hN) hd)
      (by norm_num))
    (Real.rpow_le_rpow (cubicMass_nonneg hd _) (cubicMass_packet hN ha) (by norm_num))
    (Real.rpow_nonneg (cubicMass_nonneg hd _) _) (Real.rpow_nonneg (jCubicBound_nonneg N) _)

theorem quadraticMoment_le {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (ha : Nat.Coprime a q) :
    ‖∫ eta in -deltaRadius N q..deltaRadius N q,
      packet N a q eta ^ 2 * J N eta * arcPhase N a q eta‖ ≤
        packetCubicBound N q ^ (2 / 3 : ℝ) * jCubicBound N ^ (1 / 3 : ℝ) := by
  have hd := (deltaRadius_pos hN (NeZero.pos q)).le
  apply (norm_integral_sq_mul_phase_le (continuous_packet (nat_pos_of_exp_le hN) a q)
    (continuous_J (nat_pos_of_exp_le hN)) (fun eta => charReal_norm _) hd).trans
  exact mul_le_mul
    (Real.rpow_le_rpow (cubicMass_nonneg hd _) (cubicMass_packet hN ha) (by norm_num))
    (Real.rpow_le_rpow (cubicMass_nonneg hd _) (cubicMass_J_source (nat_pos_of_exp_le hN) hd)
      (by norm_num))
    (Real.rpow_nonneg (cubicMass_nonneg hd _) _) (Real.rpow_nonneg (packetCubicBound_nonneg hN) _)

theorem cubicMoment_le {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (ha : Nat.Coprime a q) :
    ‖∫ eta in -deltaRadius N q..deltaRadius N q,
      packet N a q eta ^ 3 * arcPhase N a q eta‖ ≤ packetCubicBound N q := by
  apply (intervalIntegral.norm_integral_le_integral_norm
    (by linarith [deltaRadius_pos hN (NeZero.pos q)] :
      -deltaRadius N q ≤ deltaRadius N q)).trans
  simpa only [norm_mul, norm_pow, arcPhase, charReal_norm, mul_one,
    cubicMass, packetCubicBound] using cubicMass_packet hN ha

theorem norm_sum_numerators_le {q : ℕ} {f : ℕ → ℂ} {B : ℝ}
    (hb : ∀ a ∈ numerators q, ‖f a‖ ≤ B) :
    ‖∑ a ∈ numerators q, f a‖ ≤ (q.totient : ℝ) * B := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hb).trans_eq
  simp only [Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast reducedResidues_card q

def linearCost (N q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (q.totient : ℝ) * (3 * ‖principalCoefficient q‖ ^ 2 *
      (jCubicBound N ^ (2 / 3 : ℝ) * packetCubicBound N q ^ (1 / 3 : ℝ)))

def quadraticCost (N q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (q.totient : ℝ) * (3 * ‖principalCoefficient q‖ *
      (packetCubicBound N q ^ (2 / 3 : ℝ) * jCubicBound N ^ (1 / 3 : ℝ)))

def cubicCost (N q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (q.totient : ℝ) * packetCubicBound N q

theorem I12Arc_bound {N q : ℕ} [NeZero q] (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖I12Arc N q‖ ≤ linearCost N q := by
  rw [I12Arc, linearCost, dif_neg (NeZero.ne q)]
  apply norm_sum_numerators_le
  intro a ha
  rw [norm_mul, norm_mul, norm_pow]
  norm_num
  exact mul_le_mul_of_nonneg_left
    (linearMoment_le hN (mem_numerators.mp ha).2.2) (by positivity)

theorem I13Arc_bound {N q : ℕ} [NeZero q] (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖I13Arc N q‖ ≤ quadraticCost N q := by
  rw [I13Arc, quadraticCost, dif_neg (NeZero.ne q)]
  apply norm_sum_numerators_le
  intro a ha
  rw [norm_mul, norm_mul]
  norm_num
  exact mul_le_mul_of_nonneg_left
    (quadraticMoment_le hN (mem_numerators.mp ha).2.2) (by positivity)

theorem I14Arc_bound {N q : ℕ} [NeZero q] (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖I14Arc N q‖ ≤ cubicCost N q := by
  rw [I14Arc, cubicCost, dif_neg (NeZero.ne q)]
  apply norm_sum_numerators_le
  intro a ha
  rw [norm_neg]
  exact cubicMoment_le hN (mem_numerators.mp ha).2.2

theorem I12_bound {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖I12 N‖ ≤ ∑ q ∈ denominators (sourceP N), linearCost N q := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  exact I12Arc_bound hN

theorem I13_bound {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖I13 N‖ ≤ ∑ q ∈ denominators (sourceP N), quadraticCost N q := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  exact I13Arc_bound hN

theorem I14_bound {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖I14 N‖ ≤ ∑ q ∈ denominators (sourceP N), cubicCost N q := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  let : NeZero q := ⟨by have := (Finset.mem_Icc.mp hq).1; omega⟩
  exact I14Arc_bound hN

end LiuWang.Proof.SourceRoute.MajorOrdinary
