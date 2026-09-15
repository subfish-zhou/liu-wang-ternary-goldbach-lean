import LiuWang.Proof.VaughanRecovery.Moment

/-! 真实 Möbius 质量、系数矩和行最大值在同一个平方根内合成。 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.VaughanRecovery

open Interfaces Parameters ArithmeticBounds LambdaMoment VaughanTypeII Finset

def moebiusMass (M : ℝ) : ℝ :=
  ∑ t ∈ blockSupport M, |(ArithmeticFunction.moebius t : ℝ)|

def actualEnergy (N : ℕ) (M α : ℝ) : ℝ :=
  moebiusMass M * actualMoment N ((N : ℝ) / M) * rowMax N M α

def energySum (N : ℕ) (E : ℝ → ℝ) : ℝ :=
  ∑ j ∈ range (dyadicCount N), Real.sqrt (E (dyadicScale N j))

def recoveredKappa : ℝ := Real.sqrt ((6111 / 10000) * (291 / 1000))

theorem moebiusMass_nonneg (M : ℝ) : 0 ≤ moebiusMass M :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem moebiusMass_le_linear {M : ℝ} (hM : 0 ≤ M) :
    moebiusMass M ≤ (30517 / 50000) * M + 272 :=
  sum_abs_moebius_dyadic_le_linear hM

theorem block_sq_le_actualEnergy {N : ℕ} {M : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hM : sourceVaughanV N ≤ M) (α : ℝ) :
    ‖block N M α‖ ^ 2 ≤ actualEnergy N M α := by
  apply (moebius_weighted_cauchy (blockSupport M) (fun t => innerSum N t α)).trans
  exact (mul_le_mul_of_nonneg_left (energy_le_moment_mul_rowMax hN hM α)
    (moebiusMass_nonneg M)).trans_eq (by unfold actualEnergy; rw [mul_assoc]; rfl)

theorem sourceS4_le_energySum {N : ℕ} {α : ℝ} {E : ℝ → ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hE : ∀ j < dyadicCount N, ‖block N (dyadicScale N j) α‖ ^ 2 ≤ E (dyadicScale N j)) :
    ‖VaughanTypeI.sourceS4 N α‖ ≤ energySum N E := by
  rw [sourceS4_eq_dyadic_blocks hN]
  exact (norm_sum_le _ _).trans
    (sum_le_sum fun j hj => Real.le_sqrt_of_sq_le (hE j (mem_range.mp hj)))

theorem sourceS4_le_actualEnergy {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (α : ℝ) :
    ‖VaughanTypeI.sourceS4 N α‖ ≤ energySum N (fun M => actualEnergy N M α) :=
  sourceS4_le_energySum hN fun j _ =>
    block_sq_le_actualEnergy hN (V_le_dyadicScale hN j) α

theorem actualEnergy_le_moment_budget {N : ℕ} {M α b : ℝ}
    (hb : actualMoment N ((N : ℝ) / M) ≤ b) :
    actualEnergy N M α ≤ moebiusMass M * b * rowMax N M α :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (moebiusMass_nonneg M)) (rowMax_nonneg N M α)

theorem sourceS4_le_W123 {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (α : ℝ) :
    ‖VaughanTypeI.sourceS4 N α‖ ≤ energySum N (fun M =>
      moebiusMass M * (((N : ℝ) / M) *
        (W1 N ((N : ℝ) / M) + W2 N ((N : ℝ) / M) + 2 * W3 N ((N : ℝ) / M))) *
          rowMax N M α) := by
  have hn := exp_2000_le_of_exp_3100_le hN
  apply sourceS4_le_energySum hn
  intro j hj
  exact (block_sq_le_actualEnergy hn (V_le_dyadicScale hn j) α).trans
    (actualEnergy_le_moment_budget
      (actualMoment_source_le_613 hN (V_le_dyadicScale hn j) (dyadicScale_lt_upper hn hj).le))

theorem sourceS4_le_primeEnergy {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (α : ℝ) :
    ‖VaughanTypeI.sourceS4 N α‖ ≤ energySum N (fun M =>
      moebiusMass M * (((N : ℝ) / M) * primeBudget N ((N : ℝ) / M)) * rowMax N M α) := by
  have hn := exp_2000_le_of_exp_3100_le hN
  apply sourceS4_le_energySum hn
  intro j hj
  exact (block_sq_le_actualEnergy hn (V_le_dyadicScale hn j) α).trans
    (actualEnergy_le_moment_budget
      (actual_moment_le_primeBudget hN (V_le_dyadicScale hn j) (dyadicScale_lt_upper hn hj).le))

theorem sourceS4_le_linear_primeEnergy {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (α : ℝ) :
    ‖VaughanTypeI.sourceS4 N α‖ ≤ energySum N (fun M =>
      ((30517 / 50000) * M + 272) *
        (((N : ℝ) / M) * primeBudget N ((N : ℝ) / M)) * rowMax N M α) := by
  apply (sourceS4_le_primeEnergy hN α).trans
  apply sum_le_sum
  intro j hj
  have hn := exp_2000_le_of_exp_3100_le hN
  have hp := actual_moment_le_primeBudget hN
    (V_le_dyadicScale hn j) (dyadicScale_lt_upper hn (mem_range.mp hj)).le
  have hb : 0 ≤ ((N : ℝ) / dyadicScale N j) *
      primeBudget N ((N : ℝ) / dyadicScale N j) :=
    (sum_nonneg fun _ _ => sq_nonneg _).trans hp
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (moebiusMass_le_linear (dyadicScale_pos hn j).le) hb)
      (rowMax_nonneg N _ α))

theorem block_sq_le_291 {N : ℕ} {M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : ℝ) / sourceVaughanU N) (α : ℝ) :
    ‖block N M α‖ ^ 2 ≤
      ((6111 / 10000) * (291 / 1000)) * (N : ℝ) *
        Real.log ((N : ℝ) / sourceVaughanV N) ^ 2 * rowMax N M α := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hM0 := (sourceVaughanV_pos hn).trans_le hM
  have h400 : (400000 : ℝ) ≤ M :=
    fourHundredThousand_le_exp_13066.trans ((sourceVaughanV_ge_exp_13066 hn).trans hM)
  calc
    _ ≤ actualEnergy N M α := block_sq_le_actualEnergy hn hM α
    _ ≤ moebiusMass M * ((291 / 1000) * ((N : ℝ) / M) *
        Real.log ((N : ℝ) / sourceVaughanV N) ^ 2) * rowMax N M α :=
      actualEnergy_le_moment_budget (actual_moment_le_291 hN hM hM')
    _ ≤ ((6111 / 10000) * M) * ((291 / 1000) * ((N : ℝ) / M) *
        Real.log ((N : ℝ) / sourceVaughanV N) ^ 2) * rowMax N M α := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (sum_abs_moebius_dyadic_le_6111 h400) (by positivity))
        (rowMax_nonneg N M α)
    _ = _ := by field_simp

theorem sourceS4_le_recoveredKappa {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (α : ℝ) :
    ‖VaughanTypeI.sourceS4 N α‖ ≤
      recoveredKappa * Real.sqrt (N : ℝ) * Real.log ((N : ℝ) / sourceVaughanV N) *
        ∑ j ∈ range (dyadicCount N), Real.sqrt (rowMax N (dyadicScale N j) α) := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hlog := (VaughanTypeIIBudget.log_Y_bounds hN).1
  apply (sourceS4_le_energySum hn (E := fun M =>
    ((6111 / 10000) * (291 / 1000)) * (N : ℝ) *
      Real.log ((N : ℝ) / sourceVaughanV N) ^ 2 * rowMax N M α)
    (fun j hj => block_sq_le_291 hN (V_le_dyadicScale hn j) (dyadicScale_lt_upper hn hj).le α)).trans_eq
  unfold energySum recoveredKappa
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [Real.sqrt_mul (by positivity :
    0 ≤ ((6111 / 10000) * (291 / 1000)) * (N : ℝ) *
      Real.log ((N : ℝ) / sourceVaughanV N) ^ 2),
    Real.sqrt_mul (by positivity : 0 ≤ ((6111 / 10000) * (291 / 1000)) * (N : ℝ)),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (6111 / 10000) * (291 / 1000)),
    Real.sqrt_sq hlog]

theorem recoveredKappa_le : recoveredKappa ≤ (0.4217 : ℝ) := by
  unfold recoveredKappa
  apply Real.sqrt_le_iff.mpr
  norm_num

end LiuWang.Proof.VaughanRecovery
