import LiuWang.Proof.Campaign20260915.SecondTerminal.TwoCount

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

def lastKernel (H z : ℝ) : ℝ :=
  Real.exp (-z / 2) *
    (Real.exp (-((1 : ℝ) / 9.645908801) * H / z) -
      Real.exp (-0.2067 * H / z))

def lastCellValue (H u v : ℝ) : ℝ :=
  (v - u) *
    (Real.exp (-u / 2 - ((1 : ℝ) / 9.645908801) * H / v) -
      Real.exp (-v / 2 - 0.2067 * H / u))

theorem lastKernel_phase_form (H z : ℝ) :
    lastKernel H z =
      Real.exp (-z / 2 - ((1 : ℝ) / 9.645908801) * H / z) -
        Real.exp (-z / 2 - 0.2067 * H / z) := by
  unfold lastKernel
  rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
  congr 1 <;> congr 1 <;> ring

theorem lastKernel_nonneg {H z : ℝ} (hH : 0 ≤ H) (hz : 0 < z) :
    0 ≤ lastKernel H z := by
  apply mul_nonneg (Real.exp_pos _).le
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right
    (by norm_num : (1 : ℝ) / 9.645908801 ≤ 0.2067) hH
  exact div_le_div_of_nonneg_right (by linarith) hz.le

theorem lastKernel_continuousOn {H u v : ℝ} (hu : 0 < u) :
    ContinuousOn (lastKernel H) (Set.Icc u v) := by
  have hz : ∀ z ∈ Set.Icc u v, z ≠ 0 :=
    fun z hz => (hu.trans_le hz.1).ne'
  unfold lastKernel
  exact (Real.continuous_exp.comp_continuousOn
    (continuousOn_id.neg.div_const 2)).mul
      ((Real.continuous_exp.comp_continuousOn
        (continuousOn_const.div continuousOn_id hz)).sub
        (Real.continuous_exp.comp_continuousOn
          (continuousOn_const.div continuousOn_id hz)))

theorem lastKernel_le_signed_cell {H u v z : ℝ}
    (hH : 0 ≤ H) (hu : 0 < u) (hz : z ∈ Set.Icc u v) :
    lastKernel H z ≤
      Real.exp (-u / 2 - ((1 : ℝ) / 9.645908801) * H / v) -
        Real.exp (-v / 2 - 0.2067 * H / u) := by
  have hz0 : 0 < z := hu.trans_le hz.1
  have ha := div_le_div_of_nonneg_left
    (show 0 ≤ ((1 : ℝ) / 9.645908801) * H by positivity) hz0 hz.2
  have hb := div_le_div_of_nonneg_left
    (show 0 ≤ (0.2067 : ℝ) * H by positivity) hu hz.1
  rw [lastKernel_phase_form]
  apply sub_le_sub
  · exact Real.exp_le_exp.mpr (by linarith [hz.1])
  · exact Real.exp_le_exp.mpr (by linarith [hz.2])

theorem last_integral_le_cell {H u v : ℝ}
    (hH : 0 ≤ H) (hu : 0 < u) (huv : u ≤ v) :
    (∫ z in u..v, lastKernel H z) ≤ lastCellValue H u v := by
  have hi := intervalIntegral.integral_mono_on huv
    ((lastKernel_continuousOn hu).intervalIntegrable_of_Icc (μ := volume) huv)
    (intervalIntegrable_const (c :=
      Real.exp (-u / 2 - ((1 : ℝ) / 9.645908801) * H / v) -
        Real.exp (-v / 2 - 0.2067 * H / u)))
    (fun z hz => lastKernel_le_signed_cell hH hu hz)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, lastCellValue] using hi

theorem last_integral_le_partition {H : ℝ} (hH : 0 ≤ H)
    (n : ℕ) (p : ℕ → ℝ)
    (hp : MonotoneOn p (Set.Icc 0 n)) (hp0 : 0 < p 0) :
    (∫ z in p 0..p n, lastKernel H z) ≤
      ∑ i ∈ Finset.range n, lastCellValue H (p i) (p (i + 1)) := by
  have hlo (i : ℕ) (hi : i ≤ n) : p 0 ≤ p i :=
    hp ⟨le_rfl, Nat.zero_le _⟩ ⟨Nat.zero_le _, hi⟩ (Nat.zero_le _)
  have hord (i : ℕ) (hi : i < n) : p i ≤ p (i + 1) :=
    hp ⟨Nat.zero_le _, hi.le⟩ ⟨Nat.zero_le _, hi⟩ (Nat.le_succ _)
  have hint (i : ℕ) (hi : i < n) :
      IntervalIntegrable (lastKernel H) volume (p i) (p (i + 1)) :=
    (lastKernel_continuousOn (hp0.trans_le (hlo i hi.le))).intervalIntegrable_of_Icc
      (hord i hi)
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  apply Finset.sum_le_sum
  intro i hi
  have hin := Finset.mem_range.mp hi
  exact last_integral_le_cell hH (hp0.trans_le (hlo i hin.le)) (hord i hin)

theorem actual_last_strip_partition_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (n : ℕ) (p : ℕ → ℝ) (hp : MonotoneOn p (Set.Icc 0 n))
    (ha : p 0 = lowerLog (sourceL N)) (hb : p n = upperLog (sourceL N)) :
    (8 * (N : ℝ) * Real.sqrt q / q.totient) *
      (∫ y in (omegaCutoff N q)..middleUpper N q, heightKernel y *
        ∫ alpha in stripUpper q y..siegelCutoff q y,
          alphaKernel (0.001 * (N : ℝ)) alpha *
            (DirichletZeroCount.familyCount q alpha y : ℝ)) ≤
      (16 * (N : ℝ)) * ((q : ℝ) / q.totient) *
        ∑ i ∈ Finset.range n,
          lastCellValue (sourceL N + Real.log 0.001) (p i) (p (i + 1)) := by
  have hH : 0 ≤ sourceL N + Real.log 0.001 := by
    rw [← log_window_eq (nat_pos_of_exp_le hN)]
    exact Real.log_nonneg (window_base_ge_one hN)
  have hp0 : 0 < p 0 := by
    rw [ha]
    exact (original_endpoints (sourceL_ge_3100 hN)).1
  have hi := last_integral_le_partition hH n p hp hp0
  rw [ha, hb] at hi
  exact (actual_last_strip_log_bound_T2 hN hq).trans
    (mul_le_mul_of_nonneg_left hi (by positivity))

#print axioms last_integral_le_partition
#print axioms actual_last_strip_partition_bound

end LiuWang.Proof.Campaign20260915.SecondTerminal
