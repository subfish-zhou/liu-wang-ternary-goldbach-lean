import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral.CellIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral

theorem partition_integral_le_sum {H : ℝ} (n : ℕ) (p m : ℕ → ℝ)
    (hp : MonotoneOn p (Set.Icc 0 n)) (hp0 : 0 < p 0) (hH : 4 * p n < H)
    (hm : ∀ i < n, m i ∈ Set.Icc (p i) (p (i + 1))) :
    (∫ y in p 0..p n, densityKernel H y) ≤
      ∑ i ∈ Finset.range n, cellValue H (p i) (p (i + 1)) (m i) := by
  have hlo (i : ℕ) (hi : i ≤ n) : p 0 ≤ p i :=
    hp ⟨le_rfl, Nat.zero_le _⟩ ⟨Nat.zero_le _, hi⟩ (Nat.zero_le _)
  have hup (i : ℕ) (hi : i ≤ n) : p i ≤ p n :=
    hp ⟨Nat.zero_le _, hi⟩ ⟨Nat.zero_le _, le_rfl⟩ hi
  have hord (i : ℕ) (hi : i < n) : p i ≤ p (i + 1) :=
    hp ⟨Nat.zero_le _, hi.le⟩ ⟨Nat.zero_le _, hi⟩ (Nat.le_succ _)
  have hint (i : ℕ) (hi : i < n) :
      IntervalIntegrable (densityKernel H) volume (p i) (p (i + 1)) :=
    (densityKernel_continuousOn (hp0.trans_le (hlo i hi.le))
      (by linarith [hup (i + 1) hi])).intervalIntegrable_of_Icc (hord i hi)
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  apply Finset.sum_le_sum
  intro i hi
  have hin := Finset.mem_range.mp hi
  exact density_integral_le_cellValue (hp0.trans_le (hlo i hin.le))
    (hord i hin) (hm i hin) (by linarith [hup (i + 1) hin])

theorem density_integral_enclosure {H a b u v : ℝ} (hu : 0 < u)
    (hua : u ≤ a) (hab : a ≤ b) (hbv : b ≤ v) (hH : 4 * v < H) :
    (∫ y in a..b, densityKernel H y) ≤ ∫ y in u..v, densityKernel H y := by
  exact intervalIntegral.integral_mono_interval hua hab hbv
    (by
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro y hy
      exact densityKernel_nonnegative (hu.trans hy.1) (by linarith [hy.2]))
    ((densityKernel_continuousOn hu hH).intervalIntegrable_of_Icc
      (hua.trans (hab.trans hbv)))

theorem base_domain :
    0 < lowerLog 3100 ∧ lowerLog 3100 ≤ upperLog 3100 ∧
      4 * upperLog 3100 < (3100 : ℝ) + Real.log 0.001 := by
  have hb := base_log_domain
  have hH := (window_H_scaling (L := (3100 : ℝ)) le_rfl).1
  exact ⟨by linarith, by linarith, by linarith⟩

theorem original_fixed_partition_bound (n : ℕ) (p m : ℕ → ℝ)
    (hp : MonotoneOn p (Set.Icc 0 n))
    (ha : p 0 = lowerLog 3100) (hb : p n = upperLog 3100)
    (hm : ∀ i < n, m i ∈ Set.Icc (p i) (p (i + 1))) :
    originalDensityScalar 3100 ≤
      (8 * Real.exp (4 * 0.478) * sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) *
        ∑ i ∈ Finset.range n,
          cellValue ((3100 : ℝ) + Real.log 0.001) (p i) (p (i + 1)) (m i) := by
  have hd := base_domain
  have hs := partition_integral_le_sum n p m hp (ha ▸ hd.1) (hb ▸ hd.2.2) hm
  rw [ha, hb] at hs
  have hnu := (sourceNu_linear_scaling (L := (3100 : ℝ)) le_rfl).1
  exact mul_le_mul_of_nonneg_left hs (by positivity)

theorem original_fixed_enclosing_partition_bound (n : ℕ) (p m : ℕ → ℝ)
    (hp : MonotoneOn p (Set.Icc 0 n)) (hp0 : 0 < p 0)
    (ha : p 0 ≤ lowerLog 3100) (hb : upperLog 3100 ≤ p n)
    (hH : 4 * p n < (3100 : ℝ) + Real.log 0.001)
    (hm : ∀ i < n, m i ∈ Set.Icc (p i) (p (i + 1))) :
    originalDensityScalar 3100 ≤
      (8 * Real.exp (4 * 0.478) * sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) *
        ∑ i ∈ Finset.range n,
          cellValue ((3100 : ℝ) + Real.log 0.001) (p i) (p (i + 1)) (m i) := by
  have hs := partition_integral_le_sum n p m hp hp0 hH hm
  have he := density_integral_enclosure hp0 ha base_domain.2.1 hb hH
  have hnu := (sourceNu_linear_scaling (L := (3100 : ℝ)) le_rfl).1
  exact mul_le_mul_of_nonneg_left (he.trans hs) (by positivity)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral
