import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.CellCertificate

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

def refinedPoint (i : ℕ) : ℝ :=
  25.329413 + (59.721417 - 25.329413) * i / 1024

def refinedMidpoint (i : ℕ) : ℝ := (refinedPoint i + refinedPoint (i + 1)) / 2

theorem refinedPoint_monotone : Monotone refinedPoint := by
  intro i j hij
  have h : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
  unfold refinedPoint
  linarith

theorem refined_partition_bound :
    originalDensityScalar 3100 ≤
      (8 * 6.76661 * (1.7810725 * 3.182937 + 2.50637 / 3.182936) * 3100) *
        ∑ i ∈ Finset.range 1024,
          FixedIntegral.cellValue 3093.092244719
            (refinedPoint i) (refinedPoint (i + 1)) (refinedMidpoint i) := by
  apply FixedIntegral.original_fixed_directed_bound 1024 refinedPoint refinedMidpoint
    (refinedPoint_monotone.monotoneOn _)
  · norm_num [refinedPoint]
  · simpa only [refinedPoint, Nat.cast_zero, mul_zero, zero_div, add_zero] using lower_endpoint
  · convert upper_endpoint using 1
    norm_num [refinedPoint]
  · norm_num [refinedPoint]
  · exact window_H_lower
  · intro i _
    have h := refinedPoint_monotone (Nat.le_succ i)
    unfold refinedMidpoint
    exact ⟨by linarith, by linarith⟩
  · exact exp_phase_upper
  · exact exp_euler_upper
  · norm_num
  · exact loglog_interval.1
  · exact loglog_interval.2

def refinedCellUpper (i : ℕ) : ℝ :=
  cellUpper 3093.092244719 (refinedPoint i) (refinedPoint (i + 1)) (refinedMidpoint i)

theorem refinedCell_bound {i : ℕ} (hi : i < 1024) :
    FixedIntegral.cellValue 3093.092244719
      (refinedPoint i) (refinedPoint (i + 1)) (refinedMidpoint i) ≤
      refinedCellUpper i := by
  have hp (j : ℕ) (hj : j ≤ 1024) : refinedPoint j ∈ Set.Icc 25 60 := by
    have h := Nat.cast_le (α := ℝ).mpr hj
    norm_num only [Nat.cast_ofNat] at h
    have h0 := Nat.cast_nonneg (α := ℝ) j
    unfold refinedPoint
    constructor <;> linarith
  have hu := hp i hi.le
  have hv := hp (i + 1) hi
  have hm : refinedMidpoint i ∈ Set.Icc 25 60 := by
    unfold refinedMidpoint
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  exact cellValue_le_cellUpper (phase_certificate_domain hm hu).1
    (phase_certificate_domain hm hv).1 (phase_certificate_domain hm hu).2

theorem refined_rational_reduction :
    originalDensityScalar 3100 ≤
      (8 * 6.76661 * (1.7810725 * 3.182937 + 2.50637 / 3.182936) * 3100) *
        ∑ i ∈ Finset.range 1024, refinedCellUpper i := by
  apply refined_partition_bound.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum (fun i hi => refinedCell_bound (Finset.mem_range.mp hi))

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
