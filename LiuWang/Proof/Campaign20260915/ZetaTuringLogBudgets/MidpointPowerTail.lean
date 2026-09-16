import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.RealDirichletBudget

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem neg_rpow_tangent {s x c : ℝ} (hs : 0 ≤ s) (hx : 0 < x) (hc : 0 < c) :
    c ^ (-s) * (1 - s * (x / c - 1)) ≤ x ^ (-s) := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hc)
  have he := Real.add_one_le_exp (-s * Real.log (x / c))
  have hmul := mul_le_mul_of_nonneg_left hlog hs
  have h : 1 - s * (x / c - 1) ≤ (x / c) ^ (-s) := by
    rw [Real.rpow_def_of_pos (div_pos hx hc)]
    have hid : Real.log (x / c) * -s = -s * Real.log (x / c) := by ring
    rw [hid]
    linarith
  have h' := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hc.le (-s))
  rw [Real.div_rpow hx.le hc.le] at h'
  have hn : c ^ (-s) ≠ 0 := (Real.rpow_pos_of_pos hc (-s)).ne'
  simpa [mul_div_cancel₀, hn] using h'

theorem neg_rpow_midpoint_integral {s c : ℝ} (hs : 0 ≤ s) (hc : 1 ≤ c) :
    c ^ (-s) ≤ ∫ x in (c - 1 / 2)..(c + 1 / 2), x ^ (-s) := by
  have hc0 : 0 < c := by linarith
  have hi : IntervalIntegrable (fun x : ℝ => x ^ (-s)) volume (c - 1 / 2) (c + 1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hx.1] : x ≠ 0))).continuousWithinAt
  have h := intervalIntegral.integral_mono_on (by linarith : c - 1 / 2 ≤ c + 1 / 2)
    ((by fun_prop : Continuous (fun x : ℝ => c ^ (-s) * (1 - s * (x / c - 1)))).intervalIntegrable _ _)
    hi (fun x hx => neg_rpow_tangent hs (by linarith [hx.1]) hc0)
  have he (x : ℝ) : c ^ (-s) * (1 - s * (x / c - 1)) =
      c ^ (-s) * (1 + s) - (c ^ (-s) * s / c) * x := by ring
  simp_rw [he] at h
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous (fun x : ℝ => (c ^ (-s) * s / c) * x)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id] at h
  have hid :
      ((c + 1 / 2 - (c - 1 / 2)) * (c ^ (-s) * (1 + s)) -
        (c ^ (-s) * s / c) * (((c + 1 / 2) ^ 2 - (c - 1 / 2) ^ 2) / 2)) = c ^ (-s) := by
    field_simp
    ring
  simpa only [smul_eq_mul, hid] using h

theorem rpow_midpoint_tail_upper {s : ℝ} (hs : 1 < s) (N : ℕ) :
    (∑' k : ℕ, ((k + N + 1 : ℕ) : ℝ) ^ (-s)) ≤
      ∫ x in Set.Ioi ((N : ℝ) + 1 / 2), x ^ (-s) := by
  have hint {a : ℝ} (ha : 0 < a) :
      IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha
  have hsum : Summable (fun k : ℕ => ((k + N + 1 : ℕ) : ℝ) ^ (-s)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) ^ (-s)) (N + 1)).mpr
        (Real.summable_nat_rpow.mpr (by linarith))
  apply le_of_tendsto hsum.tendsto_sum_tsum_nat
  apply Filter.Eventually.of_forall
  intro M
  have hblock (k : ℕ) :
      ((k + N + 1 : ℕ) : ℝ) ^ (-s) ≤
        ∫ x in ((N : ℝ) + 1 / 2 + k)..((N : ℝ) + 1 / 2 + (k + 1 : ℕ)), x ^ (-s) := by
    have h := neg_rpow_midpoint_integral (by linarith : 0 ≤ s)
      (by exact_mod_cast (show 1 ≤ k + N + 1 by omega) : (1 : ℝ) ≤ (k + N + 1 : ℕ))
    convert! h using 1
    push_cast
    congr 1 <;> ring
  have hi (k : ℕ) : IntervalIntegrable (fun x : ℝ => x ^ (-s)) volume
      ((N : ℝ) + 1 / 2 + k) ((N : ℝ) + 1 / 2 + (k + 1 : ℕ)) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by push_cast; linarith)] at hx
    have hx0 : 0 < x := by
      linarith [hx.1, Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) k]
    exact (Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne')).continuousWithinAt
  have hadd := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (N : ℝ) + 1 / 2 + k) (n := M) (fun k _ => hi k)
  have hsumle := Finset.sum_le_sum (s := Finset.range M) (fun k _ => hblock k)
  rw [hadd] at hsumle
  norm_num only [Nat.cast_zero, add_zero] at hsumle
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (hint (by positivity : (0 : ℝ) < N + 1 / 2))
    (hint (by positivity : (0 : ℝ) < N + 1 / 2 + M))
  have hn : 0 ≤ ∫ x in Set.Ioi ((N : ℝ) + 1 / 2 + M), x ^ (-s) :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => Real.rpow_nonneg (by
      change (N : ℝ) + 1 / 2 + M < x at hx
      linarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) M]) _)
  linarith

theorem norm_zeta_real_midpoint_upper {s : ℝ} (hs : 1 < s) (N : ℕ) :
    ‖riemannZeta (s : ℂ)‖ ≤
      (∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ (-s)) +
        ((N : ℝ) + 1 / 2) ^ (1 - s) / (s - 1) := by
  have hsumm := Real.summable_nat_rpow.mpr (by linarith : -s < -1)
  have he := hsumm.sum_add_tsum_nat_add (N + 1)
  have ht := rpow_midpoint_tail_upper hs N
  rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) (by positivity)] at ht
  have hid : -((N : ℝ) + 1 / 2) ^ (-s + 1) / (-s + 1) =
      ((N : ℝ) + 1 / 2) ^ (1 - s) / (s - 1) := by
    rw [show -s + 1 = 1 - s by ring, show 1 - s = -(s - 1) by ring]
    field_simp
  rw [hid] at ht
  simp only [← Nat.add_assoc] at he
  rw [norm_zeta_real_eq_rpow_sum hs]
  linarith

#print axioms rpow_midpoint_tail_upper
#print axioms norm_zeta_real_midpoint_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
