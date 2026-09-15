import LiuWang.Proof.Campaign20260915.ZetaValidation.BernoulliKernel

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem fract_on_integer_unit {n : ℕ} {u : ℝ} (hu : u ∈ Ioo (n : ℝ) (n + 1)) :
    Int.fract u = u - n := by
  rw [Int.fract, Int.floor_eq_on_Ico (n : ℤ) u (by simpa using ⟨hu.1.le, hu.2⟩)]
  simp

theorem bernoulli_integral_unit (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ u in (n : ℝ)..(n + 1), bernoulliKernel k s u) =
      (normalizedBernoulli (k + 1) 0 : ℂ) *
        (((n : ℂ) + 1) ^ (-s - k) - (n : ℂ) ^ (-s - k)) +
      (s + k) * ∫ u in (n : ℝ)..(n + 1), bernoulliKernel (k + 1) s u := by
  let p : ℝ → ℂ := fun u => (normalizedBernoulli (k + 1) (u - n) : ℂ)
  let p' : ℝ → ℂ := fun u => (normalizedBernoulli k (u - n) : ℂ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hab : (n : ℝ) ≤ n + 1 := by linarith
  have hp : ∀ u ∈ Set.uIcc (n : ℝ) (n + 1), HasDerivAt p (p' u) u := by
    intro u _
    simpa [p, p'] using
      ((hasDerivAt_normalizedBernoulli k (u - n)).comp u
        ((hasDerivAt_id u).sub_const (n : ℝ))).ofReal_comp
  have he : -s - (k : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [sub_re, neg_re, natCast_re, zero_re] at hh
    linarith [Nat.cast_nonneg k (α := ℝ)]
  have hc : ∀ u ∈ Set.uIcc (n : ℝ) (n + 1),
      HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s - k))
        ((-s - k) * (u : ℂ) ^ (-s - (k + 1 : ℕ))) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    convert hasDerivAt_ofReal_cpow_const (hn0.trans_le hu.1).ne' he using 1
    push_cast
    congr 1
    ring
  have hip : IntervalIntegrable p' volume (n : ℝ) (n + 1) :=
    (Complex.continuous_ofReal.comp
      ((continuous_normalizedBernoulli k).comp
        (continuous_id.sub continuous_const))).intervalIntegrable _ _
  have hic : IntervalIntegrable
      (fun u : ℝ => (-s - k) * (u : ℂ) ^ (-s - (k + 1 : ℕ))) volume
      (n : ℝ) (n + 1) :=
    ((Complex.continuousOn_ofReal_cpow hn0).const_mul _).intervalIntegrable_of_Icc hab
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul hc hp hic hip
  have hl :
      (∫ u in (n : ℝ)..(n + 1), (u : ℂ) ^ (-s - k) * p' u) =
        ∫ u in (n : ℝ)..(n + 1), bernoulliKernel k s u := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro u hu
    rw [bernoulliKernel, fract_on_integer_unit hu]
    exact mul_comm _ _
  have hr :
      (∫ u in (n : ℝ)..(n + 1), (-s - k) * (u : ℂ) ^ (-s - (k + 1 : ℕ)) * p u) =
        (-s - k) * ∫ u in (n : ℝ)..(n + 1), bernoulliKernel (k + 1) s u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro u hu
    change (-s - k) * (u : ℂ) ^ (-s - (k + 1 : ℕ)) * p u =
      (-s - k) * ((normalizedBernoulli (k + 1) (Int.fract u) : ℂ) *
        (u : ℂ) ^ (-s - (k + 1 : ℕ)))
    rw [fract_on_integer_unit hu]
    dsimp [p]
    ring
  have hp0 : p n = (normalizedBernoulli (k + 1) 0 : ℂ) := by simp [p]
  have hp1 : p ((n : ℝ) + 1) = (normalizedBernoulli (k + 1) 0 : ℂ) := by
    simp [p, normalizedBernoulli_one (k + 1) (by omega)]
  rw [hl, hr, hp0, hp1] at hi
  rw [hi]
  push_cast
  ring

private theorem interval_of_tail {f : ℝ → ℂ} {N a b : ℝ}
    (hf : IntegrableOn f (Ioi N)) (hNa : N ≤ a) (hab : a ≤ b) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (hf.mono_set (fun _ hu => hNa.trans_lt hu.1))

theorem bernoulli_integral_nat_interval (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    (∫ u in (N : ℝ)..(N + m : ℕ), bernoulliKernel k s u) =
      (normalizedBernoulli (k + 1) 0 : ℂ) *
        (((N + m : ℕ) : ℂ) ^ (-s - k) - (N : ℂ) ^ (-s - k)) +
      (s + k) * ∫ u in (N : ℝ)..(N + m : ℕ), bernoulliKernel (k + 1) s u := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc := bernoulliKernel_integrable k (by linarith : 1 < s.re + k) hNR
  have hd := bernoulliKernel_integrable (k + 1)
    (by push_cast; linarith : 1 < s.re + (k + 1 : ℕ)) hNR
  induction m with
  | zero => simp
  | succ m ih =>
      have hNm : (N : ℝ) ≤ (N + m : ℕ) := by exact_mod_cast Nat.le_add_right N m
      have hmm : ((N + m : ℕ) : ℝ) ≤ (N + m : ℕ) + 1 := by linarith
      rw [Nat.add_succ, Nat.cast_succ]
      rw [← intervalIntegral.integral_add_adjacent_intervals
          (interval_of_tail hc le_rfl hNm) (interval_of_tail hc hNm hmm),
        ← intervalIntegral.integral_add_adjacent_intervals
          (interval_of_tail hd le_rfl hNm) (interval_of_tail hd hNm hmm)]
      rw [ih, bernoulli_integral_unit k hk hs (n := N + m) (by omega)]
      push_cast
      ring

theorem bernoulli_tail_step (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) :
    (∫ u in Ioi (N : ℝ), bernoulliKernel k s u) =
      -(normalizedBernoulli (k + 1) 0 : ℂ) * (N : ℂ) ^ (-s - k) +
      (s + k) * ∫ u in Ioi (N : ℝ), bernoulliKernel (k + 1) s u := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht : Tendsto (fun m : ℕ => ((N + m : ℕ) : ℝ)) atTop atTop := by
    simpa [Nat.add_comm, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat N)
  have hz : Tendsto (fun x : ℝ => (x : ℂ) ^ (-s - k)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_rpow_neg_atTop (by linarith : 0 < s.re + k)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
    simp only [sub_re, neg_re, natCast_re]
    ring
  have hc := intervalIntegral_tendsto_integral_Ioi (N : ℝ)
    (bernoulliKernel_integrable k (by linarith : 1 < s.re + k) hNR) ht
  have hd := intervalIntegral_tendsto_integral_Ioi (N : ℝ)
    (bernoulliKernel_integrable (k + 1)
      (by push_cast; linarith : 1 < s.re + (k + 1 : ℕ)) hNR) ht
  have hb := ((hz.comp ht).sub_const ((N : ℂ) ^ (-s - k))).const_mul
    (normalizedBernoulli (k + 1) 0 : ℂ)
  have hr := hb.add (hd.const_mul (s + k))
  have he :
      (fun m : ℕ => (normalizedBernoulli (k + 1) 0 : ℂ) *
        (((N + m : ℕ) : ℂ) ^ (-s - k) - (N : ℂ) ^ (-s - k)) +
          (s + k) * ∫ u in (N : ℝ)..(N + m : ℕ), bernoulliKernel (k + 1) s u) =
      (fun m : ℕ => ∫ u in (N : ℝ)..(N + m : ℕ), bernoulliKernel k s u) := by
    funext m
    exact (bernoulli_integral_nat_interval k hk hs hN m).symm
  simp only [Function.comp_def, ofReal_natCast] at hr
  rw [he] at hr
  simpa using tendsto_nhds_unique hc hr

#print axioms bernoulli_tail_step

end LiuWang.Proof.Campaign20260915.ZetaValidation
