import LiuWang.Proof.Campaign20260915.ZetaValidation.AbelEvaluation

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def abelPrimitive (u : ℝ) : ℝ := Int.fract u * (Int.fract u - 1) / 2

def secondAbelKernel (s : ℂ) (u : ℝ) : ℂ :=
  (abelPrimitive u : ℂ) * (u : ℂ) ^ (-s - 2)

theorem abs_abelPrimitive_le (u : ℝ) : |abelPrimitive u| ≤ (1 / 8 : ℝ) := by
  have hf := Int.fract_nonneg u
  have h1 := Int.fract_lt_one u
  rw [abelPrimitive, abs_le]
  constructor
  · nlinarith [sq_nonneg (Int.fract u - 1 / 2)]
  · have h := mul_nonpos_of_nonneg_of_nonpos hf (by linarith : Int.fract u - 1 ≤ 0)
    linarith

theorem norm_secondAbelKernel_le {u : ℝ} (hu : 0 < u) (s : ℂ) :
    ‖secondAbelKernel s u‖ ≤ (1 / 8 : ℝ) * u ^ (-s.re - 2) := by
  rw [secondAbelKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hu]
  simpa using mul_le_mul_of_nonneg_right (abs_abelPrimitive_le u)
    (Real.rpow_nonneg hu.le (-s.re - 2))

theorem secondAbelKernel_integrable {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (secondAbelKernel s) (Ioi a) := by
  have hm : AEStronglyMeasurable (secondAbelKernel s) (volume.restrict (Ioi a)) := by
    unfold secondAbelKernel abelPrimitive
    exact (((measurable_fract.mul (measurable_fract.sub_const 1)).div_const 2).complex_ofReal.mul
      (Complex.measurable_ofReal.pow_const (-s - 2))).aestronglyMeasurable
  refine IntegrableOn.mono'
    ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 2 < -1) ha).const_mul (1 / 8)) hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_secondAbelKernel_le (ha.trans hu) s

theorem norm_secondAbelTail_le {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ‖∫ u in Ioi a, secondAbelKernel s u‖ ≤ a ^ (-s.re - 1) / (8 * (s.re + 1)) := by
  calc
    _ ≤ ∫ u in Ioi a, (1 / 8 : ℝ) * u ^ (-s.re - 2) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 2 < -1) ha).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact norm_secondAbelKernel_le (ha.trans hu) s
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha]
      rw [show -s.re - 2 + 1 = -s.re - 1 by ring,
        show -s.re - 1 = -(s.re + 1) by ring, neg_div_neg_eq]
      field_simp

private theorem fract_eq_on_unit {n : ℕ} {u : ℝ} (hu : u ∈ Ioo (n : ℝ) (n + 1)) :
    Int.fract u = u - n := by
  rw [Int.fract, Int.floor_eq_on_Ico (n : ℤ) u (by simpa using ⟨hu.1.le, hu.2⟩)]
  simp

theorem centeredAbel_integral_unit {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    (∫ u in (n : ℝ)..(n + 1), centeredAbelKernel s u) =
      (s + 1) * ∫ u in (n : ℝ)..(n + 1), secondAbelKernel s u := by
  let p : ℝ → ℂ := fun u => ((u : ℂ) - n) * ((u : ℂ) - n - 1) / 2
  let p' : ℝ → ℂ := fun u => (u : ℂ) - n - 1 / 2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hab : (n : ℝ) ≤ n + 1 := by linarith
  have hp : ∀ u ∈ Set.uIcc (n : ℝ) (n + 1), HasDerivAt p (p' u) u := by
    intro u _
    have hd : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := ofRealCLM.hasDerivAt
    convert ((hd.sub_const (n : ℂ)).mul ((hd.sub_const (n : ℂ)).sub_const 1)).div_const 2 using 1
    all_goals first | rfl | ring
  have he : -s - 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [sub_re, neg_re, one_re, zero_re] at hh
    linarith
  have hc : ∀ u ∈ Set.uIcc (n : ℝ) (n + 1),
      HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s - 1))
        ((-s - 1) * (u : ℂ) ^ (-s - 2)) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    convert hasDerivAt_ofReal_cpow_const (hn0.trans_le hu.1).ne' he using 1
    congr 1
    ring
  have hip : IntervalIntegrable p' volume (n : ℝ) (n + 1) :=
    (by fun_prop : Continuous p').intervalIntegrable _ _
  have hic : IntervalIntegrable
      (fun u : ℝ => (-s - 1) * (u : ℂ) ^ (-s - 2)) volume (n : ℝ) (n + 1) :=
    ((Complex.continuousOn_ofReal_cpow hn0).const_mul _).intervalIntegrable_of_Icc hab
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul hc hp hic hip
  have hk :
      (∫ u in (n : ℝ)..(n + 1), (u : ℂ) ^ (-s - 1) * p' u) =
        ∫ u in (n : ℝ)..(n + 1), centeredAbelKernel s u := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro u hu
    rw [centeredAbelKernel, fract_eq_on_unit hu]
    dsimp [p']
    push_cast
    ring
  have hj :
      (∫ u in (n : ℝ)..(n + 1), (-s - 1) * (u : ℂ) ^ (-s - 2) * p u) =
        (-s - 1) * ∫ u in (n : ℝ)..(n + 1), secondAbelKernel s u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro u hu
    change (-s - 1) * (u : ℂ) ^ (-s - 2) * p u =
      (-s - 1) * ((abelPrimitive u : ℂ) * (u : ℂ) ^ (-s - 2))
    rw [abelPrimitive, fract_eq_on_unit hu]
    dsimp [p]
    push_cast
    ring
  rw [hk, hj] at hi
  have hp0 : p n = 0 := by simp [p]
  have hp1 : p ((n : ℝ) + 1) = 0 := by simp [p]
  rw [hp0, hp1, mul_zero, mul_zero, sub_self] at hi
  rw [hi]
  ring

private theorem intervalIntegrable_from_tail {f : ℝ → ℂ} {N a b : ℝ}
    (hf : IntegrableOn f (Ioi N)) (hNa : N ≤ a) (hab : a ≤ b) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (hf.mono_set (fun _ hu => hNa.trans_lt hu.1))

theorem centeredAbel_integral_nat_interval {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    (∫ u in (N : ℝ)..(N + k : ℕ), centeredAbelKernel s u) =
      (s + 1) * ∫ u in (N : ℝ)..(N + k : ℕ), secondAbelKernel s u := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc := centeredAbelKernel_integrable hs hNR
  have hd := secondAbelKernel_integrable hs (zero_lt_one.trans_le hNR)
  induction k with
  | zero => simp
  | succ k ih =>
    have hNk : (N : ℝ) ≤ (N + k : ℕ) := by exact_mod_cast Nat.le_add_right N k
    have hkk : ((N + k : ℕ) : ℝ) ≤ (N + k : ℕ) + 1 := by linarith
    rw [Nat.add_succ, Nat.cast_succ]
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_from_tail hc le_rfl hNk)
        (intervalIntegrable_from_tail hc hNk hkk),
      ← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_from_tail hd le_rfl hNk)
        (intervalIntegrable_from_tail hd hNk hkk)]
    rw [ih, centeredAbel_integral_unit hs (n := N + k) (by omega), mul_add]

theorem centeredAbelTail_eq_second {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    (∫ u in Ioi (N : ℝ), centeredAbelKernel s u) =
      (s + 1) * ∫ u in Ioi (N : ℝ), secondAbelKernel s u := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : Tendsto (fun k : ℕ => ((N + k : ℕ) : ℝ)) atTop atTop := by
    simpa [Nat.add_comm, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat N)
  have hc := intervalIntegral_tendsto_integral_Ioi (N : ℝ)
    (centeredAbelKernel_integrable hs hNR) ht
  have hd := (intervalIntegral_tendsto_integral_Ioi (N : ℝ)
    (secondAbelKernel_integrable hs (zero_lt_one.trans_le hNR)) ht).const_mul (s + 1)
  have he :
      (fun k : ℕ => ∫ u in (N : ℝ)..(N + k : ℕ), centeredAbelKernel s u) =
        (fun k : ℕ => (s + 1) * ∫ u in (N : ℝ)..(N + k : ℕ), secondAbelKernel s u) :=
    funext (centeredAbel_integral_nat_interval hs hN)
  rw [← he] at hd
  exact tendsto_nhds_unique hc hd

theorem zeta_sub_abelApprox_second {s : ℂ} (hs : 1 / 10 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s - abelApprox s N =
      (-s * (s + 1)) * ∫ u in Ioi (N : ℝ), secondAbelKernel s u := by
  rw [zeta_sub_abelApprox hs hs1 hN, centeredAbelTail_eq_second (by linarith) hN, mul_assoc]

theorem norm_zeta_sub_abelApprox_second_le {s : ℂ} (hs : 1 / 10 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - abelApprox s N‖ ≤
      ‖s‖ * ‖s + 1‖ * (N : ℝ) ^ (-s.re - 1) / (8 * (s.re + 1)) := by
  rw [zeta_sub_abelApprox_second hs hs1 hN, norm_mul, norm_mul, norm_neg]
  have h := norm_secondAbelTail_le (s := s) (by linarith : 0 < s.re)
    (a := N) (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN))
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left h (mul_nonneg (norm_nonneg s) (norm_nonneg (s + 1)))

#print axioms centeredAbel_integral_unit
#print axioms zeta_sub_abelApprox_second
#print axioms norm_zeta_sub_abelApprox_second_le

end LiuWang.Proof.Campaign20260915.ZetaValidation
