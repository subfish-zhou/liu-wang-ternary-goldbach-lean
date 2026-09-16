import LiuWang.Proof.Campaign20260915.RosserCount.BacklundWeightKernel

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex Filter Metric MeasureTheory MeromorphicOn
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.ZetaWinding

private theorem right_flag_sum (T : ℝ) (n : ℕ) :
    (∑ z ∈ backlundDiskSupport T n, backlundRightFlag z) =
      ((backlundWindowSupport T n (1 / 2) (5 / 4)).card : ℝ) := by
  classical
  simp only [backlundWindowSupport,
    show (1 / 2 : ℝ) - 5 / 4 = -3 / 4 by norm_num, sub_self]
  exact Finset.sum_boole _ _

theorem backlund_window_kernel_sum (T : ℝ) (n : ℕ) (u : ℝ) :
    (∑ z ∈ backlundDiskSupport T n, (backlundRightKernel z u + backlundLeftKernel z u)) =
      ((backlundWindowSupport T n (1 / 2 + u) (5 / 4)).card +
        (backlundWindowSupport T n (1 / 2 - u) (1 / 2)).card : ℝ) *
          backlundReciprocalKernel u := by
  classical
  have hR (z : ℂ) :
      backlundRightKernel z u =
      if z.im = 0 ∧ z.re ∈ Set.Icc (1 / 2 + u - 5 / 4) (5 / 4 - 5 / 4) then
        backlundReciprocalKernel u else 0 := by
    have hm :
        (z.im = 0 ∧ z.re ∈ Set.Icc (1 / 2 + u - 5 / 4) (5 / 4 - 5 / 4)) ↔
        (z.im = 0 ∧ z.re ≤ 0) ∧ u ≤ z.re + 3 / 4 := by
      constructor
      · rintro ⟨hi, hl, hh⟩
        exact ⟨⟨hi, by linarith⟩, by linarith⟩
      · rintro ⟨⟨hi, hh⟩, hl⟩
        exact ⟨hi, by constructor <;> linarith⟩
    simp only [hm]
    by_cases hc : z.im = 0 ∧ z.re ≤ 0 <;>
      simp [backlundRightKernel, hc, Set.indicator]
  have hL (z : ℂ) :
      backlundLeftKernel z u =
      if z.im = 0 ∧ z.re ∈ Set.Icc (1 / 2 - u - 5 / 4) (1 / 2 - 5 / 4) then
        backlundReciprocalKernel u else 0 := by
    have hm :
        (z.im = 0 ∧ z.re ∈ Set.Icc (1 / 2 - u - 5 / 4) (1 / 2 - 5 / 4)) ↔
        (z.im = 0 ∧ z.re ≤ -3 / 4) ∧ -z.re - 3 / 4 ≤ u := by
      constructor
      · rintro ⟨hi, hl, hh⟩
        exact ⟨⟨hi, by linarith⟩, by linarith⟩
      · rintro ⟨⟨hi, hh⟩, hl⟩
        exact ⟨hi, by constructor <;> linarith⟩
    simp only [hm]
    by_cases hc : z.im = 0 ∧ z.re ≤ -3 / 4 <;>
      simp [backlundLeftKernel, hc, Set.indicator]
  simp_rw [Finset.sum_add_distrib, hR, hL]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, backlundWindowSupport]
  ring

theorem backlundAux_weighted_phase_divisor {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {n : ℕ} (hn : backlundAux T n 0 ≠ 0) :
    2 * Real.log (44 / 25 : ℝ) *
        ((n : ℝ) * |(backlundLog T (5 / 4)).im - (backlundLog T (1 / 2)).im|) ≤
      Real.pi * (∑ᶠ z,
        (divisor (backlundAux T n) (closedBall 0 (33 / 25 : ℝ)) z : ℝ) *
          Real.log ((33 / 25 : ℝ) * ‖z‖⁻¹)) +
      4 * Real.log (44 / 25 : ℝ) * Real.pi +
      Real.log (44 / 25 : ℝ) * (4 * (n : ℝ) / T) := by
  classical
  let q := Real.log (44 / 25 : ℝ)
  let V := (n : ℝ) * |(backlundLog T (5 / 4)).im - (backlundLog T (1 / 2)).im|
  let C := V - 2 * Real.pi - 4 * (n : ℝ) / T
  let g (u : ℝ) :=
    ∑ z ∈ backlundDiskSupport T n, (backlundRightKernel z u + backlundLeftKernel z u)
  have hq : 0 < q := Real.log_pos (by norm_num)
  have hk : IntervalIntegrable backlundReciprocalKernel volume 0 (57 / 100) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (by fun_prop)
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    dsimp [backlundReciprocalKernel]
    linarith [hu.1]
  have hki : (∫ u in (0 : ℝ)..57 / 100, backlundReciprocalKernel u) = q := by
    have he := intervalIntegral.integral_comp_add_left (fun u : ℝ => 1 / u)
      (a := 0) (b := 57 / 100) (3 / 4 : ℝ)
    have hh := he.trans (integral_one_div_of_pos (by norm_num) (by norm_num))
    convert! hh using 1
    norm_num [backlundReciprocalKernel, q]
  have hg : IntervalIntegrable g volume 0 (57 / 100) := by
    convert! (IntervalIntegrable.sum (backlundDiskSupport T n)
      (fun z _ => backlund_pair_kernels_integrable z)) using 1
    funext u
    simp only [g, Finset.sum_apply]
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) (57 / 100)) :
      C * backlundReciprocalKernel u ≤ Real.pi * g u := by
    have hv := backlund_reflected_window_count_bound hT hr hn hu
    have hc : C ≤ Real.pi *
        ((backlundWindowSupport T n (1 / 2 + u) (5 / 4)).card +
          (backlundWindowSupport T n (1 / 2 - u) (1 / 2)).card : ℝ) := by
      dsimp [C, V]
      nlinarith only [hv]
    have hkp : 0 ≤ backlundReciprocalKernel u := by
      unfold backlundReciprocalKernel
      have hu0 := hu.1
      positivity
    dsimp only [g]
    rw [backlund_window_kernel_sum]
    convert! mul_le_mul_of_nonneg_right hc hkp using 1
    ring
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 57 / 100)
    (hk.const_mul C) (hg.const_mul Real.pi) hpoint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hki] at hi
  have hgi : (∫ u in (0 : ℝ)..57 / 100, g u) =
      ∑ z ∈ backlundDiskSupport T n,
        ∫ u in (0 : ℝ)..57 / 100, backlundRightKernel z u + backlundLeftKernel z u :=
    intervalIntegral.integral_finsetSum
      (s := backlundDiskSupport T n) (fun z _ => backlund_pair_kernels_integrable z)
  rw [hgi] at hi
  have hbase := backlund_window_phase_variation hT hr hn
    (by norm_num : (-7 / 100 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4) le_rfl
  have hb := mul_le_mul_of_nonneg_left hbase hq.le
  have hw := backlund_weighted_window_integrals hT hn
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, right_flag_sum] at hw
  have hws := mul_le_mul_of_nonneg_left hw Real.pi_pos.le
  dsimp [C, V, q] at hi hb
  nlinarith only [hi, hb, hws]

theorem backlund_weighted_phase_envelope {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |(backlundLog T (5 / 4)).im - (backlundLog T (1 / 2)).im| ≤
      ((Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ))) * Real.pi + 2 / T := by
  obtain ⟨f, hf, hfn, hl⟩ := backlundAux_center_log_limit T
  let q := Real.log (44 / 25 : ℝ)
  let E := Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ)
  let V := |(backlundLog T (5 / 4)).im - (backlundLog T (1 / 2)).im|
  have hq : 0 < q := Real.log_pos (by norm_num)
  have hT0 : T ≠ 0 := by linarith [rsA_ge_thousand]
  have hinv : Tendsto (fun n => (1 : ℝ) / (f n : ℝ)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun n => (f n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hf
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hcast
  have ht := ((((tendsto_const_nhds (x := E)).sub hl).mul_const Real.pi).add
    (hinv.const_mul (4 * q * Real.pi))).add_const (4 * q / T)
  simp only [mul_zero, add_zero] at ht
  have hlim : 2 * q * V ≤
      (E - Real.log ‖riemannZeta (backlundCenterPoint T)‖) * Real.pi + 4 * q / T := by
    apply ge_of_tendsto ht
    filter_upwards [hf.eventually (eventually_ge_atTop 1)] with k hk
    have hp : (0 : ℝ) < f k := by exact_mod_cast (by omega : 0 < f k)
    have hv := backlundAux_weighted_phase_divisor hT hr (hfn k)
    have hj := backlundAux_circleAverage_le_envelope hT (hfn k)
    rw [backlundAux_jensen_formula hT (hfn k)] at hj
    have hb :
        2 * q * ((f k : ℝ) * V) ≤
          Real.pi * ((f k : ℝ) * E - Real.log ‖backlundAux T (f k) 0‖) +
            4 * q * Real.pi + q * (4 * (f k : ℝ) / T) := by
      have hh := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
      dsimp [q, V, E]
      nlinarith only [hv, hh]
    calc
      2 * q * V ≤
          (Real.pi * ((f k : ℝ) * E - Real.log ‖backlundAux T (f k) 0‖) +
            4 * q * Real.pi + q * (4 * (f k : ℝ) / T)) / (f k : ℝ) := by
        apply (le_div_iff₀ hp).mpr
        nlinarith only [hb]
      _ = _ := by field_simp
  calc
    V ≤ ((E - Real.log ‖riemannZeta (backlundCenterPoint T)‖) * Real.pi +
        4 * q / T) / (2 * q) := by
      apply (le_div_iff₀ (mul_pos (by norm_num) hq)).mpr
      nlinarith only [hlim]
    _ = _ := by
      change _ = (E - Real.log ‖riemannZeta (backlundCenterPoint T)‖) / (2 * q) *
        Real.pi + 2 / T
      field_simp
      ring

theorem positiveCount_centered_weighted_envelope_bound {T : ℝ} (hT : rsA ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0) :
    |Real.pi * ((positiveCount T : ℝ) - rosserMain T) -
      rosserGammaRemainder T - (backlundLog T (5 / 4)).im| ≤
      ((Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖) /
          (2 * Real.log (44 / 25 : ℝ))) * Real.pi + 2 / T := by
  have hpos : 0 < T := by linarith [rsA_ge_thousand]
  rw [positiveCount_error_backlundLog hpos hr]
  have he : rosserGammaRemainder T + (backlundLog T (1 / 2)).im -
      rosserGammaRemainder T - (backlundLog T (5 / 4)).im =
      (backlundLog T (1 / 2)).im - (backlundLog T (5 / 4)).im := by ring
  rw [he, abs_sub_comm]
  exact backlund_weighted_phase_envelope hT hr

#print axioms backlund_window_kernel_sum
#print axioms backlundAux_weighted_phase_divisor
#print axioms backlund_weighted_phase_envelope
#print axioms positiveCount_centered_weighted_envelope_bound

end LiuWang.Proof.Campaign20260915.RosserCount
