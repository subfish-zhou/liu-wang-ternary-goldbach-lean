import LiuWang.Proof.SourceRoute.MajorException.CubicIntegral

set_option autoImplicit false
noncomputable section

open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.SingularIntegral
open LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException

theorem scaled_young_cubic {x y k : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hk : 0 < k) :
    x^2 * y ≤ (2*k*x^3 + y^3/k^2)/3 := by
  have h := mul_nonneg (sq_nonneg (k*x-y)) (by positivity : 0 ≤ 2*k*x+y)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hk)).mp
  field_simp
  nlinarith

theorem finite_double_single_young {N : ℕ} (hN : 0 < N) (rho tau : ℂ)
    {delta k : ℝ} (hd : 0 ≤ delta) (hk : 0 < k) :
    ‖finiteMoment N delta rho rho tau‖ ≤
      (2*k*(∫ eta in -delta..delta, ‖Jrho N rho eta‖^3) +
        (∫ eta in -delta..delta, ‖Jrho N tau eta‖^3)/k^2)/3 := by
  have hr : IntervalIntegrable (fun eta => ‖Jrho N rho eta‖^3) volume (-delta) delta :=
    ((Jrho_continuous hN rho).norm.pow 3).intervalIntegrable _ _
  have ht : IntervalIntegrable (fun eta => ‖Jrho N tau eta‖^3) volume (-delta) delta :=
    ((Jrho_continuous hN tau).norm.pow 3).intervalIntegrable _ _
  have hkernel := (tripleKernel_integrable hN rho rho tau).norm.intervalIntegrable
    (a := -delta) (b := delta)
  have hmono := intervalIntegral.integral_mono_on (by linarith : -delta ≤ delta)
    hkernel ((hr.const_mul (2*k)).add (ht.div_const (k^2)) |>.div_const 3)
    (fun eta _ => by
      simp only [tripleKernel, norm_mul, charReal_norm, one_mul]
      simpa only [pow_two] using scaled_young_cubic
        (norm_nonneg (Jrho N rho eta)) (norm_nonneg (Jrho N tau eta)) hk)
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := tripleKernel N rho rho tau) (by linarith : -delta ≤ delta)
  apply hnorm.trans (hmono.trans_eq ?_)
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (hr.const_mul (2*k)) (ht.div_const (k^2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div]

theorem source_cubic_scaling {N : ℕ} (hN : 0 < N) (beta : ℝ) :
    (N : ℝ)^(3*beta-1) = (N : ℝ)^2 * baseWeight N beta^3 := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [baseWeight, ← Real.rpow_mul_natCast hn.le, ← Real.rpow_natCast (N : ℝ) 2,
    ← Real.rpow_add hn]
  congr 1
  norm_num
  ring

theorem Jrho_cubic_source_scaled {N : ℕ} (hN : 0 < N) {beta delta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) (hd : 0 ≤ delta) :
    (∫ eta in -delta..delta, ‖Jrho N (beta : ℂ) eta‖^3) ≤
      (3*1.0302*1.0033^2/Real.pi) * (N : ℝ)^2 * baseWeight N beta^3 := by
  simpa only [source_cubic_scaling hN, mul_assoc] using Jrho_cubic_source hN hb hb1 hd

theorem source_linear_holder_constant :
    (2*(1.013 : ℝ)*2.994006 + (3*1.0302*1.0033^2)/(1.013^2)) /
      (3*Real.pi) ≤ 0.9653 := by
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [Real.pi_gt_d6]

theorem source_quadratic_holder_constant :
    (2/(1.013 : ℝ)*(3*1.0302*1.0033^2) + 2.994006*1.013^2) /
      Real.pi * 2.82682 ≤ 8.2914 := by
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_gt_d6]

theorem finite_linear_source {N : ℕ} (hN : 0 < N) {beta delta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) (hd : 0 ≤ delta) :
    ‖finiteMoment N delta 1 1 beta‖ ≤
      0.9653 * (N : ℝ)^2 * baseWeight N beta := by
  have hv : 0 < baseWeight N beta := by
    unfold baseWeight
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _
  have h := finite_double_single_young hN 1 beta hd
    (show 0 < 1.013*baseWeight N beta by positivity)
  have hJ := J_cubic_source hN hd
  have hbeta := Jrho_cubic_source_scaled hN hb hb1 hd
  simp only [Jrho_one_eq_J] at h
  apply h.trans
  calc
    _ ≤ (2*(1.013*baseWeight N beta)*
          ((2.994006/Real.pi)*(N : ℝ)^2) +
        ((3*1.0302*1.0033^2/Real.pi)*(N : ℝ)^2*baseWeight N beta^3) /
          (1.013*baseWeight N beta)^2)/3 := by gcongr
    _ = ((2*(1.013 : ℝ)*2.994006 + (3*1.0302*1.0033^2)/(1.013^2)) /
          (3*Real.pi)) * ((N : ℝ)^2*baseWeight N beta) := by
      field_simp
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        source_linear_holder_constant (by positivity : 0 ≤ (N : ℝ)^2*baseWeight N beta)

def quadraticHolderConstant : ℝ :=
  (2/(1.013 : ℝ)*(3*1.0302*1.0033^2) + 2.994006*1.013^2) / (3*Real.pi)

theorem finite_quadratic_source {N : ℕ} (hN : 0 < N) {beta delta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) (hd : 0 ≤ delta) :
    ‖finiteMoment N delta 1 beta beta‖ ≤
      quadraticHolderConstant * (N : ℝ)^2 * baseWeight N beta^2 := by
  have hv : 0 < baseWeight N beta := by
    unfold baseWeight
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _
  have h := finite_double_single_young hN beta 1 hd
    (show 0 < 1/(1.013*baseWeight N beta) by positivity)
  have hJ := J_cubic_source hN hd
  have hbeta := Jrho_cubic_source_scaled hN hb hb1 hd
  have he : finiteMoment N delta 1 beta beta = finiteMoment N delta beta beta 1 := by
    unfold finiteMoment
    congr 1
    ext eta
    unfold tripleKernel
    ring
  rw [he]
  simp only [Jrho_one_eq_J] at h
  apply h.trans
  calc
    _ ≤ (2*(1/(1.013*baseWeight N beta))*
          ((3*1.0302*1.0033^2/Real.pi)*(N : ℝ)^2*baseWeight N beta^3) +
        ((2.994006/Real.pi)*(N : ℝ)^2) /
          (1/(1.013*baseWeight N beta))^2)/3 := by gcongr
    _ = _ := by
      unfold quadraticHolderConstant
      field_simp

theorem finite_cubic_source {N : ℕ} (hN : 0 < N) {beta delta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) (hd : 0 ≤ delta) :
    ‖finiteMoment N delta beta beta beta‖ ≤
      (3*1.0302*1.0033^2/Real.pi) * (N : ℝ)^2 * baseWeight N beta^3 := by
  have h := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := tripleKernel N beta beta beta) (by linarith : -delta ≤ delta)
  simp only [norm_triple_repeated] at h
  exact h.trans (Jrho_cubic_source_scaled hN hb hb1 hd)

end LiuWang.Proof.SourceRoute.MajorException
