import LiuWang.Proof.SourceRoute.MajorOrdinary.SourceSums
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SumIntegralComparisons

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

def nu (x : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x) +
    2.50637 / Real.log (Real.log x)

def nuKernel (s x : ℝ) : ℝ := x ^ (s - 2) * nu x ^ 2

theorem exp_gamma_ge_one : 1 ≤ Real.exp Real.eulerMascheroniConstant :=
  Real.one_le_exp (by linarith [Real.one_half_lt_eulerMascheroniConstant])

theorem log_hundred_thousand_ge_ten : (10 : ℝ) ≤ Real.log 100000 := by
  apply (Real.le_log_iff_exp_le (by norm_num)).mpr
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le
    (show Real.exp 1 ≤ 3 by linarith [Real.exp_one_lt_d9]) 10
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  linarith

theorem log_ten_ge_two : (2 : ℝ) ≤ Real.log 10 := by
  apply (Real.le_log_iff_exp_le (by norm_num)).mpr
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le
    (show Real.exp 1 ≤ 3 by linarith [Real.exp_one_lt_d9]) 2
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  linarith

theorem large_log_bounds {x : ℝ} (hx : 100000 ≤ x) :
    10 ≤ Real.log x ∧ 2 ≤ Real.log (Real.log x) := by
  have hl := log_hundred_thousand_ge_ten.trans (Real.log_le_log (by norm_num) hx)
  exact ⟨hl, log_ten_ge_two.trans (Real.log_le_log (by norm_num) hl)⟩

theorem nu_pos {x : ℝ} (hx : 100000 ≤ x) : 0 < nu x := by
  have hu : 0 < Real.log (Real.log x) := by linarith [(large_log_bounds hx).2]
  unfold nu
  positivity

theorem nu_continuousOn : ContinuousOn nu (Ici 100000) := by
  intro x hx
  change 100000 ≤ x at hx
  have hl := large_log_bounds hx
  have hx0 : x ≠ 0 := by linarith
  have ht0 : Real.log x ≠ 0 := by linarith [hl.1]
  have hu0 : Real.log (Real.log x) ≠ 0 := by linarith [hl.2]
  exact ((continuousAt_const.mul ((Real.continuousAt_log ht0).comp
    (Real.continuousAt_log hx0))).add (continuousAt_const.div
      ((Real.continuousAt_log ht0).comp (Real.continuousAt_log hx0)) hu0)).continuousWithinAt

theorem nu_monotoneOn : MonotoneOn nu (Ici 100000) := by
  intro x hx y hy hxy
  change 100000 ≤ x at hx
  change 100000 ≤ y at hy
  have hxL := large_log_bounds hx
  have hyL := large_log_bounds hy
  have hlog := Real.log_le_log (by linarith : 0 < x) hxy
  have huv := Real.log_le_log (by linarith : 0 < Real.log x) hlog
  have hu : 0 < Real.log (Real.log x) := by linarith [hxL.2]
  have hv : 0 < Real.log (Real.log y) := by linarith [hyL.2]
  have hprod : 2.50637 ≤ Real.exp Real.eulerMascheroniConstant *
      (Real.log (Real.log x) * Real.log (Real.log y)) := by
    have h := mul_le_mul_of_nonneg_left exp_gamma_ge_one (mul_nonneg hu.le hv.le)
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.log (Real.log x) - 2)
      (by linarith : 0 ≤ Real.log (Real.log y) - 2)]
  have hdiff := mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hprod)
  unfold nu
  apply (mul_le_mul_iff_left₀ (mul_pos hu hv)).mp
  field_simp
  nlinarith [hdiff]

theorem nu_ratio_le_loglog_ratio {x y : ℝ} (hx : 100000 ≤ x) (hxy : x ≤ y) :
    nu y ≤ nu x * (Real.log (Real.log y) / Real.log (Real.log x)) := by
  have hl := large_log_bounds hx
  have hu : 0 < Real.log (Real.log x) := by linarith [hl.2]
  have huv := Real.log_le_log (by linarith : 0 < Real.log x)
    (Real.log_le_log (by linarith : 0 < x) hxy)
  have hv : 0 < Real.log (Real.log y) := hu.trans_le huv
  have hs := sq_le_sq₀ hu.le hv.le |>.mpr huv
  unfold nu
  apply (mul_le_mul_iff_left₀ (mul_pos (pow_pos hu 2) hv)).mp
  field_simp
  nlinarith

theorem nu_growth {x y a : ℝ} (hx : 100000 ≤ x) (hxy : x ≤ y)
    (ha : 1 ≤ a * Real.log x * Real.log (Real.log x)) :
    nu y ≤ nu x * (y / x) ^ a := by
  have hl := large_log_bounds hx
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have ht : 0 < Real.log x := by linarith [hl.1]
  have hu : 0 < Real.log (Real.log x) := by linarith [hl.2]
  have hz : 0 ≤ Real.log (y / x) := Real.log_nonneg ((le_div_iff₀ hx0).mpr (by simpa))
  have h1 := Real.log_le_sub_one_of_pos
    (div_pos (Real.log_pos (by linarith : 1 < y)) ht)
  rw [Real.log_div (Real.log_pos (by linarith : 1 < y)).ne' ht.ne'] at h1
  have hlog := Real.log_div hy0.ne' hx0.ne'
  have hstep : Real.log (Real.log y) ≤ Real.log (Real.log x) +
      Real.log (y / x) / Real.log x := by
    rw [hlog, sub_div, div_self ht.ne']
    linarith
  have h3 : Real.log (y / x) / Real.log x ≤
      a * Real.log (Real.log x) * Real.log (y / x) := by
    apply (div_le_iff₀ ht).mpr
    nlinarith [mul_le_mul_of_nonneg_right ha hz]
  have hratio : Real.log (Real.log y) / Real.log (Real.log x) ≤
      1 + a * Real.log (y / x) := by
    apply (div_le_iff₀ hu).mpr
    nlinarith
  calc
    nu y ≤ nu x * (Real.log (Real.log y) / Real.log (Real.log x)) :=
      nu_ratio_le_loglog_ratio hx hxy
    _ ≤ nu x * (1 + a * Real.log (y / x)) :=
      mul_le_mul_of_nonneg_left hratio (nu_pos hx).le
    _ ≤ nu x * Real.exp (a * Real.log (y / x)) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (a * Real.log (y / x))])
        (nu_pos hx).le
    _ = _ := by rw [Real.rpow_def_of_pos (div_pos hy0 hx0)]; congr 2; ring

theorem nuKernel_nonneg {x : ℝ} (hx : 0 ≤ x) (s : ℝ) : 0 ≤ nuKernel s x := by
  unfold nuKernel
  positivity

theorem nuKernel_continuousOn (s : ℝ) : ContinuousOn (nuKernel s) (Ici 100000) := by
  apply ContinuousOn.mul _ (nu_continuousOn.pow 2)
  intro x hx
  change 100000 ≤ x at hx
  exact (Real.continuousAt_rpow_const x (s - 2) (Or.inl (by linarith))).continuousWithinAt

theorem nuKernel_antitoneOn {s : ℝ} (hs : s ≤ 7 / 6) :
    AntitoneOn (nuKernel s) (Ici 100000) := by
  intro x hx y _ hxy
  change 100000 ≤ x at hx
  have hx0 : 0 < x := by linarith [hx]
  have hy0 : 0 < y := hx0.trans_le hxy
  have hl := large_log_bounds hx
  have hg := nu_growth (a := 1 / 4) hx hxy (by
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.log x - 10)
      (by linarith : 0 ≤ Real.log (Real.log x) - 2)])
  have hpow : nu y ^ 2 ≤ nu x ^ 2 * (y / x) ^ (1 / 2 : ℝ) := by
    have h := pow_le_pow_left₀ (nu_pos (hx.trans hxy)).le hg 2
    have he : ((y / x) ^ (1 / 4 : ℝ)) ^ 2 = (y / x) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hy0 hx0).le]
      norm_num
    simpa only [mul_pow, he] using h
  have he : y ^ (s - 2) * (y / x) ^ (1 / 2 : ℝ) ≤ x ^ (s - 2) := by
    rw [Real.div_rpow hy0.le hx0.le]
    rw [← mul_div_assoc, ← Real.rpow_add hy0]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)).mpr
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  unfold nuKernel
  calc
    _ ≤ y ^ (s - 2) * (nu x ^ 2 * (y / x) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hy0.le _)
    _ = (y ^ (s - 2) * (y / x) ^ (1 / 2 : ℝ)) * nu x ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right he (sq_nonneg _)

theorem sourceP_ge_ten_billion {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    10000000000 ≤ sourceP N := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) (sourceL_ge_3100 hN) 3
  change 10000000000 ≤ sourceL N ^ 3
  norm_num at h
  linarith

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
