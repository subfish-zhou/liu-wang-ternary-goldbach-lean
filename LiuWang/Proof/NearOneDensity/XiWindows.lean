import LiuWang.Proof.NearOneDensity.NonprincipalWindows
import LiuWang.Proof.PrincipalPsi.Quantitative.XiBridge

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate
open Classical Complex BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.NearOneDensity

theorem xi_finite_reflected_sum_le (s : Finset RiemannXiDivisorZeroIndex)
    (hr : ∀ p ∈ s, 1 / 2 < (riemannXiDivisorZeroValue p).re)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (∑ p ∈ s, (dampedZeroKernel σ t (riemannXiDivisorZeroValue p) +
      dampedZeroKernel σ t (1 - conj (riemannXiDivisorZeroValue p)))) ≤ zetaZeroSum σ t := by
  have h0 : 1 ≤ ((σ : ℂ) + I * t).re := by simpa [Complex.mul_re] using hσ.le
  have h1 : 1 ≤ ((stechkinSigma σ : ℂ) + I * t).re := by
    simpa [Complex.mul_re] using (hσ.trans_le (stechkinSigma_ge hσ)).le
  have hs := (xi_raw_summable h0).sub ((xi_raw_summable h1).mul_left stechkinK)
  have hd : Disjoint s (s.image xiReflection) := by
    apply Finset.disjoint_left.mpr
    intro p hps hpi
    obtain ⟨j, hjs, rfl⟩ := Finset.mem_image.mp hpi
    have hj := hr j hjs
    have hh := hr (xiReflection j) hps
    change 1 / 2 < (1 - conj (riemannXiDivisorZeroValue j)).re at hh
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hh
    linarith
  exact finite_reflected_sum_le s xiReflection xiReflect_involutive
    (fun p => dampedZeroKernel σ t (riemannXiDivisorZeroValue p)) hs
    (fun p => dampedZeroKernel_pair_nonneg hσ t
      ⟨(riemannXiDivisorZeroValue_re_mem_Ioo p).1.le,
        (riemannXiDivisorZeroValue_re_mem_Ioo p).2.le⟩) hd

theorem poleDifference_window_nonpos {σ t : ℝ} (hσ : 1 < σ)
    (hσ₁ : σ ≤ 23 / 20) (ht : 9 / 10 ≤ |t|) : poleDifference σ t ≤ 0 := by
  have hb := stechkinSigma_bounds hσ hσ₁
  have hu : 0 < σ - 1 := by linarith
  have hv : 0 < stechkinSigma σ - 1 := by linarith [hb.1]
  have ht2 : 81 / 100 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hkv : 33 / 125 ≤ stechkinK * (stechkinSigma σ - 1) := by
    have hh := mul_le_mul stechkinK_ge
      (show 3 / 5 ≤ stechkinSigma σ - 1 by linarith [hb.1]) (by norm_num) stechkinK_mem.1
    norm_num at hh
    exact hh
  have hvsq : (stechkinSigma σ - 1) ^ 2 ≤ (19 / 25 : ℝ) ^ 2 := by
    nlinarith [hb.1, hb.2]
  have hprod := mul_le_mul (show σ - 1 ≤ 3 / 20 by linarith) hvsq
    (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 20)
  have hY := mul_le_mul_of_nonneg_right (show σ - 1 ≤ 3 / 20 by linarith) (sq_nonneg t)
  have hbig := mul_le_mul_of_nonneg_right hkv (sq_nonneg t)
  have hpos : 0 ≤ stechkinK * (stechkinSigma σ - 1) * (σ - 1) ^ 2 := by positivity
  simp only [poleDifference, one_div, Complex.inv_re, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, one_mul, sub_zero, add_zero, zero_add]
  apply sub_nonpos.mpr
  rw [← mul_div_assoc, div_le_div_iff₀
    (by nlinarith [sq_nonneg (σ - 1)])
    (by nlinarith [sq_nonneg (stechkinSigma σ - 1)])]
  nlinarith

theorem xi_window_mass_budget (s : Finset RiemannXiDivisorZeroIndex)
    (hr : ∀ p ∈ s, 1 / 2 < (riemannXiDivisorZeroValue p).re)
    {a L t : ℝ} (hL : 25 ≤ L) (ha : 0 < a) (haL : a / L ≤ 3 / 20)
    (ht : 9 / 10 ≤ |t|) (hheight : Real.log (max 1 |t|) ≤ L + 1 / 10) :
    (∑ p ∈ s, (dampedZeroKernel (1 + a / L) t (riemannXiDivisorZeroValue p) +
      dampedZeroKernel (1 + a / L) t (1 - conj (riemannXiDivisorZeroValue p)))) ≤
        L * (1 / a + 277 / 1000) := by
  have hL0 : 0 < L := by linarith
  have hσ : 1 < 1 + a / L := by linarith [div_pos ha hL0]
  have hσ₁ : 1 + a / L ≤ 23 / 20 := by linarith
  have hsum := xi_finite_reflected_sum_le s hr hσ t
  have hid := zeta_full_zero_sum_identity hσ t
  have hg := shiftedGamma_all_height hσ hσ₁ t
  have hp := poleDifference_window_nonpos hσ hσ₁ ht
  have hm := (logKernel_bounds_by_mass (1 : DirichletCharacter ℂ 1) t hσ
    (hσ.trans_le (stechkinSigma_ge hσ)) (stechkinSigma_ge hσ) stechkinK_mem.2).1
  rw [logKernel_eq_dampedLogDeriv, damped_mass_eq_zetaDamped hσ] at hm
  simp only [dampedLogDeriv, DirichletCharacter.LFunction_modOne_eq] at hm
  change -zetaDamped (1 + a / L) 0 ≤ zetaDamped (1 + a / L) t at hm
  have hreal := zeta_real_strong hσ hσ₁
  have he : 1 / (1 + a / L - 1) = L * (1 / a) := by
    field_simp [hL0.ne', ha.ne']
    ring
  rw [he] at hreal
  have hk : 0 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_mem.2]
  have hk' : stechkinConductorCoeff ≤ 277 / 1000 := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_ge_447]
  have hh := mul_le_mul_of_nonneg_left
    (show Real.log (max 1 |t|) - Real.log Real.pi ≤ L by linarith [log_pi_ge_one]) hk
  have hh' := mul_le_mul_of_nonneg_right hk' hL0.le
  linarith [stechkinK_mem.1]

theorem xi_row_window_count (r : DensityRow) (s : Finset RiemannXiDivisorZeroIndex)
    {L lam t : ℝ} (hL : 25 ≤ L) (hlam : 0 ≤ lam) (hlam₁ : lam ≤ rowLambda r)
    (hheight : Real.log (max 1 |t|) ≤ L + 1 / 10)
    (hre : ∀ p ∈ s, 1 - lam / L ≤ (riemannXiDivisorZeroValue p).re)
    (ht : ∀ p ∈ s, |t - (riemannXiDivisorZeroValue p).im| ≤ rowRadius r / L) :
    s.card ≤ rowMultiplicity r := by
  by_cases he : s = ∅
  · simp [he]
  obtain ⟨p, hps⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hc := row_window_certificate r
  have hL0 : 0 < L := by linarith
  have hsmall : rowRadius r / L ≤ 1 / 10 :=
    (div_le_iff₀ hL0).mpr (by linarith [hc.2.2.2.1])
  have ht0 : 9 / 10 ≤ |t| := by
    have hh := abs_add_le t ((riemannXiDivisorZeroValue p).im - t)
    rw [add_sub_cancel] at hh
    have hh' := ht p hps
    rw [abs_sub_comm] at hh'
    linarith [xi_zero_height_gt_one p]
  have hmax : rowLambda r ≤ 1 / 2 := by cases r <;> norm_num [rowLambda]
  have hr (p) (hps : p ∈ s) : 1 / 2 < (riemannXiDivisorZeroValue p).re := by
    have hh : lam / L < 1 / 2 := (div_lt_iff₀ hL0).mpr (by linarith)
    linarith [hre p hps]
  exact row_window_count_of_pair_budget r s riemannXiDivisorZeroValue hL hlam hlam₁ hre
    (fun p _ => (riemannXiDivisorZeroValue_re_mem_Ioo p).2.le) ht
    (xi_window_mass_budget s hr hL hc.1
      ((div_le_iff₀ hL0).mpr (by linarith [hc.2.1])) ht0 hheight)

end LiuWang.Proof.NearOneDensity
