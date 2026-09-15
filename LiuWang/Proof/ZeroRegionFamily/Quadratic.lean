import LiuWang.Proof.ZeroRegionFamily.Nonquadratic

/-! # 二次字符非实零点：实际共轭对与高低高度的显式间距 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ZeroRegionFamily

theorem high_pair_scalar {L beta t : ℝ} (hL : 1 < L) (hb : beta < 1)
    (ht : 1/(10*L) ≤ |t|)
    (hcore : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      4/(sigma-beta) ≤ 3/(sigma-1) +
        (sigma-1)/((sigma-1)^2+4*t^2)+10*L) :
    1/(1280*L) ≤ 1-beta := by
  have hL0 : 0 < L := by linarith
  let u := 1/(80*L)
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hu : L*u=1/80 := by dsimp [u]; field_simp
  have htL : 1/10 ≤ L*|t| := by
    have hh := (div_le_iff₀ (show 0 < 10*L by positivity)).mp ht
    nlinarith
  have hsq : 1/100 ≤ L^2*t^2 := by
    have hh := sq_nonneg (L*|t|-1/10)
    have he : (L*|t|)^2=L^2*t^2 := by rw [mul_pow, sq_abs]
    nlinarith
  have hden : 0 < u^2+4*t^2 := by positivity
  have hpole : u/(u^2+4*t^2) ≤ L := by
    apply (div_le_iff₀ hden).mpr
    have hh : 0 ≤ L^2*u^2 := by positivity
    nlinarith
  have h := hcore (1+u) (by linarith) (by linarith)
  rw [show 1+u-1=u by ring] at h
  have hi : 3/u=240*L := by dsimp [u]; field_simp; ring
  rw [hi] at h
  have hbden : 0 < 1+u-beta := by linarith
  have hm := (div_le_iff₀ hbden).mp (show 4/(1+u-beta) ≤ 251*L by linarith)
  by_contra hg
  have hgap := (lt_div_iff₀ (show 0 < 1280*L by positivity)).mp (lt_of_not_ge hg)
  nlinarith

theorem primitive_quadratic_nonreal_gap {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    (hsq : chi^2 = 1) {rho : ℂ} (hrho : 0 < rho.re)
    (hz : chi.LFunction rho = 0) (hnreal : rho.im ≠ 0) :
    1/(1280*(Real.log q+Real.log (|rho.im|+2))) ≤ 1-rho.re := by
  obtain ⟨p, hp⟩ := exists_completedZeroIndex_of_LFunction_eq_zero hchi hprim hrho hz
  have hstrip := symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hchi hprim p
  rw [hp] at hstrip
  have hlog := log_level_gt_one
    (BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi)
  have hht : 0 ≤ Real.log (|rho.im|+2) := Real.log_nonneg (by linarith [abs_nonneg rho.im])
  by_cases ht : |rho.im| < 1/(10*(Real.log q+Real.log (|rho.im|+2)))
  · obtain ⟨r, hr⟩ := exists_quadratic_conjugateZeroIndex hchi hprim hsq p
    have hne : p ≠ r := by
      intro he
      have hh := congrArg Complex.im hr
      rw [← he, hp, Complex.conj_im] at hh
      exact hnreal (by linarith)
    have hlow := nonreal_core_inequality_implies_lowHeight_gap hstrip.2
      (abs_pos.mpr hnreal) (by linarith : 0 < Real.log q) hlog.le
      (show |rho.im| < (10*Real.log q)⁻¹ by
        apply ht.trans_le
        simpa only [one_div] using one_div_le_one_div_of_le
          (show 0 < 10*Real.log q by positivity) (by linarith)) (fun sigma hs hs2 => ?_)
    · apply le_trans _ hlow
      rw [← one_div (15*Real.log q)]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    · have hh := two_real_kernel_le hchi hprim p r hne hs hs2
      rw [hr, hp, conjugatePairKernel_re] at hh
      simpa only [sq_abs, one_div] using hh.trans
        (show 1/(sigma-1)+Real.log q/2 ≤ 1/(sigma-1)+Real.log q by linarith)
  · apply high_pair_scalar (by linarith) hstrip.2 (le_of_not_gt ht)
    intro sigma hs hs2
    have hpos := logDerivative_combination_nonneg chi hs rho.im
    rw [hsq] at hpos
    have hmain := primitive_selected_kernel_le hchi hprim p
      (s := (sigma : ℂ)+I*(rho.im : ℂ)) (by simpa using hs) (by simpa using hs2)
    have hthird := principal_complex_le_pole (q := q)
      (s := (sigma : ℂ)+2*I*(rho.im : ℂ)) (by simpa using hs) (by simpa using hs2)
    have hprincipal := principal_real_le_pole (q := q) hs hs2
    have hk := zeroKernel_re_of_same_im (s := (sigma : ℂ)+I*(rho.im : ℂ)) (rho := rho)
      (by simpa using ne_of_gt (hstrip.2.trans hs)) (by simp)
    rw [hp, one_div, hk] at hmain
    have hpole : (1/((sigma : ℂ)+2*I*(rho.im : ℂ)-1)).re =
        (sigma-1)/((sigma-1)^2+4*rho.im^2) := by
      rw [one_div, Complex.inv_re, Complex.normSq_apply]
      norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.sub_im,
        Complex.add_im, Complex.mul_im]
      ring
    rw [hpole] at hthird
    simp only [neg_div, Complex.neg_re, ← logDeriv_apply] at hpos
    have hdouble := doubled_log_le rho.im
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hdouble
    norm_num [Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re] at hmain hthird
    simp only [div_eq_mul_inv] at hprincipal hmain hthird ⊢
    linarith

theorem quadratic_nonreal_gap {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hsq : chi^2 = 1)
    {rho : ℂ} (hrho : 0 < rho.re) (hz : chi.LFunction rho = 0) (hnreal : rho.im ≠ 0) :
    1/(1280*(Real.log chi.conductor+Real.log (|rho.im|+2))) ≤ 1-rho.re := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact primitive_quadratic_nonreal_gap
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi)
    chi.primitiveCharacter_isPrimitive
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_pow_eq_one_of_pow_eq_one chi hsq)
    hrho (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hchi hrho hz) hnreal

end LiuWang.Proof.ZeroRegionFamily
