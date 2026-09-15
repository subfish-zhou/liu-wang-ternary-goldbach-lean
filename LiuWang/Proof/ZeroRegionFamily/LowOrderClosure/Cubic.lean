import LiuWang.Proof.ZeroRegionFamily.LowOrderClosure.Pole

/-! # 三阶字符的ζ+2Re L实轴正性与单个实际零核 -/

set_option autoImplicit false
noncomputable section

open Complex
open ArithmeticFunction hiding log
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily.RealClosure

namespace LiuWang.Proof.ZeroRegionFamily.LowOrderClosure

theorem cubic_unit_re_nonneg {z : ℂ} (h : z^3=1) : 0 ≤ 1+2*z.re := by
  have he : (z-1)*(z^2+z+1)=0 := by calc
    _ = z^3-1 := by ring
    _ = 0 := by rw [h]; ring
  rcases mul_eq_zero.mp he with he | he
  · have hz : z=1 := sub_eq_zero.mp he
    norm_num [hz]
  · have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    norm_num [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] at hr hi
    by_cases him : z.im=0
    · rw [him] at hr
      nlinarith [sq_nonneg (z.re+1/2)]
    · have he : z.im*(2*z.re+1)=0 := by nlinarith only [hi]
      have hh := (mul_eq_zero.mp he).resolve_left him
      linarith

theorem cubic_euler_nonneg {q : ℕ} (chi : DirichletCharacter ℂ q) (h3 : chi^3=1) (n : ℕ) :
    0 ≤ 1+2*(chi n).re := by
  by_cases hu : IsUnit (n : ZMod q)
  · have hh := congrArg (fun c : DirichletCharacter ℂ q => c n) h3
    rw [chi.pow_apply' (by norm_num : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hh
    exact cubic_unit_re_nonneg hh
  · simp [MulChar.map_nonunit chi hu]

theorem cubic_term_nonneg {q : ℕ} (chi : DirichletCharacter ℂ q) (h3 : chi^3=1)
    (sigma : ℝ) (n : ℕ) :
    0 ≤ harmonicTerm (1 : DirichletCharacter ℂ 1) sigma 0 1 n+
      2*harmonicTerm chi sigma 0 1 n := by
  by_cases hn : n=0
  · simp [hn, harmonicTerm]
  have ha : (((Λ n : ℝ)/(n : ℝ)^sigma : ℝ) : ℂ) =
      (Λ n : ℂ)/(n : ℂ)^(sigma : ℂ) := by
    rw [ofReal_div, ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast]
  have hterm (z : ℂ) : z*(Λ n : ℂ)/(n : ℂ)^(sigma : ℂ) =
      z*((Λ n : ℝ)/(n : ℝ)^sigma : ℝ) := by rw [ha]; ring
  simp only [harmonicTerm, pow_one, mul_zero, Complex.ofReal_zero, add_zero,
    LSeries.term, if_neg hn, Pi.mul_apply, DirichletCharacter.modOne_eq_one, Pi.one_apply, one_mul]
  rw [← ha, hterm]
  have hh := mul_nonneg (cubic_euler_nonneg chi h3 n)
    (div_nonneg (show 0 ≤ Λ n from vonMangoldt_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg n) sigma))
  simpa only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero,
    add_mul, one_mul, mul_assoc] using hh

theorem cubic_actual_real_nonneg {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (h3 : chi^3=1) {sigma : ℝ} (hs : 1 < sigma) :
    0 ≤ -(logDeriv riemannZeta (sigma : ℂ)).re-2*(logDeriv chi.LFunction (sigma : ℂ)).re := by
  have hsum := (harmonicTerm_hasSum (1 : DirichletCharacter ℂ 1) hs 0 1).add
    ((harmonicTerm_hasSum chi hs 0 1).mul_left 2)
  have hh : 0 ≤ ∑' n, (harmonicTerm (1 : DirichletCharacter ℂ 1) sigma 0 1 n+
      2*harmonicTerm chi sigma 0 1 n) := tsum_nonneg (cubic_term_nonneg chi h3 sigma)
  rw [hsum.tsum_eq] at hh
  simpa only [pow_one, mul_zero, Complex.ofReal_zero, add_zero,
    DirichletCharacter.LFunction_modOne_eq, Complex.neg_re, sub_eq_add_neg, mul_neg] using hh

theorem cubic_real_axis_single {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (h3 : chi^3=1)
    {rho : ℂ} (hr : 0 < rho.re) (hz : chi.LFunction rho=0)
    {sigma : ℝ} (hs : 1 < sigma) (hs2 : sigma ≤ 2) :
    2*(sigma-rho.re)/((sigma-rho.re)^2+rho.im^2) ≤ 1/(sigma-1)+Real.log q := by
  obtain ⟨p, hv⟩ := exists_completedZeroIndex_of_LFunction_eq_zero hc hp hr hz
  have hid := primitive_kernel_identity hc hp (s := (sigma : ℂ)) (by simpa)
  have hsum := summable_symmetricCompletedLFunction_zeroKernel_re hc hp
    (s := (sigma : ℂ)) (by simpa)
  have hh := hsum.le_tsum p (fun r _ => zero_kernel_nonneg hc hp (by simpa using hs) r)
  rw [hv] at hh
  have he : (1/((sigma : ℂ)-rho)).re =
      (sigma-rho.re)/((sigma-rho.re)^2+rho.im^2) := by
    simp [one_div, Complex.inv_re, Complex.normSq_apply, pow_two]
  rw [he] at hh
  have hg := gamma_real_nonpos chi hs hs2
  have hpos := cubic_actual_real_nonneg chi h3 hs
  have hzet := ChebyshevBound.HighHeight.zeta_real_le_pole hs hs2
  simp only [neg_div, Complex.neg_re, ← logDeriv_apply] at hzet
  simp only [div_eq_mul_inv, one_mul] at hid hh hzet ⊢
  linarith

end LiuWang.Proof.ZeroRegionFamily.LowOrderClosure
