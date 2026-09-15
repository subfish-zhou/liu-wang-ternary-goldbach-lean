import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.GammaBounds

/-!
# 左线与反射右线的显式伽马界

保留 digamma 主对数系数一：有限调和和与有限倒数和分别估计，
不对裸零点倒数级数取绝对值。低虚部由正实部控制，包含虚部零。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.LocalAnalyticBounds.LeftVertical

theorem norm_digamma_le_log_add_fourteen {z : Complex}
    (hlo : (1 : Real) / 4 ≤ z.re) (hhi : z.re ≤ 2) :
    ‖Complex.digamma z‖ ≤ Real.log (|z.im| + 2) + 14 := by
  let M : Nat := ⌈|z.im|⌉₊ + 1
  have hM : 1 ≤ M := Nat.le_add_left 1 _
  have hMpos : (0 : Real) < M := by exact_mod_cast (by omega : 0 < M)
  have hMlo : |z.im| + 1 ≤ (M : Real) := by
    dsimp [M]
    push_cast
    linarith [Nat.le_ceil |z.im|]
  have hMhi : (M : Real) ≤ |z.im| + 2 := by
    dsimp [M]
    push_cast
    linarith [Nat.ceil_lt_add_one (abs_nonneg z.im)]
  have hz : ‖z - 1‖ ≤ (M : Real) := by
    have he := Complex.norm_le_abs_re_add_abs_im (z - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero] at he
    have hr : |z.re - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have herr : ‖Complex.digamma z - digammaApprox z M‖ ≤ 4 := by
    refine (norm_digamma_sub_approx_le (by norm_num : (0 : Real) < 1 / 4)
      (by norm_num) hlo hM).trans ?_
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hinv : ∑ n ∈ Finset.range M, ‖(z + n)⁻¹‖ ≤ (8 : Real) := by
    by_cases him : 1 ≤ |z.im|
    · have him0 : 0 < |z.im| := by linarith
      calc
        _ ≤ ∑ _n ∈ Finset.range M, |z.im|⁻¹ := by
          apply Finset.sum_le_sum
          intro n _
          rw [norm_inv]
          apply inv_anti₀ him0
          simpa using Complex.abs_im_le_norm (z + n)
        _ = (M : Real) / |z.im| := by simp [div_eq_mul_inv]
        _ ≤ 3 := (div_le_iff₀ him0).mpr (by linarith)
        _ ≤ 8 := by norm_num
    · have htwo : (M : Real) ≤ 2 := by
        have hc : ⌈|z.im|⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using (le_of_not_ge him))
        dsimp [M]
        exact_mod_cast (by omega : ⌈|z.im|⌉₊ + 1 ≤ 2)
      calc
        _ ≤ ∑ _n ∈ Finset.range M, (4 : Real) := by
          apply Finset.sum_le_sum
          intro n _
          have hn : (1 : Real) / 4 ≤ ‖z + n‖ := by
            have hh := Complex.re_le_norm (z + n)
            simp only [Complex.add_re, Complex.natCast_re] at hh
            linarith [Nat.cast_nonneg (α := Real) n]
          rw [norm_inv]
          exact (inv_anti₀ (by norm_num : (0 : Real) < 1 / 4) hn).trans (by norm_num)
        _ ≤ 8 := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; linarith
  have hgamma : ‖(Real.eulerMascheroniConstant : Complex)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [Real.one_half_lt_eulerMascheroniConstant])]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hhead : ‖digammaApprox z M‖ ≤ 1 + ((harmonic M : Rat) : Real) + 8 := by
    calc
      _ ≤ ‖-(Real.eulerMascheroniConstant : Complex)‖ +
          ∑ n ∈ Finset.range M, ‖((n : Complex) + 1)⁻¹ - (z + n)⁻¹‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
      _ ≤ 1 + ∑ n ∈ Finset.range M,
          (‖((n : Complex) + 1)⁻¹‖ + ‖(z + n)⁻¹‖) := by
        exact add_le_add (by simpa using hgamma)
          (Finset.sum_le_sum fun n _ => norm_sub_le _ _)
      _ = 1 + ((harmonic M : Rat) : Real) +
          ∑ n ∈ Finset.range M, ‖(z + n)⁻¹‖ := by
        rw [Finset.sum_add_distrib]
        have he : ∑ n ∈ Finset.range M, ‖((n : Complex) + 1)⁻¹‖ =
            ((harmonic M : Rat) : Real) := by
          calc
            _ = ∑ n ∈ Finset.range M, ((n : Real) + 1)⁻¹ := by
              apply Finset.sum_congr rfl
              intro n _
              rw [norm_inv, ← Nat.cast_one (R := Complex), ← Nat.cast_add,
                Complex.norm_natCast]
              norm_cast
            _ = _ := Complex.sum_inv_natCast_add_one_real M
        rw [he]
        ring
      _ ≤ _ := by linarith
  have htri := norm_sub_le (Complex.digamma z - digammaApprox z M) (-digammaApprox z M)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
  have hh := harmonic_le_one_add_log M
  have hl := Real.log_le_log hMpos hMhi
  linarith

private theorem gamma_formula_bound {q : Nat} {chi : DirichletCharacter Complex q}
    {s : Complex} {d : Complex} {C : Real}
    (hf : logDeriv chi.gammaFactor s =
      -(Real.log Real.pi : Complex) / 2 + (1 / 2 : Complex) * d)
    (hd : ‖d‖ ≤ Real.log (|s.im| + 2) + C) :
    ‖logDeriv chi.gammaFactor s‖ ≤ Real.log (|s.im| + 2) / 2 + (C + 3) / 2 := by
  have hpi : ‖(Real.log Real.pi : Complex)‖ ≤ 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    linarith [Real.log_le_sub_one_of_pos Real.pi_pos, Real.pi_lt_four]
  rw [hf]
  have h := norm_add_le (-(Real.log Real.pi : Complex) / 2) ((1 / 2 : Complex) * d)
  simp only [norm_div, norm_neg, norm_mul] at h
  norm_num at h
  simp only [Complex.norm_real, Real.norm_eq_abs] at hpi
  linarith

theorem norm_logDeriv_gammaFactor_left_le {q : Nat}
    (chi : DirichletCharacter Complex q) {s : Complex}
    (hs : s.re = -(1 : Real) / 2) :
    ‖logDeriv chi.gammaFactor s‖ ≤ Real.log (|s.im| + 2) / 2 + 11 := by
  have hsrange : -1 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hbound : ∀ z : Complex, (1 : Real) / 4 ≤ z.re → z.re ≤ 2 →
      |z.im| ≤ |s.im| → ‖Complex.digamma z‖ ≤ Real.log (|s.im| + 2) + 14 := by
    intro z h1 h2 hi
    exact (norm_digamma_le_log_add_fourteen h1 h2).trans
      (add_le_add (Real.log_le_log (by positivity : 0 < |z.im| + 2)
        (by linarith : |z.im| + 2 ≤ |s.im| + 2)) le_rfl)
  rcases chi.even_or_odd with he | ho
  · have hd := hbound ((s + 2) / 2)
      (by norm_num [Complex.div_ofNat_re, hs])
      (by norm_num [Complex.div_ofNat_re, hs])
      (by simp [abs_div])
    have hr := Complex.digamma_apply_add_one (s / 2)
      (half_ne_neg_nat_of_neg_one_lt_re_of_ne_zero hsrange hs0)
    rw [show s / 2 + 1 = (s + 2) / 2 by ring] at hr
    have hn : (1 : Real) / 4 ≤ ‖s / 2‖ := by
      have h := Complex.abs_re_le_norm (s / 2)
      norm_num [Complex.div_ofNat_re, hs] at h ⊢
      exact h
    have hi : ‖(s / 2)⁻¹‖ ≤ 4 := by
      rw [norm_inv]
      exact (inv_anti₀ (by norm_num : (0 : Real) < 1 / 4) hn).trans (by norm_num)
    have ht := norm_sub_le (Complex.digamma ((s + 2) / 2)) ((s / 2)⁻¹)
    rw [show Complex.digamma ((s + 2) / 2) - (s / 2)⁻¹ =
      Complex.digamma (s / 2) by rw [hr]; ring] at ht
    have hg := gamma_formula_bound
      (logDeriv_gammaFactor_of_even_of_neg_one_lt_re_of_ne_zero he hsrange hs0)
      (C := 18) (by linarith)
    linarith
  · have hd := hbound ((s + 1) / 2)
      (by norm_num [Complex.div_ofNat_re, hs])
      (by norm_num [Complex.div_ofNat_re, hs])
      (by simp [abs_div])
    have hg := gamma_formula_bound
      (logDeriv_gammaFactor_of_odd_of_neg_one_lt_re ho hsrange) hd
    linarith

theorem norm_logDeriv_gammaFactor_three_halves_le {q : Nat}
    (chi : DirichletCharacter Complex q) {s : Complex}
    (hs : s.re = (3 : Real) / 2) :
    ‖logDeriv chi.gammaFactor s‖ ≤ Real.log (|s.im| + 2) / 2 + 9 := by
  have hspos : 0 < s.re := by linarith
  have hbound : ∀ z : Complex, (1 : Real) / 4 ≤ z.re → z.re ≤ 2 →
      |z.im| ≤ |s.im| → ‖Complex.digamma z‖ ≤ Real.log (|s.im| + 2) + 14 := by
    intro z h1 h2 hi
    exact (norm_digamma_le_log_add_fourteen h1 h2).trans
      (add_le_add (Real.log_le_log (by positivity : 0 < |z.im| + 2)
        (by linarith : |z.im| + 2 ≤ |s.im| + 2)) le_rfl)
  rcases chi.even_or_odd with he | ho
  · have hd := hbound (s / 2)
      (by norm_num [Complex.div_ofNat_re, hs])
      (by norm_num [Complex.div_ofNat_re, hs]) (by simp [abs_div])
    have hg := gamma_formula_bound (logDeriv_gammaFactor_of_even he hspos) hd
    linarith
  · have hd := hbound ((s + 1) / 2)
      (by norm_num [Complex.div_ofNat_re, hs])
      (by norm_num [Complex.div_ofNat_re, hs]) (by simp [abs_div])
    have hg := gamma_formula_bound (logDeriv_gammaFactor_of_odd ho hspos) hd
    linarith

end LiuWang.Proof.LocalAnalyticBounds.LeftVertical
