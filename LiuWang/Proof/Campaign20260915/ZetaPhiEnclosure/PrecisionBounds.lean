import LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure.MachinPrecision

set_option autoImplicit false
noncomputable section

open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure

def sincTail (n : ℕ) : ℚ := 3 ^ (n + 1) / (n + 2).factorial

theorem sincApprox_abs_bound (n : ℕ) {x : ℚ} (hx : |x| ≤ 3) :
    |sincApprox n x| ≤ 1 + sincTail n := by
  have hxR : |(x : ℝ)| ≤ 3 := by exact_mod_cast hx
  have he := sincPolynomial_error n (x : ℝ)
  have ht : |(x : ℝ)| ^ (n + 1) / (n + 2).factorial ≤ (sincTail n : ℝ) := by
    simp only [sincTail, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
    gcongr
  have h := abs_sub_le (sincPolynomial n (x : ℝ)) (Real.sinc (x : ℝ)) 0
  rw [sub_zero, sub_zero, abs_sub_comm (sincPolynomial _ _) (Real.sinc _)] at h
  have hb : |(sincApprox n x : ℝ)| ≤ 1 + (sincTail n : ℝ) := by
    rw [sincApprox_cast]
    linarith [Real.abs_sinc_le_one (x : ℝ)]
  exact_mod_cast hb

theorem sincError_bound (n : ℕ) {x : ℚ} (hx : |x| ≤ 3) (e : ℚ) :
    sincError n x e ≤ sincTail n + e := by
  unfold sincError sincTail
  gcongr

theorem phi_arguments_bound {r : ℚ} (hr : |r| ≤ 1) :
    |r ^ 2 - 1 / 4| ≤ 3 / 2 ∧ |r + 1 / 2| ≤ 3 / 2 ∧ |r - 1 / 2| ≤ 3 / 2 := by
  have hr' := abs_le.mp hr
  have hs := (sq_le_one_iff_abs_le_one r).mpr hr
  constructor
  · rw [abs_le]
    constructor <;> nlinarith [sq_nonneg r]
  · constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem scaled_argument_bound {p a : ℚ} (hp : |p| ≤ 4) (ha : |a| ≤ 3 / 2) :
    |p / 2 * a| ≤ 3 := by
  rw [abs_mul, abs_div]
  norm_num
  nlinarith [mul_le_mul hp ha (abs_nonneg _) (by norm_num : (0 : ℚ) ≤ 4)]

theorem phiApprox_center_bound (n : ℕ) {p ep r d : ℚ}
    (hp : |p| ≤ 4) (hr : |r| ≤ 1) (hT : sincTail n ≤ 1) :
    |(phiApprox n p ep r d).center| ≤ 48 := by
  have hn := sincApprox_abs_bound n (scaled_argument_bound hp (phi_arguments_bound hr).1)
  have hS : (1 : ℚ) / 24 ≤ phiSafeDenominator n p r := le_max_left _ _
  have hpos : 0 < phiSafeDenominator n p r := lt_of_lt_of_le (by norm_num) hS
  change |phiNumeratorApprox n p r / phiSafeDenominator n p r| ≤ 48
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  change |sincApprox n (p / 2 * (r ^ 2 - 1 / 4))| ≤ _
  linarith

theorem phiApprox_radius_bound (n : ℕ) {p ep r d : ℚ}
    (hp : |p| ≤ 4) (hep : 0 ≤ ep) (hr : |r| ≤ 1) (hT : sincTail n ≤ 1) :
    (phiApprox n p ep r d).radius ≤ 7500 * (sincTail n + ep) + derivativeBudget 1 * d := by
  have hT0 : 0 ≤ sincTail n := by unfold sincTail; positivity
  have ha := phi_arguments_bound hr
  have hn : phiNumeratorError n p ep r ≤ sincTail n + ep := by
    apply (sincError_bound n (scaled_argument_bound hp ha.1) _).trans
    nlinarith [mul_le_mul_of_nonneg_left ha.1 (show 0 ≤ ep / 2 by positivity)]
  have hu := sincError_bound n (scaled_argument_bound hp ha.2.1)
    (ep / 2 * |r + 1 / 2|)
  have hv := sincError_bound n (scaled_argument_bound hp ha.2.2)
    (ep / 2 * |r - 1 / 2|)
  have heU : sincError n (p / 2 * (r + 1 / 2)) (ep / 2 * |r + 1 / 2|) ≤ sincTail n + ep := by
    nlinarith [mul_le_mul_of_nonneg_left ha.2.1 (show 0 ≤ ep / 2 by positivity)]
  have heV : sincError n (p / 2 * (r - 1 / 2)) (ep / 2 * |r - 1 / 2|) ≤ sincTail n + ep := by
    nlinarith [mul_le_mul_of_nonneg_left ha.2.2 (show 0 ≤ ep / 2 by positivity)]
  have hU : |sincApprox n (p / 2 * (r + 1 / 2))| ≤ 2 := by
    linarith [sincApprox_abs_bound n (scaled_argument_bound hp ha.2.1)]
  have heV0 : 0 ≤ sincError n (p / 2 * (r - 1 / 2)) (ep / 2 * |r - 1 / 2|) := by
    unfold sincError
    positivity
  have hd : phiDenominatorError n p ep r ≤ 12 * sincTail n + 13 * ep := by
    unfold phiDenominatorError
    have hmul := mul_le_mul hU heV heV0 (by norm_num : (0 : ℚ) ≤ 2)
    have hsum : sincError n (p / 2 * (r + 1 / 2)) (ep / 2 * |r + 1 / 2|) +
        |sincApprox n (p / 2 * (r + 1 / 2))| *
          sincError n (p / 2 * (r - 1 / 2)) (ep / 2 * |r - 1 / 2|) ≤
        3 * (sincTail n + ep) := by linarith
    have hprod := mul_le_mul_of_nonneg_left hsum (abs_nonneg p)
    have hp' := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ 3 * (sincTail n + ep) by positivity)
    linarith
  have hd0 : 0 ≤ phiDenominatorError n p ep r := by
    unfold phiDenominatorError sincError
    positivity
  have hq := phiApprox_center_bound (ep := ep) (d := d) n hp hr hT
  have hm := mul_le_mul hq hd hd0 (by norm_num : (0 : ℚ) ≤ 48)
  change 12 * (phiNumeratorError n p ep r +
    |(phiApprox n p ep r d).center| * phiDenominatorError n p ep r) + derivativeBudget 1 * d ≤ _
  nlinarith

theorem precisePi_abs_le_four : |precisePi| ≤ 4 := by
  have hp := precisePi_correct
  have he : (precisePiError : ℝ) ≤ 1 / 100 := by
    have h : precisePiError ≤ (1 : ℚ) / 100 :=
      precisePiError_small.trans (by norm_num)
    have hR : (precisePiError : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) := Rat.cast_le.mpr h
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hR
  have h := abs_sub_le (precisePi : ℝ) Real.pi 0
  rw [sub_zero, sub_zero, abs_sub_comm (precisePi : ℝ) Real.pi, abs_of_pos Real.pi_pos] at h
  have hR : |(precisePi : ℝ)| ≤ 4 := by linarith [Real.pi_lt_d2]
  exact_mod_cast hR

theorem precisePiError_nonneg : 0 ≤ precisePiError := by
  have h : (0 : ℝ) ≤ precisePiError := (abs_nonneg _).trans precisePi_correct
  exact_mod_cast h

theorem sincTail128_small : sincTail 128 ≤ (1 : ℚ) / 10 ^ 140 := by decide +kernel

theorem precisePhi_center_bound {r d : ℚ} (hr : |r| ≤ 1) :
    |(precisePhi r d).center| ≤ 48 :=
  phiApprox_center_bound 128 precisePi_abs_le_four hr
    (sincTail128_small.trans (by norm_num))

theorem precisePhi_radius_bound {r d : ℚ} (hr : |r| ≤ 1) :
    (precisePhi r d).radius ≤ (1 : ℚ) / 10 ^ 115 + derivativeBudget 1 * d := by
  have h := phiApprox_radius_bound (d := d) 128 precisePi_abs_le_four precisePiError_nonneg hr
    (sincTail128_small.trans (by norm_num))
  have hnum : 7500 * ((1 : ℚ) / 10 ^ 140 + 1 / 10 ^ 120) ≤ 1 / 10 ^ 115 := by decide +kernel
  have hmul := mul_le_mul_of_nonneg_left (add_le_add sincTail128_small precisePiError_small)
    (by norm_num : (0 : ℚ) ≤ 7500)
  exact h.trans (add_le_add (hmul.trans hnum) le_rfl)

def preciseDerivativeRadius (n : ℕ) : ℚ :=
  (∑ j ∈ Finset.range (n + 1), (n.choose j : ℚ) *
    ((1 : ℚ) / 10 ^ 115 + (derivativeBudget (n + 1) : ℚ) *
      ((j : ℚ) / 10 ^ 17) ^ (n + 1) / (n + 1).factorial)) /
    ((1 : ℚ) / 10 ^ 17) ^ n + (derivativeBudget (n + 1) : ℚ) / 10 ^ 24

def preciseDerivativeCenterBudget (n : ℕ) : ℚ :=
  (∑ j ∈ Finset.range (n + 1), (n.choose j : ℚ) * 48) / ((1 : ℚ) / 10 ^ 17) ^ n

theorem inwardStep_abs (r h : ℚ) : |inwardStep r h| = |h| := by
  unfold inwardStep
  split_ifs <;> simp

theorem preciseDerivative_bounds (n : ℕ) (hn : n ≤ 6) {r d : ℚ}
    (hr : |r| ≤ 1) (hd : d ≤ (1 : ℚ) / 10 ^ 24) :
    |(derivativeApprox n 128 precisePi precisePiError r (inwardStep r (1 / 10 ^ 17)) d).center| ≤
        preciseDerivativeCenterBudget n ∧
      (derivativeApprox n 128 precisePi precisePiError r (inwardStep r (1 / 10 ^ 17)) d).radius ≤
        preciseDerivativeRadius n := by
  have hdom (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      |r + j * inwardStep r (1 / 10 ^ 17)| ≤ 1 := by
    have hj6 : (j : ℚ) ≤ 6 := by exact_mod_cast
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hn
    have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg _
    have hr' := abs_le.mp hr
    unfold inwardStep
    split_ifs with hr0
    · rw [abs_le]
      constructor <;> nlinarith
    · rw [abs_le]
      constructor <;> nlinarith
  constructor
  · change |(∑ j ∈ Finset.range (n + 1), (stencilWeight n j : ℚ) *
      (precisePhi (r + j * inwardStep r (1 / 10 ^ 17)) 0).center) /
      inwardStep r (1 / 10 ^ 17) ^ n| ≤ _
    rw [abs_div, abs_pow, inwardStep_abs, abs_of_pos (by norm_num : (0 : ℚ) < 1 / 10 ^ 17)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    have hw : |(stencilWeight n j : ℚ)| = (n.choose j : ℚ) := by
      simp [stencilWeight, abs_mul, abs_pow]
    rw [abs_mul, hw]
    exact mul_le_mul_of_nonneg_left (precisePhi_center_bound (hdom j hj)) (by positivity)
  · unfold derivativeApprox preciseDerivativeRadius
    simp only [abs_mul, Nat.abs_cast, inwardStep_abs,
      abs_of_pos (by norm_num : (0 : ℚ) < 1 / 10 ^ 17)]
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hb := precisePhi_radius_bound (d := 0) (hdom j hj)
      simp only [mul_zero, add_zero] at hb
      apply (add_le_add hb (le_refl ((derivativeBudget (n + 1) : ℚ) *
        ((j : ℚ) * (1 / 10 ^ 17)) ^ (n + 1) / (n + 1).factorial))).trans_eq
      congr 1
      ring
    · exact (mul_le_mul_of_nonneg_left hd
        (by positivity : (0 : ℚ) ≤ derivativeBudget (n + 1))).trans_eq (by ring)

theorem RationalBall.divide_radius_bound (b : RationalBall) {a ea l C E F : ℚ}
    (hl : 0 < l) (hC : |b.center| ≤ C) (hE : b.radius ≤ E) (hea : 0 ≤ ea) (hF : ea ≤ F) :
    (b.divide a ea l).radius ≤ (E + (2 * C / l) * F) / l := by
  have hS : l / 2 ≤ max (l / 2) a := le_max_left _ _
  have hS0 : 0 < max (l / 2) a := lt_of_lt_of_le (by positivity) hS
  have hq : |b.center / max (l / 2) a| ≤ 2 * C / l := by
    rw [abs_div, abs_of_pos hS0]
    exact (div_le_div₀ ((abs_nonneg _).trans hC) hC (by positivity) hS).trans_eq (by ring)
  have hm := mul_le_mul hq hF hea (by
    have h := (abs_nonneg _).trans hC
    positivity)
  exact div_le_div_of_nonneg_right (add_le_add hE hm) hl.le

theorem precisePhiOne_radius_small {r d : ℚ} (hr : |r| ≤ 1) (hd : d ≤ (1 : ℚ) / 10 ^ 24) :
    (precisePhiOne r d).radius ≤ (1 : ℚ) / 10 ^ 9 := by
  have hb := preciseDerivative_bounds 3 (by norm_num) hr hd
  have he : 12 * piSquareError precisePi precisePiError ≤ 96 / 10 ^ 120 := by
    unfold piSquareError
    have h := mul_le_mul precisePiError_small (show 4 + |precisePi| ≤ 8 by
      linarith [precisePi_abs_le_four]) (by positivity) (by positivity : (0 : ℚ) ≤ 1 / 10 ^ 120)
    nlinarith
  have he0 : 0 ≤ 12 * piSquareError precisePi precisePiError := by
    unfold piSquareError
    have h := precisePiError_nonneg
    positivity
  apply (RationalBall.divide_radius_bound _ (by norm_num) hb.1 hb.2 he0 he).trans
  decide +kernel

theorem precisePhiTwo_radius_small {r d : ℚ} (hr : |r| ≤ 1) (hd : d ≤ (1 : ℚ) / 10 ^ 24) :
    (precisePhiTwo r d).radius ≤ (1 : ℚ) / 10 ^ 6 := by
  have h2 := preciseDerivative_bounds 2 (by norm_num) hr hd
  have h6 := preciseDerivative_bounds 6 (by norm_num) hr hd
  have hep := precisePiError_nonneg
  have he2 : piSquareError precisePi precisePiError ≤ 8 / 10 ^ 120 := by
    unfold piSquareError
    have h := mul_le_mul precisePiError_small (show 4 + |precisePi| ≤ 8 by
      linarith [precisePi_abs_le_four]) (by positivity) (by positivity : (0 : ℚ) ≤ 1 / 10 ^ 120)
    nlinarith
  have he20 : 0 ≤ piSquareError precisePi precisePiError := by unfold piSquareError; positivity
  have he4 : piFourthError precisePi precisePiError ≤ 256 / 10 ^ 120 := by
    unfold piFourthError
    have hp2 : precisePi ^ 2 ≤ 16 := by
      have h := pow_le_pow_left₀ (abs_nonneg precisePi) precisePi_abs_le_four 2
      norm_num only [sq_abs, show (4 : ℚ) ^ 2 = 16 by norm_num] at h
      exact h
    have h := mul_le_mul he2 (show 16 + precisePi ^ 2 ≤ 32 by linarith)
      (by positivity) (by positivity : (0 : ℚ) ≤ 8 / 10 ^ 120)
    nlinarith
  have he40 : 0 ≤ piFourthError precisePi precisePiError := by unfold piFourthError; positivity
  have hb2 := RationalBall.divide_radius_bound _ (a := 16 * precisePi ^ 2)
    (l := 144) (by norm_num) h2.1 h2.2 (by positivity : 0 ≤ 16 * piSquareError precisePi precisePiError)
    (show 16 * piSquareError precisePi precisePiError ≤ 128 / 10 ^ 120 by nlinarith)
  have hb6 := RationalBall.divide_radius_bound _ (a := 288 * precisePi ^ 4)
    (l := 23328) (by norm_num) h6.1 h6.2 (by positivity : 0 ≤ 288 * piFourthError precisePi precisePiError)
    (show 288 * piFourthError precisePi precisePiError ≤ 73728 / 10 ^ 120 by nlinarith)
  apply (add_le_add hb2 hb6).trans
  decide +kernel

end LiuWang.Proof.Campaign20260915.ZetaPhiEnclosure
