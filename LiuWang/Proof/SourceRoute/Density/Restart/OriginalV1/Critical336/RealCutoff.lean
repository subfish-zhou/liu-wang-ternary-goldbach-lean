import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Titchmarsh.EulerIdentity

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Finset
open scoped Interval

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336

def bernoulliBoundary (x : ℝ) : ℝ := (⌊x⌋ : ℝ) + 1 / 2 - x

def realRemainder (N : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi N, (bernoulliBoundary x : ℂ) * (x : ℂ) ^ (-(s + 1))

theorem bernoulliBoundary_norm (x : ℝ) : ‖bernoulliBoundary x‖ ≤ 1 / 2 :=
  ZetaSum_aux1_3 x

theorem bernoulliBoundary_nat (n : ℕ) : bernoulliBoundary n = 1 / 2 := by
  simp [bernoulliBoundary]

theorem realRemainder_integrable {N : ℝ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (bernoulliBoundary x : ℂ) * (x : ℂ) ^ (-(s + 1)))
      (Set.Ioi N) := by
  apply Integrable.bdd_mul (c := 1 / 2) ?_ ?_ ?_
  · exact (integrableOn_Ioi_cpow_iff hN).mpr (by simp; linarith)
  · apply Measurable.aestronglyMeasurable
    unfold bernoulliBoundary
    push_cast
    exact ((Measurable.comp (measurable_of_countable (fun n : ℤ => (n : ℂ)))
      Int.measurable_floor).add
      measurable_const).sub Complex.measurable_ofReal
  · exact Filter.Eventually.of_forall (fun x => by
      simpa only [Complex.norm_real] using bernoulliBoundary_norm x)

theorem realRemainder_nat {n : ℕ} (s : ℂ) :
    realRemainder n s = Titchmarsh.remainder n s := by
  unfold realRemainder Titchmarsh.remainder bernoulliBoundary
  congr 1
  ext x
  push_cast
  simp only [div_eq_mul_inv, Complex.cpow_neg]

theorem realRemainder_norm_le {N : ℝ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    ‖realRemainder N s‖ ≤ N ^ (-s.re) / (2 * s.re) := by
  have hp : -(s.re + 1) < -1 := by linarith
  calc
    _ ≤ ∫ x in Set.Ioi N, x ^ (-(s.re + 1)) / 2 := by
      apply norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt hp hN).div_const 2)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 := hN.trans hx
      rw [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
      have h := mul_le_mul_of_nonneg_right (bernoulliBoundary_norm x)
        (Real.rpow_nonneg hx0.le (-(s.re + 1)))
      linarith
    _ = _ := by
      rw [integral_div, integral_Ioi_rpow_of_lt hp hN,
        show -(s.re + 1) + 1 = -s.re by ring]
      ring

theorem real_euler_finite {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (n : ℂ) ^ (-s)) =
      ((b : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) +
        (bernoulliBoundary b : ℂ) * (b : ℂ) ^ (-s) -
        (bernoulliBoundary a : ℂ) * (a : ℂ) ^ (-s) +
        s * ∫ x in a..b, (bernoulliBoundary x : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  let f : ℝ → ℂ := fun x => 1 / (x : ℂ) ^ s
  have hx0 {x : ℝ} (hx : x ∈ Set.uIcc a b) : 0 < x := by
    rw [uIcc_of_le hab.le] at hx
    exact ha.trans_le hx.1
  have hder : ContinuousOn (deriv f) (Set.uIcc a b) := by
    have he : EqOn (deriv f) (fun x : ℝ => -s * (x : ℂ) ^ (-(s + 1))) (Set.uIcc a b) :=
      fun x hx => ZetaSum_aux1φderiv hs0 (hx0 hx)
    exact ((Complex.continuous_ofReal.continuousOn.cpow_const
      (fun x hx => Complex.ofReal_mem_slitPlane.mpr (hx0 hx))).const_mul (-s)).congr he
  have he := sum_eq_int_deriv ha.le hab (fun x hx => ZetaSum_aux1φDiff (hx0 hx)) hder
  have hint : (∫ x in a..b, f x) =
      ((b : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
    have h := integral_cpow (a := a) (b := b) (r := -s)
      (Or.inr ⟨by intro h; apply hs1; linear_combination -h, fun hx => (hx0 hx).ne' rfl⟩)
    convert! h using 1
    · apply intervalIntegral.integral_congr
      intro x _
      simp [f, one_div, Complex.cpow_neg]
    · congr 2 <;> ring
  have hb (x : ℝ) (hx : 0 ≤ x) :
      ((⌊x⌋₊ : ℂ) + 1 / 2 - x) = (bernoulliBoundary x : ℂ) := by
    unfold bernoulliBoundary
    rw [← Int.natCast_floor_eq_floor hx]
    push_cast
    rfl
  have hi : (∫ x in a..b, ((⌊x⌋ : ℂ) + 1 / 2 - x) * deriv f x) =
      -s * ∫ x in a..b, (bernoulliBoundary x : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [f]
    rw [ZetaSum_aux1φderiv hs0 (hx0 hx)]
    unfold bernoulliBoundary
    push_cast
    ring
  change (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n) = _ at he
  rw [hint, hb b (ha.trans hab).le, hb a ha.le, hi] at he
  simpa only [f, Complex.ofReal_natCast, one_div, ← Complex.cpow_neg, neg_mul, sub_neg_eq_add] using he

theorem real_cutoff_identity {N : ℝ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s - (∑ n ∈ Finset.Icc 1 ⌊N⌋₊, (n : ℂ) ^ (-s)) =
      s * realRemainder N s + (N : ℂ) ^ (1 - s) / (s - 1) -
        (bernoulliBoundary N : ℂ) * (N : ℂ) ^ (-s) := by
  let b := ⌊N⌋₊ + 1
  have hb : N < (b : ℝ) := by simpa [b] using Nat.lt_floor_add_one N
  have hb0 : 0 < b := by dsimp [b]; omega
  have he := real_euler_finite hN hb hs hs1
  rw [Nat.floor_natCast, bernoulliBoundary_nat] at he
  push_cast at he
  have hz := Titchmarsh.equation_3_5_3 hb0 hs hs1
  rw [← realRemainder_nat] at hz
  have hi := intervalIntegral.integral_Ioi_sub_Ioi (realRemainder_integrable hN hs) hb.le
  change realRemainder N s - realRemainder b s =
    ∫ x in N..(b : ℝ), (bernoulliBoundary x : ℂ) * (x : ℂ) ^ (-(s + 1)) at hi
  have hsum :
      (∑ n ∈ Finset.Icc 1 b, (n : ℂ) ^ (-s)) =
        (∑ n ∈ Finset.Icc 1 ⌊N⌋₊, (n : ℂ) ^ (-s)) +
          ∑ n ∈ Finset.Ioc ⌊N⌋₊ b, (n : ℂ) ^ (-s) := by
    have hset : Finset.Icc 1 b = Finset.Icc 1 ⌊N⌋₊ ∪ Finset.Ioc ⌊N⌋₊ b := by
      ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; dsimp [b]; omega
    rw [hset, Finset.sum_union]
    exact Finset.disjoint_left.mpr (by
      intro n hn hm; simp only [Finset.mem_Icc, Finset.mem_Ioc] at hn hm; omega)
  rw [hsum] at hz
  have hden : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hp : ((b : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) =
      (N : ℂ) ^ (1 - s) / (s - 1) - (b : ℂ) ^ (1 - s) / (s - 1) := by
    rw [show 1 - s = -(s - 1) by ring]
    field_simp
    ring
  rw [hp, ← hi] at he
  linear_combination hz + he

theorem real_cutoff_below_one {N : ℝ} (hN : 0 < N) (hN1 : N < 1) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s * realRemainder N s + (N : ℂ) ^ (1 - s) / (s - 1) -
      ((1 / 2 - N : ℝ) : ℂ) * (N : ℂ) ^ (-s) := by
  have hf : ⌊N⌋₊ = 0 := Nat.floor_eq_zero.mpr hN1
  have hi : ⌊N⌋ = 0 := by rw [← Int.natCast_floor_eq_floor hN.le, hf]; rfl
  simpa [hf, bernoulliBoundary, hi] using real_cutoff_identity hN hs hs1

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336
