import LiuWang.Proof.Campaign20260915.ZetaJnCentral.CentralCancellation

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem jn_measurable (sigma eta : ℝ) (m N : ℕ) :
    Measurable (rsJnIntegrand sigma eta m N) := by
  unfold rsJnIntegrand rsGaussianKernel rsHankelDenominator rsSaddleRemainder
    rsSaddleWeight rsSaddleExponent rsDescentPoint
  fun_prop

theorem jn_central_integrable (sigma : ℝ) {eta R d : ℝ} {m : ℕ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hd : 0 ≤ d) (hdR : 21 / 20 * (rsSaddleScale * d) ≤ R)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    IntervalIntegrable (rsJnIntegrand sigma eta m (N + 1)) volume (-d) d := by
  have hi : IntervalIntegrable (fun y : ℝ =>
      centralTaylorConstant sigma eta R (N + 1) * Real.exp (-Real.pi * y ^ 2) *
        |y| ^ N * (|y| + 1 / (Real.sqrt 2 * Real.pi))) volume (-d) d :=
    (by fun_prop : Continuous (fun y : ℝ =>
      centralTaylorConstant sigma eta R (N + 1) * Real.exp (-Real.pi * y ^ 2) *
        |y| ^ N * (|y| + 1 / (Real.sqrt 2 * Real.pi)))).intervalIntegrable _ _
  apply hi.mono_fun' (jn_measurable sigma eta m (N + 1)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
  rw [uIoc_of_le (by linarith : -d ≤ d)] at hy
  have hyd : |y| ≤ d := abs_le.mpr ⟨hy.1.le, hy.2⟩
  exact jn_central_pointwise sigma he hR0 hR
    (by nlinarith [mul_le_mul_of_nonneg_left hyd rsSaddleScale_pos.le]) hm0 hm1 N

theorem jn_local_integrable (sigma : ℝ) {eta : ℝ} {m : ℕ}
    (he : 0 < eta) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    IntervalIntegrable (rsJnIntegrand sigma eta m (N + 1))
      volume (eta / 2) (-eta / 2) := by
  have hs := rsSaddleScale_pos
  have h := jn_central_integrable sigma he
    (R := 3 / 5 * (rsSaddleScale * eta)) (d := eta / 2)
    (by positivity) le_rfl (by positivity)
    (by nlinarith [mul_pos hs he]) hm0 hm1 N
  simpa only [neg_div] using h.symm

def localJnBudget (sigma eta R d : ℝ) (N : ℕ) : ℝ :=
  centralIntervalBudget sigma eta R d N +
    rsJnOuterConstant sigma d (N + 1) * (29 / (Real.pi * d)) *
      Real.exp (-Real.pi / 29 * d ^ 2)

theorem jn_local_split (sigma : ℝ) {eta d : ℝ} {m : ℕ}
    (he : 0 < eta) (hd : 0 ≤ d) (hde : d ≤ eta / 2)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    (∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta m (N + 1) y) =
      -((∫ y : ℝ in (-eta / 2)..(-d), rsJnIntegrand sigma eta m (N + 1) y) +
        (∫ y : ℝ in (-d)..d, rsJnIntegrand sigma eta m (N + 1) y) +
        ∫ y : ℝ in d..(eta / 2), rsJnIntegrand sigma eta m (N + 1) y) := by
  have hi := (jn_local_integrable sigma he hm0 hm1 N).symm
  have hs {a b : ℝ} (ha : -eta / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ eta / 2) :
      IntervalIntegrable (rsJnIntegrand sigma eta m (N + 1)) volume a b := by
    apply hi.mono_set
    rw [uIcc_of_le hab, uIcc_of_le (by linarith : -eta / 2 ≤ eta / 2)]
    exact Icc_subset_Icc ha hb
  have hn := hs (a := -eta / 2) (b := -d) le_rfl (by linarith) (by linarith)
  have hc := hs (a := -d) (b := d) (by linarith) (by linarith) hde
  have hp := hs (a := d) (b := eta / 2) (by linarith) hde le_rfl
  rw [intervalIntegral.integral_add_adjacent_intervals hn hc,
    intervalIntegral.integral_add_adjacent_intervals (hn.trans hc) hp,
    intervalIntegral.integral_symm (eta / 2) (-eta / 2), neg_neg]

theorem jn_local_budget (sigma : ℝ) {eta R d : ℝ} {m : ℕ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hd : 0 < d) (hdR : 21 / 20 * (rsSaddleScale * d) ≤ R) (hde : d ≤ eta / 2)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta m (N + 1) y‖ ≤
      localJnBudget sigma eta R d N := by
  rw [jn_local_split sigma he hd.le hde hm0 hm1 N, norm_neg]
  have hc := jn_central_integral sigma he hR0 hR hd.le hdR hm0 hm1 N
  have ho := (jn_middle_integrals sigma he hd hde le_rfl hm0 hm1 (N + 1)).2.2
  apply norm_add₃_le.trans
  unfold localJnBudget
  simp only [neg_div] at ho ⊢
  linarith

theorem jn_floor_local_budget (sigma : ℝ) {eta R d : ℝ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hd : 0 < d) (hdR : 21 / 20 * (rsSaddleScale * d) ≤ R) (hde : d ≤ eta / 2)
    (N : ℕ) :
    IntervalIntegrable (rsJnIntegrand sigma eta ⌊eta⌋₊ (N + 1))
      volume (eta / 2) (-eta / 2) ∧
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta ⌊eta⌋₊ (N + 1) y‖ ≤
      localJnBudget sigma eta R d N := by
  have h0 := Nat.zero_le_self_sub_floor he.le
  have h1 := (Nat.self_sub_floor_lt_one eta).le
  exact ⟨jn_local_integrable sigma he h0 h1 N,
    jn_local_budget sigma he hR0 hR hd hdR hde h0 h1 N⟩

theorem local_budget_parameters {eta : ℝ} (he : 0 < eta) :
    0 < (21 / 40 * (rsSaddleScale * eta)) ∧
    (21 / 40 * (rsSaddleScale * eta)) ≤ 3 / 5 * (rsSaddleScale * eta) ∧
    0 < eta / 2 ∧
    21 / 20 * (rsSaddleScale * (eta / 2)) ≤ 21 / 40 * (rsSaddleScale * eta) := by
  have hs := mul_pos rsSaddleScale_pos he
  refine ⟨by positivity, by nlinarith, by positivity, ?_⟩
  ring_nf
  rfl

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
