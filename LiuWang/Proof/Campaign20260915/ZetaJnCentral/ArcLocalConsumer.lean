import LiuWang.Proof.Campaign20260915.ZetaJnCentral.MinorArcBudget
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.FullLocalBudget

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem sourceMinor_endpoints_bound {eta e : ℝ} {k : ℤ}
    (he : |e| = 1) (hside : 0 < e * (eta - k))
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius) :
    |sourceMinorHigh eta k e| ≤ sourcePoleDistance ∧
      |sourceMinorLow eta k e| ≤ sourcePoleDistance := by
  have hl := sourceMinorPoint_distance he hk (-sourceMinorAngle eta k e)
  have hr := sourceMinorPoint_distance he hk (sourceMinorAngle eta k e)
  rw [sourceMinorPoint_endpoint he hside hk (Or.inr rfl), rsDescentPoint_distance] at hl
  rw [sourceMinorPoint_endpoint he hside hk (Or.inl rfl), rsDescentPoint_distance] at hr
  have he' : e = 1 ∨ e = -1 := abs_eq_abs.mp (by simpa using he : |e| = |(1 : ℝ)|)
  rcases he' with rfl | rfl
  · simpa [sourceMinorHigh, sourceMinorLow, sourceMinorY] using And.intro hl hr
  · simpa [sourceMinorHigh, sourceMinorLow, sourceMinorY] using And.intro hr hl

def centralSupBound (sigma eta R d : ℝ) (N : ℕ) : ℝ :=
  centralTaylorConstant sigma eta R (N + 1) * d ^ N * (d + 1 / (Real.sqrt 2 * Real.pi))

theorem centralSupBound_nonneg (sigma eta : ℝ) {R d : ℝ}
    (hR : 0 < R) (hd : 0 ≤ d) (N : ℕ) : 0 ≤ centralSupBound sigma eta R d N := by
  unfold centralSupBound
  exact mul_nonneg (mul_nonneg (centralTaylorConstant_nonneg sigma eta hR _)
    (pow_nonneg hd N)) (by positivity)

theorem jn_central_sup (sigma : ℝ) {eta R d y : ℝ} {m : ℕ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hyd : |y| ≤ d) (hdR : 21 / 20 * (rsSaddleScale * d) ≤ R)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖rsJnIntegrand sigma eta m (N + 1) y‖ ≤ centralSupBound sigma eta R d N := by
  have hC := centralTaylorConstant_nonneg sigma eta hR0 (N + 1)
  have hd := (abs_nonneg y).trans hyd
  apply (jn_central_pointwise sigma he hR0 hR
    (by nlinarith [mul_le_mul_of_nonneg_left hyd rsSaddleScale_pos.le]) hm0 hm1 N).trans
  have hex : Real.exp (-Real.pi * y ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg y, Real.pi_pos])
  have hpow : |y| ^ N ≤ d ^ N := pow_le_pow_left₀ (abs_nonneg _) hyd N
  have hbase : centralTaylorConstant sigma eta R (N + 1) *
      Real.exp (-Real.pi * y ^ 2) * |y| ^ N ≤
      centralTaylorConstant sigma eta R (N + 1) * d ^ N := by
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hex hC) hpow
      (pow_nonneg (abs_nonneg _) _) (by simpa using hC)).trans_eq
    ring
  exact mul_le_mul hbase (by linarith) (by positivity) (mul_nonneg hC (pow_nonneg hd N))

theorem jn_central_subinterval (sigma : ℝ) {eta R d a b : ℝ} {m : ℕ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (ha : |a| ≤ d) (hb : |b| ≤ d) (hdR : 21 / 20 * (rsSaddleScale * d) ≤ R)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖∫ y : ℝ in a..b, rsJnIntegrand sigma eta m (N + 1) y‖ ≤
      centralSupBound sigma eta R d N * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro y hy
  have hy' := uIoc_subset_uIcc hy
  have hyd : |y| ≤ d := by
    rcases mem_uIcc.mp hy' with hy' | hy'
    · exact abs_le.mpr ⟨(abs_le.mp ha).1.trans hy'.1, hy'.2.trans (abs_le.mp hb).2⟩
    · exact abs_le.mpr ⟨(abs_le.mp hb).1.trans hy'.1, hy'.2.trans (abs_le.mp ha).2⟩
  exact jn_central_sup sigma he hR0 hR hyd hdR hm0 hm1 N

theorem jn_minor_connectors (sigma : ℝ) {eta R e : ℝ} {m : ℕ} {k : ℤ}
    (heta : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hDR : 21 / 20 * (rsSaddleScale * sourcePoleDistance) ≤ R)
    (he : |e| = 1) (hside : 0 < e * (eta - k))
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖∫ y : ℝ in sourcePoleDistance..(sourceMinorHigh eta k e),
      rsJnIntegrand sigma eta m (N + 1) y‖ +
    ‖∫ y : ℝ in (sourceMinorLow eta k e)..(-sourcePoleDistance),
      rsJnIntegrand sigma eta m (N + 1) y‖ ≤
      centralIntervalBudget sigma eta R sourcePoleDistance N := by
  have hp := sourceMinor_endpoints_bound he hside hk
  have horder := sourceMinorLow_le_high he hside hk
  have hD : |sourcePoleDistance| ≤ sourcePoleDistance := (abs_of_pos sourcePoleDistance_pos).le
  have hDn : |-sourcePoleDistance| ≤ sourcePoleDistance := by simpa only [abs_neg] using hD
  have hh := jn_central_subinterval sigma heta hR0 hR hD hp.1 hDR hm0 hm1 N
  have hl := jn_central_subinterval sigma heta hR0 hR hp.2 hDn hDR hm0 hm1 N
  rw [abs_of_nonpos (by linarith [(abs_le.mp hp.1).2])] at hh
  rw [abs_of_nonpos (by linarith [(abs_le.mp hp.2).1])] at hl
  have hB := centralSupBound_nonneg sigma eta hR0 sourcePoleDistance_pos.le N
  have hm := mul_nonneg hB (sub_nonneg.mpr horder)
  change _ ≤ 2 * sourcePoleDistance * centralSupBound sigma eta R sourcePoleDistance N
  nlinarith

theorem jn_local_subinterval_integrable (sigma : ℝ) {eta a b : ℝ} {m : ℕ}
    (he : 0 < eta) (ha : |a| ≤ eta / 2) (hb : |b| ≤ eta / 2)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    IntervalIntegrable (rsJnIntegrand sigma eta m (N + 1)) volume a b := by
  apply (jn_local_integrable sigma he hm0 hm1 N).mono_set
  rw [uIcc_of_ge (by linarith : -eta / 2 ≤ eta / 2)]
  intro y hy
  have hyd : |y| ≤ eta / 2 := by
    rcases mem_uIcc.mp hy with hy | hy
    · exact abs_le.mpr ⟨(abs_le.mp ha).1.trans hy.1, hy.2.trans (abs_le.mp hb).2⟩
    · exact abs_le.mpr ⟨(abs_le.mp hb).1.trans hy.1, hy.2.trans (abs_le.mp ha).2⟩
  simpa only [mem_Icc, neg_div] using abs_le.mp hyd

theorem jn_local_minor_split (sigma : ℝ) {eta e : ℝ} {m : ℕ} {k : ℤ}
    (heta : 0 < eta) (hD : sourcePoleDistance ≤ eta / 2)
    (he : |e| = 1) (hside : 0 < e * (eta - k))
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    (∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta m (N + 1) y) =
      (∫ y : ℝ in (eta / 2)..sourcePoleDistance, rsJnIntegrand sigma eta m (N + 1) y) +
      (∫ y : ℝ in sourcePoleDistance..(sourceMinorHigh eta k e), rsJnIntegrand sigma eta m (N + 1) y) +
      (e : ℂ) * jnSourceMinorArc sigma eta m (N + 1) k e +
      (∫ y : ℝ in (sourceMinorLow eta k e)..(-sourcePoleDistance), rsJnIntegrand sigma eta m (N + 1) y) +
      (∫ y : ℝ in (-sourcePoleDistance)..(-eta / 2), rsJnIntegrand sigma eta m (N + 1) y) := by
  have hp := sourceMinor_endpoints_bound he hside hk
  have hD' : |sourcePoleDistance| ≤ eta / 2 := by rwa [abs_of_pos sourcePoleDistance_pos]
  have hDn : |-sourcePoleDistance| ≤ eta / 2 := by simpa only [abs_neg] using hD'
  have he' : |eta / 2| ≤ eta / 2 := (abs_of_pos (by positivity : 0 < eta / 2)).le
  have hen : |-eta / 2| ≤ eta / 2 := by simpa only [neg_div, abs_neg] using he'
  have hH := hp.1.trans hD
  have hL := hp.2.trans hD
  have h1 := jn_local_subinterval_integrable sigma heta he' hD' hm0 hm1 N
  have h2 := jn_local_subinterval_integrable sigma heta hD' hH hm0 hm1 N
  have h3 := jn_local_subinterval_integrable sigma heta hH hL hm0 hm1 N
  have h4 := jn_local_subinterval_integrable sigma heta hL hDn hm0 hm1 N
  have h5 := jn_local_subinterval_integrable sigma heta hDn hen hm0 hm1 N
  rw [← jn_source_minor_oriented sigma m (N + 1) heta (by linarith) he hside hk,
    intervalIntegral.integral_add_adjacent_intervals h1 h2,
    intervalIntegral.integral_add_adjacent_intervals (h1.trans h2) h3,
    intervalIntegral.integral_add_adjacent_intervals ((h1.trans h2).trans h3) h4,
    intervalIntegral.integral_add_adjacent_intervals (((h1.trans h2).trans h3).trans h4) h5]

def arcLocalBudget (sigma eta R : ℝ) (N : ℕ) : ℝ :=
  localJnBudget sigma eta R sourcePoleDistance N +
    Real.pi * sourcePoleRadius * poleArcCoreBound sigma eta R (N + 1)

theorem jn_local_arc_budget (sigma : ℝ) {eta R e : ℝ} {m : ℕ} {k : ℤ}
    (heta : 0 < eta) (hD : sourcePoleDistance ≤ eta / 2)
    (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hDR : 21 / 20 * (rsSaddleScale * sourcePoleDistance) ≤ R)
    (he : |e| = 1) (hside : 0 < e * (eta - k))
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖∫ y : ℝ in (eta / 2)..(-eta / 2), rsJnIntegrand sigma eta m (N + 1) y‖ ≤
      arcLocalBudget sigma eta R N := by
  rw [jn_local_minor_split sigma heta hD he hside hk hm0 hm1 N]
  have hc := jn_minor_connectors sigma heta hR0 hR hDR he hside hk hm0 hm1 N
  have ha := jn_source_minor_bound sigma heta hR0 hR hDR he hside hk hm0 hm1 (N + 1)
  have ho := (jn_middle_integrals sigma heta sourcePoleDistance_pos hD le_rfl hm0 hm1 (N + 1)).2.2
  rw [intervalIntegral.integral_symm sourcePoleDistance (eta / 2),
    intervalIntegral.integral_symm (-eta / 2) (-sourcePoleDistance)]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  apply (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl).trans
  apply (add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl).trans
  simp only [norm_neg, norm_mul, norm_real, Real.norm_eq_abs, he, one_mul]
  unfold arcLocalBudget localJnBudget
  simp only [neg_div] at ho ⊢
  linarith

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
