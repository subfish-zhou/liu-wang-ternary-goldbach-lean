import LiuWang.Proof.ExceptionalZeroGap.PolyaVinogradov
import LiuWang.Proof.EffectiveLValue.RealAbelLog
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalDerivativeAnalyticContinuation

/-!
# 真实导数的单倍 Abel 尾

部分和始终从尾的第一个整数开始。对非负递减权重，末端项与变差
恰好合成一次首权重；随后用自然顺序极限与已证解析延拓识别真实导数。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ExceptionalZeroGap

open Complex Finset Filter
open scoped Topology
open DirichletLAbelWeightVariation DirichletLConditionalDerivativeSeries
open DirichletLConditionalDerivativeAnalyticContinuation

theorem sum_weighted_Ico_forward (w : ℕ → ℝ) (f : ℕ → ℂ)
    {m n : ℕ} (hmn : m ≤ n) :
    (∑ k ∈ Ico m n, (w k : ℂ) * f k) =
      (w n : ℂ) * (∑ k ∈ Ico m n, f k) +
        ∑ k ∈ Ico m n, ((w k - w (k + 1) : ℝ) : ℂ) *
          (∑ j ∈ Ico m (k + 1), f j) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [sum_Ico_succ_top hmn, sum_Ico_succ_top hmn,
        sum_Ico_succ_top hmn, sum_Ico_succ_top hmn, ih]
      push_cast
      ring

theorem norm_sum_weighted_Ico_le (w : ℕ → ℝ) (f : ℕ → ℂ)
    {m n : ℕ} {B : ℝ} (hmn : m ≤ n)
    (hwn : 0 ≤ w n) (hw : AntitoneOn w (Set.Icc m n))
    (hB : ∀ k ∈ Set.Icc m n, ‖∑ j ∈ Ico m k, f j‖ ≤ B) :
    ‖∑ k ∈ Ico m n, (w k : ℂ) * f k‖ ≤ w m * B := by
  have hdiff (k : ℕ) (hk : k ∈ Ico m n) : 0 ≤ w k - w (k + 1) := by
    have hk' := mem_Ico.mp hk
    exact sub_nonneg.mpr (hw ⟨hk'.1, hk'.2.le⟩ ⟨by omega, by omega⟩ (by omega))
  rw [sum_weighted_Ico_forward w f hmn]
  calc
    _ ≤ ‖(w n : ℂ) * (∑ k ∈ Ico m n, f k)‖ +
        ∑ k ∈ Ico m n, ‖((w k - w (k + 1) : ℝ) : ℂ) *
          (∑ j ∈ Ico m (k + 1), f j)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ w n * B + ∑ k ∈ Ico m n, (w k - w (k + 1)) * B := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwn]
        exact mul_le_mul_of_nonneg_left (hB n ⟨hmn, le_rfl⟩) hwn
      · apply sum_le_sum
        intro k hk
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hdiff k hk)]
        exact mul_le_mul_of_nonneg_left
          (hB (k + 1) (by have := mem_Ico.mp hk; constructor <;> omega)) (hdiff k hk)
    _ = w m * B := by
      rw [← sum_mul, sum_sub_distrib]
      have htel := sum_Ico_sub (f := w) hmn
      rw [sum_sub_distrib] at htel
      rw [show (∑ k ∈ Ico m n, w k) - (∑ k ∈ Ico m n, w (k + 1)) =
        w m - w n by linarith only [htel]]
      ring

def realLogWeight (σ t : ℝ) : ℝ := Real.log t * t ^ (-σ)

theorem realLogWeight_nonneg (σ : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ realLogWeight σ t :=
  mul_nonneg (Real.log_nonneg ht) (Real.rpow_nonneg (by linarith) _)

theorem hasDerivAt_realLogWeight (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (realLogWeight σ)
      (t ^ (-σ - 1) * (1 - σ * Real.log t)) t := by
  have h := (Real.hasDerivAt_log ht.ne').mul
    (Real.hasDerivAt_rpow_const (p := -σ) (Or.inl ht.ne'))
  convert! h using 1
  rw [Real.rpow_sub_one ht.ne']
  ring

theorem antitoneOn_realLogWeight {σ y : ℝ} (hσ : 0 ≤ σ)
    (hy : 0 < y) (hyσ : 1 ≤ σ * Real.log y) :
    AntitoneOn (realLogWeight σ) (Set.Ici y) := by
  have hd (t : ℝ) (ht : t ∈ Set.Ici y) := hasDerivAt_realLogWeight σ (hy.trans_le ht)
  apply antitoneOn_of_deriv_nonpos (convex_Ici y)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hd t (interior_subset ht)).deriv]
  apply mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hy.le.trans (interior_subset ht)) _)
  have hlog := Real.log_le_log hy (interior_subset ht)
  nlinarith

theorem logCpowWeight_ofReal {σ t : ℝ} (ht : 0 ≤ t) :
    logCpowWeight (σ : ℂ) t = -(realLogWeight σ t : ℝ) := by
  rw [logCpowWeight, cpowWeight, show -(σ : ℂ) = ((-σ : ℝ) : ℂ) by simp,
    ← Complex.ofReal_cpow ht, realLogWeight]
  push_cast
  ring

variable {r : ℕ} [NeZero r]

theorem norm_sum_Ico_derivative_weight_le {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hr : 987 ≤ r) {σ y : ℝ}
    (hσ : 0 ≤ σ) (hy : 1 ≤ y) (hyσ : 1 ≤ σ * Real.log y)
    {m n : ℕ} (hym : y ≤ m) (hmn : m ≤ n) :
    ‖∑ k ∈ Ico m n, logCpowWeight (σ : ℂ) k * χ k‖ ≤
      Real.sqrt r * Real.log r * realLogWeight σ y := by
  have hm : 1 ≤ m := by exact_mod_cast hy.trans hym
  have hmono := antitoneOn_realLogWeight hσ (by linarith) hyσ
  have hweight (k : ℕ) :
      logCpowWeight (σ : ℂ) k * χ k =
        -((realLogWeight σ k : ℂ) * χ k) := by
    rw [logCpowWeight_ofReal (Nat.cast_nonneg k)]
    ring
  simp_rw [hweight]
  rw [sum_neg_distrib, norm_neg]
  calc
    _ ≤ realLogWeight σ m * (Real.sqrt r * Real.log r) := by
      apply norm_sum_weighted_Ico_le _ _ hmn
      · apply realLogWeight_nonneg
        exact_mod_cast hm.trans hmn
      · intro i hi j _ hij
        exact hmono (hym.trans (by exact_mod_cast hi.1))
          (hym.trans (by exact_mod_cast hi.1.trans hij)) (by exact_mod_cast hij)
      · intro k _
        exact norm_sum_Ico_le_sqrt_mul_log hχ hr m k
    _ ≤ realLogWeight σ y * (Real.sqrt r * Real.log r) :=
      mul_le_mul_of_nonneg_right (hmono (Set.mem_Ici.mpr le_rfl) hym hym)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg _))
    _ = _ := by ring

/-- 从 `floor y + 1` 开始的真实导数尾；不将 `floor y` 视为 `y`。 -/
theorem norm_deriv_sub_sum_floor_le {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hr : 987 ≤ r) {σ y : ℝ}
    (hσ : 0 < σ) (hy : 1 ≤ y) (hyσ : 1 ≤ σ * Real.log y) :
    ‖deriv χ.LFunction (σ : ℂ) -
        ∑ k ∈ range (⌊y⌋₊ + 1), logCpowWeight (σ : ℂ) k * χ k‖ ≤
      Real.sqrt r * Real.log r * (Real.log y / y ^ σ) := by
  have hne := EffectiveLValue.primitiveCharacter_ne_one χ hχ (by omega : 1 < r)
  have hs : 0 < (σ : ℂ).re := hσ
  have hlim := tendsto_sum_range_orderedLogDerivativeSeries χ hne (σ : ℂ) hs
  rw [orderedLogDerivativeSeries_eq_deriv_LFunction_of_re_pos χ hne (σ : ℂ) hs] at hlim
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖(∑ k ∈ range n, logCpowWeight (σ : ℂ) k * χ k) -
          ∑ k ∈ range (⌊y⌋₊ + 1), logCpowWeight (σ : ℂ) k * χ k‖ ≤
        Real.sqrt r * Real.log r * realLogWeight σ y := by
    filter_upwards [eventually_ge_atTop (⌊y⌋₊ + 1)] with n hn
    rw [← sum_Ico_eq_sub _ hn]
    exact norm_sum_Ico_derivative_weight_le hχ hr hσ.le hy hyσ
      (by exact_mod_cast (Nat.lt_floor_add_one y).le) hn
  have h := le_of_tendsto ((hlim.sub_const _).norm) hbound
  simpa only [realLogWeight, Real.rpow_neg (by linarith : 0 ≤ y), div_eq_mul_inv] using h

end LiuWang.Proof.ExceptionalZeroGap
