import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.FiniteEvaluator
import LiuWang.Proof.Campaign20260915.ZetaValidation.StirlingRational

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator

open LiuWang.Proof.Campaign20260915.ZetaValidation
open Finset

def piLower : ℚ := rationalPi20
def piUpper : ℚ := rationalPi20 + 1 / 10 ^ 20

def CutoffWindow (a b : ℚ) (lo hi : ℕ) : Prop :=
  0 ≤ a ∧ 2 * piUpper * lo ^ 2 ≤ a ∧ b < 2 * piLower * (hi + 1) ^ 2

instance (a b : ℚ) (lo hi : ℕ) : Decidable (CutoffWindow a b lo hi) :=
  inferInstanceAs (Decidable
    (0 ≤ a ∧ 2 * piUpper * lo ^ 2 ≤ a ∧ b < 2 * piLower * (hi + 1) ^ 2))

noncomputable section

def sourceCutoff (t : ℝ) : ℕ := ⌊Real.sqrt (t / (2 * Real.pi))⌋₊

def sourceMainSum (t : ℝ) : ℝ := finiteMainSum t (sourceCutoff t)

theorem pi_enclosure : (piLower : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piUpper : ℝ) := by
  have hl := Real.pi_gt_d20
  have hu := Real.pi_lt_d20
  norm_num [piLower, piUpper, rationalPi20] at *
  exact ⟨hl.le, hu.le⟩

theorem sourceCutoff_eq_iff {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    sourceCutoff t = m ↔
      2 * Real.pi * (m : ℝ) ^ 2 ≤ t ∧ t < 2 * Real.pi * ((m : ℝ) + 1) ^ 2 := by
  rw [sourceCutoff, Nat.floor_eq_iff (Real.sqrt_nonneg _),
    Real.le_sqrt (Nat.cast_nonneg m) (by positivity),
    Real.sqrt_lt (by positivity) (by positivity),
    le_div_iff₀ (by positivity : 0 < 2 * Real.pi),
    div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> nlinarith

theorem sourceCutoff_boundary (m : ℕ) :
    sourceCutoff (2 * Real.pi * (m : ℝ) ^ 2) = m := by
  apply (sourceCutoff_eq_iff (by positivity) m).mpr
  constructor
  · rfl
  · have h : (m : ℝ) ^ 2 < ((m : ℝ) + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    exact mul_lt_mul_of_pos_left h (by positivity)

theorem cutoffWindow_bounds {a b : ℚ} {lo hi : ℕ} (h : CutoffWindow a b lo hi)
    {t : ℝ} (ht : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ)) :
    lo ≤ sourceCutoff t ∧ sourceCutoff t ≤ hi := by
  have ha : (0 : ℝ) ≤ a := by exact_mod_cast h.1
  have hl : 2 * (piUpper : ℝ) * (lo : ℝ) ^ 2 ≤ (a : ℝ) := by exact_mod_cast h.2.1
  have hu : (b : ℝ) < 2 * (piLower : ℝ) * ((hi : ℝ) + 1) ^ 2 := by exact_mod_cast h.2.2
  have hlow : 2 * Real.pi * (lo : ℝ) ^ 2 ≤ t :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pi_enclosure.2 (by norm_num))
      (sq_nonneg _)).trans (hl.trans ht.1)
  have hhigh : t < 2 * Real.pi * ((hi : ℝ) + 1) ^ 2 :=
    (ht.2.trans_lt hu).trans_le
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pi_enclosure.1 (by norm_num))
        (sq_nonneg _))
  have ht0 := ha.trans ht.1
  constructor
  · apply Nat.le_floor
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
    nlinarith
  · have hs : Real.sqrt (t / (2 * Real.pi)) < (hi : ℝ) + 1 := by
      rw [Real.sqrt_lt (by positivity) (by positivity),
        div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
      nlinarith
    have hf := Nat.floor_le (Real.sqrt_nonneg (t / (2 * Real.pi)))
    have hx : (sourceCutoff t : ℝ) < ((hi + 1 : ℕ) : ℝ) := by
      simpa [sourceCutoff] using hf.trans_lt hs
    have hxN : sourceCutoff t < hi + 1 := by exact_mod_cast hx
    omega

theorem cutoffWindow_constant {a b : ℚ} {m : ℕ} (h : CutoffWindow a b m m)
    {t : ℝ} (ht : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ)) :
    sourceCutoff t = m := by
  obtain ⟨hl, hu⟩ := cutoffWindow_bounds h ht
  omega

theorem sourceTerm_abs_le_two (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |sourceTerm t n| ≤ 2 := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hw : 1 / Real.sqrt (n : ℝ) ≤ 1 :=
    (div_le_one hs).mpr (Real.one_le_sqrt.mpr (by exact_mod_cast hn))
  have hc := Real.abs_cos_le_one (t * Real.log (n : ℝ) - criticalGammaArgument t)
  rw [sourceTerm, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (n : ℝ))]
  nlinarith [mul_le_mul hw hc (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]

theorem finiteMainSum_length_error (t : ℝ) (lo d : ℕ) :
    |finiteMainSum t (lo + d) - finiteMainSum t lo| ≤ 2 * (d : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hs : finiteMainSum t (lo + (d + 1)) =
        finiteMainSum t (lo + d) + sourceTerm t (lo + d + 1) := by
      change (∑ j ∈ range ((lo + d) + 1), sourceTerm t (j + 1)) = _
      exact sum_range_succ _ _
    rw [hs]
    have ht := abs_add_le (finiteMainSum t (lo + d) - finiteMainSum t lo)
      (sourceTerm t (lo + d + 1))
    have he : finiteMainSum t (lo + d) + sourceTerm t (lo + d + 1) - finiteMainSum t lo =
        (finiteMainSum t (lo + d) - finiteMainSum t lo) + sourceTerm t (lo + d + 1) := by ring
    rw [he]
    push_cast
    linarith [sourceTerm_abs_le_two t (n := lo + d + 1) (by omega)]

theorem evaluate_window_error {D lo hi : ℕ} (hD : 1 ≤ D)
    (cache : ℕ → SharedEntry)
    (hcache : ∀ n, 1 ≤ n → n ≤ lo → EntryValid n (cache n))
    {a b t₀ θ₀ dt dθ : ℚ} (hw : CutoffWindow a b lo hi)
    {t : ℝ} (hab : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ))
    (ht : |t - (t₀ : ℝ)| ≤ (dt : ℝ))
    (hθ : |criticalGammaArgument t - (θ₀ : ℝ)| ≤ (dθ : ℝ))
    (hfit : ∀ n, 1 ≤ n → n ≤ lo → PhaseFits (cache n) t₀ θ₀) :
    |sourceMainSum t - (evaluate D cache t₀ θ₀ lo : ℝ)| ≤
      (evaluationRadius D cache t₀ dt dθ lo : ℝ) + 2 * ((hi - lo : ℕ) : ℝ) := by
  obtain ⟨hl, hu⟩ := cutoffWindow_bounds hw hab
  have hlen := finiteMainSum_length_error t lo (sourceCutoff t - lo)
  rw [Nat.add_sub_of_le hl] at hlen
  have he := evaluate_error hD cache hcache ht hθ hfit
  have htri := abs_sub_le (sourceMainSum t) (finiteMainSum t lo)
    (evaluate D cache t₀ θ₀ lo : ℝ)
  have hdiff : ((sourceCutoff t - lo : ℕ) : ℝ) ≤ ((hi - lo : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_right hu lo
  change |sourceMainSum t - finiteMainSum t lo| ≤ _ at hlen
  linarith

#print axioms sourceCutoff_boundary
#print axioms evaluate_window_error

end

end LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator
