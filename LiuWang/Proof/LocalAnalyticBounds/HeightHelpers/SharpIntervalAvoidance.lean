import BombieriVinogradov.Helpers.RealAnalysis.FiniteSetIntervalAvoidance

/-!
# 长度二区间中的精确有限避点

取 `n + 1` 个间距为 `2 / (n + 1)` 的网格点，端点各留
`1 / (n + 1)`。每个禁点至多严格覆盖一个网格点；鸽巢原理给出
闭半径分离。端点余量用于运输窗口外的点。
-/

set_option autoImplicit false

namespace LiuWang.Proof.LocalAnalyticBounds

theorem exists_sharp_interval_away_from_finset (s : Finset Real) (T : Real) :
    ∃ H : Real, |H - T| ≤ 1 - 1 / ((s.card : Real) + 1) ∧
      ∀ x ∈ s, 1 / ((s.card : Real) + 1) ≤ |x - H| := by
  classical
  let d : Real := (s.card : Real) + 1
  let r : Real := 1 / d
  let grid : Fin (s.card + 1) → Real :=
    fun k => T - 1 + (2 * (k.val : Real) + 1) / d
  have hd : 0 < d := by dsimp [d]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hgrid : ∀ k, |grid k - T| ≤ 1 - r := by
    intro k
    have hk : (k.val : Real) ≤ (s.card : Real) := by
      exact_mod_cast (Nat.le_of_lt_succ k.isLt)
    have hlo : r ≤ (2 * (k.val : Real) + 1) / d := by
      exact div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := Real) k.val]) hd.le
    have hhi : (2 * (k.val : Real) + 1) / d ≤ 2 - r := by
      apply (div_le_iff₀ hd).mpr
      have hrd : r * d = 1 := by dsimp [r]; field_simp
      dsimp [d] at *
      nlinarith
    apply abs_le.mpr
    dsimp [grid]
    constructor <;> linarith
  by_cases hgood : ∃ k, ∀ x ∈ s, r ≤ |x - grid k|
  · obtain ⟨k, hk⟩ := hgood
    exact ⟨grid k, hgrid k, hk⟩
  have hbad : ∀ k, ∃ x : s, |(x : Real) - grid k| < r := by
    intro k
    by_contra hn
    apply hgood
    refine ⟨k, fun x hx => ?_⟩
    exact le_of_not_gt (fun h => hn ⟨⟨x, hx⟩, h⟩)
  let chosen : Fin (s.card + 1) → s := fun k => Classical.choose (hbad k)
  have hchosen : ∀ k, |(chosen k : Real) - grid k| < r :=
    fun k => Classical.choose_spec (hbad k)
  obtain ⟨k, l, hkl, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt chosen
    (by simp : Fintype.card s < Fintype.card (Fin (s.card + 1)))
  have hclose : |grid k - grid l| < 2 * r := by
    have hk := hchosen k
    have hl := hchosen l
    rw [← heq] at hl
    calc
      |grid k - grid l| ≤ |grid k - (chosen k : Real)| +
          |(chosen k : Real) - grid l| := abs_sub_le _ _ _
      _ < 2 * r := by rw [abs_sub_comm (grid k)]; linarith
  have hne : k.val ≠ l.val := fun h => hkl (Fin.ext h)
  have hgap : (1 : Real) ≤ |(k.val : Real) - (l.val : Real)| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hc : (k.val : Real) + 1 ≤ (l.val : Real) := by
        exact_mod_cast (Nat.succ_le_iff.mpr h)
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hc : (l.val : Real) + 1 ≤ (k.val : Real) := by
        exact_mod_cast (Nat.succ_le_iff.mpr h)
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hdiff : grid k - grid l =
      ((k.val : Real) - (l.val : Real)) * (2 * r) := by
    dsimp [grid, r]
    ring
  have hfar : 2 * r ≤ |grid k - grid l| := by
    rw [hdiff, abs_mul, abs_of_pos (by positivity : 0 < 2 * r)]
    simpa using mul_le_mul_of_nonneg_right hgap (by positivity : 0 ≤ 2 * r)
  exact False.elim (not_lt_of_ge hfar hclose)

end LiuWang.Proof.LocalAnalyticBounds
