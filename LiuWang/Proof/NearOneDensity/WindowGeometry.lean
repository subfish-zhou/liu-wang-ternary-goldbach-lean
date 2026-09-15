import LiuWang.Proof.NearOneDensity.PrincipalWindows

set_option autoImplicit false
noncomputable section

open Classical

namespace LiuWang.Proof.NearOneDensity

theorem window_log_height {Q x y z b t γ : ℝ}
    (hQ : 0 < Q) (hQx : Q ≤ x) (hy : 1 ≤ y)
    (hz : 100000000000 ≤ z) (hxy : x * y ≤ z)
    (hb : 0 ≤ b) (hbmax : b ≤ 2.04)
    (hγ : |γ| ≤ y) (ht : |γ - t| ≤ b / Real.log z) :
    Real.log Q + Real.log (max 1 |t|) ≤ Real.log z + 1 / 10 := by
  have hL : 25 ≤ Real.log z := by linarith [source_log_lower hz]
  have hL0 : 0 < Real.log z := by linarith
  have hsmall : b / Real.log z ≤ 1 / 10 :=
    (div_le_iff₀ hL0).mpr (by linarith)
  have hδ : 0 ≤ b / Real.log z := div_nonneg hb hL0.le
  have ht' : |t| ≤ y + b / Real.log z := by
    have hh := abs_add_le γ (t - γ)
    rw [add_sub_cancel] at hh
    rw [abs_sub_comm] at ht
    linarith
  have hmax : max 1 |t| ≤ y * (1 + b / Real.log z) := by
    have hh := mul_le_mul_of_nonneg_right hy hδ
    apply max_le
    · nlinarith
    · nlinarith
  have hprod : Q * max 1 |t| ≤ z * (1 + b / Real.log z) := by
    calc
      Q * max 1 |t| ≤ x * (y * (1 + b / Real.log z)) :=
        mul_le_mul hQx hmax (by positivity) (hQ.trans_le hQx).le
      _ = (x * y) * (1 + b / Real.log z) := by ring
      _ ≤ z * (1 + b / Real.log z) :=
        mul_le_mul_of_nonneg_right hxy (by positivity)
  have hz0 : 0 < z := by linarith
  have hm0 : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hfac : 0 < 1 + b / Real.log z := by positivity
  have hh := Real.log_le_log (mul_pos hQ hm0) hprod
  rw [Real.log_mul hQ.ne' hm0.ne', Real.log_mul hz0.ne' hfac.ne'] at hh
  have hl := Real.log_le_sub_one_of_pos hfac
  linarith

theorem source_row_window_count_of_one_le_height (r : DensityRow) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x y z lam : ℝ}
    (hqx : (q : ℝ) ≤ x) (hy : 1 ≤ y) (hz : 100000000000 ≤ z) (hxy : x * y ≤ z)
    (hlam : 0 ≤ lam) (hlam₁ : lam ≤ rowLambda r) (t : ℝ) :
    ((zeroFamily q (1 - lam / Real.log z) y).filter
      (fun p => p.1 = χ ∧ |p.2.1.im - t| ≤ rowRadius r / Real.log z)).card ≤
        rowMultiplicity r := by
  rw [← ordinaryWindowCount_eq_family_filter]
  let v := ordinaryWindowValues χ (1 - lam / Real.log z) y t (rowRadius r / Real.log z)
  by_cases he : v = ∅
  · change (∑ ρ ∈ v, analyticOrderNatAt χ.LFunction ρ) ≤ _
    simp [he]
  obtain ⟨ρ, hρ⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hmax : rowLambda r ≤ 0.5 := by cases r <;> norm_num [rowLambda]
  have hα := source_alpha_ge_half hz (hlam₁.trans hmax)
  have hm := (mem_zeroValues hα).mp (Finset.mem_filter.mp hρ).1
  have hQ : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hh := window_log_height hQ hqx hy hz hxy (rowRadius_nonneg r)
    (row_window_certificate r).2.2.2.1 hm.2.2.2 (Finset.mem_filter.mp hρ).2
  by_cases hχ : χ = 1
  · subst χ
    apply principal_row_window_count r hz hlam hlam₁
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
    have hlog := Real.log_nonneg hq
    linarith
  · apply nonprincipal_row_window_count r χ hχ hz hlam hlam₁
    have hd : χ.conductor ≤ q := Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
    have hd0 : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
    have hlog := Real.log_le_log hd0 (show (χ.conductor : ℝ) ≤ q by exact_mod_cast hd)
    linarith

theorem source_row_window_count_effective_height (r : DensityRow) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {y z lam : ℝ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0 ≤ lam) (hlam₁ : lam ≤ rowLambda r) (t : ℝ) :
    ((zeroFamily q (1 - lam / Real.log z) y).filter
      (fun p => p.1 = χ ∧ |p.2.1.im - t| ≤ rowRadius r / Real.log z)).card ≤
        rowMultiplicity r := by
  have hmax : rowLambda r ≤ 0.5 := by cases r <;> norm_num [rowLambda]
  have hα := source_alpha_ge_half hz (hlam₁.trans hmax)
  have hsub : zeroFamily q (1 - lam / Real.log z) y ⊆
      zeroFamily q (1 - lam / Real.log z) (max 1 y) := by
    intro p hp
    have hh := (mem_zeroFamily hα p).mp hp
    exact (mem_zeroFamily hα p).mpr
      ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.trans (le_max_right _ _)⟩
  exact (Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans
    (source_row_window_count_of_one_le_height r χ le_rfl (le_max_left _ _) hz hqy
      hlam hlam₁ t)

end LiuWang.Proof.NearOneDensity
