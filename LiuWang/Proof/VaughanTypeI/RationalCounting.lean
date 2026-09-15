import LiuWang.Proof.VaughanTypeI.Geometric
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# 同一有理逼近见证下的逐块圆距离计数

以整数余量注入完成 q 长块上的计数，再排序支付固定截断核。
变截断核的分块总和位于独立的 `VariableKernel` 叶。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeI

open Finset AnalyticNumberTheory.LargeSieve

theorem distToInt_eq_abs_round (x : ℝ) :
    distToInt x = |x - (round x : ℤ)| :=
  (abs_sub_round_eq_min x).symm

private theorem card_int_abs_le (s : Finset ℤ) {c R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ z ∈ s, |(z : ℝ) + c| ≤ R) :
    (s.card : ℝ) ≤ 2 * R + 1 := by
  classical
  have hinj : Function.Injective (fun z : ℤ => (z : ℝ)) := Int.cast_injective
  have hcard := card_image_of_injective s hinj
  have h := sepCard_le_interval (-c - R) (2 * R) (by norm_num : (0 : ℝ) < 1)
    (by positivity) (s.image (fun z : ℤ => (z : ℝ))) (by
      intro x hx
      rcases mem_image.mp hx with ⟨z, hz, rfl⟩
      have hz' := abs_le.mp (hs z hz)
      constructor <;> linarith) (by
      intro x hx y hy hxy
      rcases mem_image.mp hx with ⟨z, hz, rfl⟩
      rcases mem_image.mp hy with ⟨w, hw, rfl⟩
      have hne : z - w ≠ 0 := by
        intro he
        exact hxy (by rw [sub_eq_zero.mp he])
      have habs := Int.one_le_abs hne
      exact_mod_cast habs)
  simpa only [hcard, div_one] using h

private def blockResidue (a q M : ℕ) (α : ℝ) (k : ℕ) : ℤ :=
  (a : ℤ) * k - (q : ℤ) * round (α * (M + k : ℕ))

private theorem blockResidue_injective {a q M : ℕ} {α : ℝ}
    (hcop : Nat.Coprime a q) :
    Set.InjOn (blockResidue a q M α) (Finset.range q) := by
  intro k hk l hl he
  have hdiv : (q : ℤ) ∣ ((a * l : ℕ) : ℤ) - ((a * k : ℕ) : ℤ) := by
    refine ⟨round (α * (M + l : ℕ)) - round (α * (M + k : ℕ)), ?_⟩
    dsimp [blockResidue] at he
    push_cast at he ⊢
    linear_combination -he
  have hm : Nat.ModEq q (a * k) (a * l) := Nat.modEq_iff_dvd.mpr hdiv
  have hc := hm.cancel_left_of_coprime hcop.symm
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hk),
    Nat.mod_eq_of_lt (mem_range.mp hl)] using hc

private theorem blockResidue_abs_le {a q M k : ℕ} {α θ r : ℝ}
    (hq : 0 < q) (hk : k < q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hr : distToInt (α * (M + k : ℕ)) ≤ r) :
    |(blockResidue a q M α k : ℝ) + (q : ℝ) * α * M| ≤ (q : ℝ) * r + 1 := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hkq : (k : ℝ) ≤ q := by exact_mod_cast hk.le
  have herr : |θ * (k : ℝ) / q| ≤ 1 := by
    simp only [abs_div, abs_mul, Nat.abs_cast, abs_of_pos hqp]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg k)) hqp.le).trans
      (by simpa using (div_le_one hqp).mpr hkq)
  have hid : (blockResidue a q M α k : ℝ) + (q : ℝ) * α * M =
      (q : ℝ) * (α * (M + k : ℕ) - (round (α * (M + k : ℕ)) : ℤ)) -
        θ * k / q := by
    unfold blockResidue
    push_cast
    rw [hα]
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |(q : ℝ) * (α * (M + k : ℕ) - (round (α * (M + k : ℕ)) : ℤ))| +
        |θ * k / q| := abs_sub _ _
    _ ≤ (q : ℝ) * r + 1 := by
      apply add_le_add _ herr
      rw [abs_mul, abs_of_pos hqp, ← distToInt_eq_abs_round]
      exact mul_le_mul_of_nonneg_left hr hqp.le

theorem rational_block_ball_card_le {a q M : ℕ} {α θ r : ℝ}
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) (hr : 0 ≤ r) :
    (((Finset.range q).filter
      (fun k => distToInt (α * (M + k : ℕ)) ≤ r)).card : ℝ) ≤
        2 * (q : ℝ) * r + 3 := by
  classical
  let s := (Finset.range q).filter (fun k => distToInt (α * (M + k : ℕ)) ≤ r)
  have hinj : Set.InjOn (blockResidue a q M α) s :=
    (blockResidue_injective hcop).mono (filter_subset _ _)
  have hc := card_image_iff.mpr hinj
  have hbound := card_int_abs_le (s.image (blockResidue a q M α))
    (c := (q : ℝ) * α * M) (R := (q : ℝ) * r + 1) (by positivity) (by
      intro z hz
      rcases mem_image.mp hz with ⟨k, hk, rfl⟩
      exact blockResidue_abs_le hq (mem_range.mp (mem_filter.mp hk).1) hθ hα
        (mem_filter.mp hk).2)
  rw [hc] at hbound
  dsimp [s] at hbound
  linarith

theorem truncatedKernel_le_length (T x : ℝ) : truncatedKernel T x ≤ T := by
  unfold truncatedKernel
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

private theorem fin_filter_card (q : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Fin q)).filter (fun i : Fin q => p i)).card =
      ((Finset.range q).filter p).card := by
  apply card_bij (i := fun (i : Fin q) _ => (i : ℕ))
  · intro i hi
    exact mem_filter.mpr ⟨mem_range.mpr i.isLt, (mem_filter.mp hi).2⟩
  · intro i _ j _ h
    exact Fin.ext h
  · intro i hi
    exact ⟨⟨i, mem_range.mp (mem_filter.mp hi).1⟩,
      mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩, rfl⟩

private theorem sum_kernel_le_of_ball_count (q : ℕ) (x : Fin q → ℝ)
    {T : ℝ} (hT : 0 ≤ T)
    (hc : ∀ r, 0 ≤ r →
      (((Finset.univ : Finset (Fin q)).filter
        (fun i => distToInt (x i) ≤ r)).card : ℝ) ≤ 2 * (q : ℝ) * r + 3) :
    (∑ i : Fin q, truncatedKernel T (x i)) ≤
      3 * T + (q : ℝ) * (1 + Real.log q) := by
  classical
  let σ := Tuple.sort (fun i => distToInt (x i))
  have hsort : Monotone (fun i => distToInt (x (σ i))) :=
    Tuple.monotone_sort (fun i => distToInt (x i))
  have hcard (r : ℝ) :
      ((Finset.univ : Finset (Fin q)).filter
        (fun i => distToInt (x (σ i)) ≤ r)).card =
      ((Finset.univ : Finset (Fin q)).filter
        (fun i => distToInt (x i) ≤ r)).card := by
    apply card_bij (i := fun i _ => σ i)
    · intro i hi
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
    · intro i _ j _ h
      exact σ.injective h
    · intro j hj
      refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
      simpa only [mem_filter, mem_univ, true_and, σ.apply_symm_apply] using (mem_filter.mp hj).2
  have hrank (i : Fin q) : (i : ℝ) + 1 ≤ 2 * (q : ℝ) * distToInt (x (σ i)) + 3 := by
    have hlt := (Tuple.lt_card_le_iff_apply_le_of_monotone hsort (j := i)).mpr le_rfl
    have hle : (i : ℝ) + 1 ≤
        (((Finset.univ : Finset (Fin q)).filter
          (fun j => distToInt (x (σ j)) ≤ distToInt (x (σ i)))).card : ℝ) := by
      exact_mod_cast hlt
    rw [hcard] at hle
    exact hle.trans (hc _ (distToInt_nonneg _))
  have hpoint (i : Fin q) :
      truncatedKernel T (x (σ i)) ≤
        if (i : ℕ) < 3 then T else (q : ℝ) / ((i : ℝ) - 2) := by
    split_ifs with hi
    · exact truncatedKernel_le_length _ _
    · have hi3 : 3 ≤ (i : ℕ) := Nat.le_of_not_gt hi
      have hip : (0 : ℝ) < (i : ℝ) - 2 := by
        have hiR : (3 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi3
        linarith
      have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hr := hrank i
      have hd : 0 < distToInt (x (σ i)) := by nlinarith
      rw [truncatedKernel, if_neg hd.ne']
      apply (min_le_right _ _).trans
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * distToInt (x (σ i))) hip).mpr
      nlinarith
  calc
    _ = ∑ i : Fin q, truncatedKernel T (x (σ i)) := (Equiv.sum_comp σ _).symm
    _ ≤ ∑ i : Fin q, if (i : ℕ) < 3 then T else (q : ℝ) / ((i : ℝ) - 2) :=
      sum_le_sum (fun i _ => hpoint i)
    _ = ∑ i ∈ range q, if i < 3 then T else (q : ℝ) / ((i : ℝ) - 2) :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < 3 then T else (q : ℝ) / ((i : ℝ) - 2)) q
    _ ≤ 3 * T + (q : ℝ) * (1 + Real.log q) := by
      by_cases hq : 3 ≤ q
      · rw [← sum_range_add_sum_Ico _ hq]
        have hfirst : (∑ i ∈ range 3, if i < 3 then T else (q : ℝ) / ((i : ℝ) - 2)) =
            3 * T := by
          norm_num [sum_range_succ]
          ring
        rw [hfirst]
        apply add_le_add_right
        have htail :
            (∑ i ∈ Ico 3 q, if i < 3 then T else (q : ℝ) / ((i : ℝ) - 2)) =
              (q : ℝ) * (harmonic (q - 3) : ℝ) := by
          calc
            _ = ∑ i ∈ Ico 3 q, (q : ℝ) / ((i : ℝ) - 2) := by
              apply sum_congr rfl
              intro i hi
              rw [if_neg (not_lt.mpr (mem_Ico.mp hi).1)]
            _ = ∑ j ∈ Icc 1 (q - 3), (q : ℝ) / j := by
              apply sum_bij (i := fun i _ => i - 2)
              · intro i hi
                simp only [mem_Ico, mem_Icc] at hi ⊢
                omega
              · intro i hi j hj h
                have := mem_Ico.mp hi
                have := mem_Ico.mp hj
                omega
              · intro j hj
                refine ⟨j + 2, ?_, by omega⟩
                simp only [mem_Icc, mem_Ico] at hj ⊢
                omega
              · intro i hi
                rw [Nat.cast_sub (by have := (mem_Ico.mp hi).1; omega), Nat.cast_ofNat]
            _ = _ := by
              simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
                mul_sum, div_eq_mul_inv]
        rw [htail]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact (harmonic_le_one_add_log (q - 3)).trans (by
          by_cases hz : q - 3 = 0
          · simp only [hz, Nat.cast_zero, Real.log_zero, add_zero]
            exact le_add_of_nonneg_right (Real.log_natCast_nonneg q)
          · exact add_le_add_right
              (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
                (by exact_mod_cast Nat.sub_le q 3)) _)
      · have hq3 : q ≤ 3 := Nat.le_of_lt (Nat.lt_of_not_ge hq)
        have he : (∑ i ∈ range q, if i < 3 then T else (q : ℝ) / ((i : ℝ) - 2)) =
            (q : ℝ) * T := by
          simp only [sum_ite_of_true (fun i hi => (mem_range.mp hi).trans_le hq3),
            sum_const, card_range, nsmul_eq_mul]
        rw [he]
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hq3) hT).trans
          (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (by
            linarith [Real.log_natCast_nonneg q])))

theorem rational_block_kernel_le {a q M : ℕ} {α θ T : ℝ}
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) (hT : 0 ≤ T) :
    (∑ k ∈ range q, truncatedKernel T (α * (M + k : ℕ))) ≤
      3 * T + (q : ℝ) * (1 + Real.log q) := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_kernel_le_of_ball_count q (fun i => α * (M + (i : ℕ) : ℕ)) hT
  intro r hr
  rw [fin_filter_card q (fun k => distToInt (α * (M + k : ℕ)) ≤ r)]
  exact rational_block_ball_card_le hq hcop hθ hα hr

/-- Public wrapper for the integer interval counting argument. -/
theorem card_int_abs_le_public (s : Finset ℤ) {c R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ z ∈ s, |(z : ℝ) + c| ≤ R) :
    (s.card : ℝ) ≤ 2 * R + 1 :=
  card_int_abs_le s hR hs

/-- Public wrapper for the sorted-distance harmonic kernel bound. -/
theorem sum_kernel_le_of_ball_count_public (q : ℕ) (x : Fin q → ℝ)
    {T : ℝ} (hT : 0 ≤ T)
    (hc : ∀ r, 0 ≤ r →
      (((Finset.univ : Finset (Fin q)).filter
        (fun i => distToInt (x i) ≤ r)).card : ℝ) ≤ 2 * (q : ℝ) * r + 3) :
    (∑ i : Fin q, truncatedKernel T (x i)) ≤
      3 * T + (q : ℝ) * (1 + Real.log q) :=
  sum_kernel_le_of_ball_count q x hT hc

end LiuWang.Proof.VaughanTypeI
