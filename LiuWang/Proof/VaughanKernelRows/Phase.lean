import LiuWang.Proof.VaughanTypeI.RationalCounting

/-!
# 任意实相位的有理逼近块界

整数余量的中心为 `q * β`，不要求相位来自自然数平移。
计数与排序分别复用第一类叶的两个公开薄封装；共振仍取完整截断值。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanKernelRows

open Finset AnalyticNumberTheory.LargeSieve VaughanTypeI

private def phaseResidue (a q : ℕ) (α β : ℝ) (k : ℕ) : ℤ :=
  (a : ℤ) * k - (q : ℤ) * round (α * k + β)

private theorem phaseResidue_injective {a q : ℕ} {α β : ℝ}
    (hcop : Nat.Coprime a q) :
    Set.InjOn (phaseResidue a q α β) (range q) := by
  intro k hk l hl he
  have hdiv : (q : ℤ) ∣ ((a * l : ℕ) : ℤ) - ((a * k : ℕ) : ℤ) := by
    refine ⟨round (α * l + β) - round (α * k + β), ?_⟩
    dsimp [phaseResidue] at he
    push_cast at he ⊢
    linear_combination -he
  have hm : Nat.ModEq q (a * k) (a * l) := Nat.modEq_iff_dvd.mpr hdiv
  have hc := hm.cancel_left_of_coprime hcop.symm
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hk),
    Nat.mod_eq_of_lt (mem_range.mp hl)] using hc

private theorem phaseResidue_abs_le {a q k : ℕ} {α β θ r : ℝ}
    (hq : 0 < q) (hk : k < q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hr : distToInt (α * k + β) ≤ r) :
    |(phaseResidue a q α β k : ℝ) + (q : ℝ) * β| ≤ (q : ℝ) * r + 1 := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hkq : (k : ℝ) ≤ q := by exact_mod_cast hk.le
  have herr : |θ * (k : ℝ) / q| ≤ 1 := by
    simp only [abs_div, abs_mul, Nat.abs_cast, abs_of_pos hqp]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg k)) hqp.le).trans
      (by simpa using (div_le_one hqp).mpr hkq)
  have hid : (phaseResidue a q α β k : ℝ) + (q : ℝ) * β =
      (q : ℝ) * (α * k + β - (round (α * k + β) : ℤ)) -
        θ * k / q := by
    unfold phaseResidue
    push_cast
    rw [hα]
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |(q : ℝ) * (α * k + β - (round (α * k + β) : ℤ))| +
        |θ * k / q| := abs_sub _ _
    _ ≤ (q : ℝ) * r + 1 := by
      apply add_le_add _ herr
      rw [abs_mul, abs_of_pos hqp, ← distToInt_eq_abs_round]
      exact mul_le_mul_of_nonneg_left hr hqp.le

theorem rational_phase_ball_card_le {a q : ℕ} {α β θ r : ℝ}
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) (hr : 0 ≤ r) :
    (((range q).filter (fun k : ℕ => distToInt (α * k + β) ≤ r)).card : ℝ) ≤
      2 * (q : ℝ) * r + 3 := by
  classical
  let s := (range q).filter (fun k : ℕ => distToInt (α * k + β) ≤ r)
  have hinj : Set.InjOn (phaseResidue a q α β) s :=
    (phaseResidue_injective hcop).mono (filter_subset _ _)
  have hc := card_image_iff.mpr hinj
  have hbound := card_int_abs_le_public (s.image (phaseResidue a q α β))
    (c := (q : ℝ) * β) (R := (q : ℝ) * r + 1) (by positivity) (by
      intro z hz
      rcases mem_image.mp hz with ⟨k, hk, rfl⟩
      exact phaseResidue_abs_le hq (mem_range.mp (mem_filter.mp hk).1) hθ hα
        (mem_filter.mp hk).2)
  rw [hc] at hbound
  dsimp [s] at hbound
  linarith

theorem rational_phase_kernel_le {a q : ℕ} {α β θ T : ℝ}
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) (hT : 0 ≤ T) :
    (∑ k ∈ range q, truncatedKernel T (α * k + β)) ≤
      3 * T + (q : ℝ) * (1 + Real.log q) := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_kernel_le_of_ball_count_public q (fun i => α * i + β) hT
  intro r hr
  have hc :
      ((univ : Finset (Fin q)).filter (fun i : Fin q => distToInt (α * i + β) ≤ r)).card =
        ((range q).filter (fun k : ℕ => distToInt (α * k + β) ≤ r)).card := by
    apply card_bij (i := fun (i : Fin q) _ => (i : ℕ))
    · intro i hi
      exact mem_filter.mpr ⟨mem_range.mpr i.isLt, (mem_filter.mp hi).2⟩
    · intro i _ j _ h
      exact Fin.ext h
    · intro i hi
      exact ⟨⟨i, mem_range.mp (mem_filter.mp hi).1⟩,
        mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩, rfl⟩
  rw [hc]
  exact rational_phase_ball_card_le hq hcop hθ hα hr

end LiuWang.Proof.VaughanKernelRows
