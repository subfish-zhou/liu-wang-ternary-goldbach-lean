import LiuWang.Proof.SingularSeries.Uniform.Consumer

/-! Local factor comparison and finite cubic tails, without prime enumeration. -/

set_option autoImplicit false
noncomputable section
open Finset

namespace LiuWang.Proof.SingularSeries.Decimal

def a (t : ℝ) : ℝ := 1 - 1 / (t - 1) ^ 2

def b (t : ℝ) : ℝ := 1 - 1 / t ^ 2

theorem b_pos {t : ℝ} (ht : 1 < t) : 0 < b t := by
  unfold b
  have ht0 : 0 < t := by linarith
  have : 1 < t ^ 2 := by nlinarith
  have := (div_lt_one (sq_pos_of_pos ht0)).mpr this
  linarith

theorem b_le_one (t : ℝ) : b t ≤ 1 := by
  unfold b
  exact sub_le_self _ (by positivity)

theorem a_pos {t : ℝ} (ht : 2 < t) : 0 < a t := by
  exact b_pos (by linarith : 1 < t - 1)

theorem local_comparison {t : ℝ} (ht : 5 ≤ t) :
    b t * (1 - 3 / t ^ 3) ≤ a t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - 1 := by linarith
  have hid :
      (a t - b t * (1 - 3 / t ^ 3)) * (t ^ 5 * (t - 1) ^ 2) =
        t ^ 3 * (t - 5) + 6 * t - 3 := by
    unfold a b
    field_simp
    ring
  have hr : 0 ≤ t ^ 3 * (t - 5) + 6 * t - 3 := by
    have := mul_nonneg (pow_nonneg ht0.le 3) (sub_nonneg.mpr ht)
    linarith
  have hden : 0 < t ^ 5 * (t - 1) ^ 2 := by positivity
  have := (mul_nonneg_iff_of_pos_right hden).mp (hid.symm ▸ hr)
  linarith

theorem odd_cube_step {k : ℕ} (hk : 0 < k) :
    1 / (2 * (k : ℝ) + 1) ^ 3 ≤
      (1 / 16 : ℝ) * (1 / (k : ℝ) ^ 2 - 1 / ((k : ℝ) + 1) ^ 2) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hid :
      (2 * (k : ℝ) + 1) ^ 4 - 16 * (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 =
        8 * (k : ℝ) ^ 2 + 8 * (k : ℝ) + 1 := by ring
  have hpoly : 16 * (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 ≤
      (2 * (k : ℝ) + 1) ^ 4 := by nlinarith
  field_simp
  nlinarith

theorem odd_cube_interval {m B : ℕ} (hm : 0 < m) (hB : m ≤ B) :
    (∑ k ∈ Icc m B, 1 / (2 * (k : ℝ) + 1) ^ 3) ≤
      (1 / 16 : ℝ) * (1 / (m : ℝ) ^ 2 - 1 / ((B : ℝ) + 1) ^ 2) := by
  induction B, hB using Nat.le_induction with
  | base => simpa using odd_cube_step hm
  | succ B hB ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hs := odd_cube_step (show 0 < B + 1 by omega)
    push_cast at hs ⊢
    linarith

theorem odd_cube_finite {m : ℕ} (hm : 0 < m) (s : Finset ℕ)
    (hs : ∀ k ∈ s, m ≤ k) :
    (∑ k ∈ s, 1 / (2 * (k : ℝ) + 1) ^ 3) ≤ 1 / (16 * (m : ℝ) ^ 2) := by
  by_cases he : s.Nonempty
  · let B := s.sup id
    have hB : m ≤ B := by
      obtain ⟨k, hk⟩ := he
      exact (hs k hk).trans (le_sup (f := id) hk)
    calc
      _ ≤ ∑ k ∈ Icc m B, 1 / (2 * (k : ℝ) + 1) ^ 3 :=
        sum_le_sum_of_subset_of_nonneg
          (fun k hk => mem_Icc.mpr ⟨hs k hk, le_sup (f := id) hk⟩) (by intros; positivity)
      _ ≤ (1 / 16 : ℝ) * (1 / (m : ℝ) ^ 2 - 1 / ((B : ℝ) + 1) ^ 2) :=
        odd_cube_interval hm hB
      _ ≤ _ := by
        calc
          _ ≤ (1 / 16 : ℝ) * (1 / (m : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by norm_num)
          _ = _ := by ring
  · simp only [not_nonempty_iff_eq_empty.mp he, sum_empty]
    positivity

theorem odd_tail_finite (s : Finset ℕ)
    (hs : ∀ n ∈ s, 100 < n ∧ Odd n) :
    (∑ n ∈ s, 1 / (n : ℝ) ^ 3) ≤ (1 / 40000 : ℝ) := by
  have he (n : ℕ) (hn : n ∈ s) : n = 2 * (n / 2) + 1 := by
    obtain ⟨k, hk⟩ := (hs n hn).2
    omega
  have hi : Set.InjOn (fun n : ℕ => n / 2) s := by
    intro n hn j hj h
    dsimp only at h
    have := he n hn
    have := he j hj
    omega
  have hm : ∀ k ∈ s.image (fun n => n / 2), 50 ≤ k := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    have := (hs n hn).1
    omega
  calc
    _ = ∑ k ∈ s.image (fun n => (n / 2 : ℕ)), 1 / (2 * (k : ℝ) + 1) ^ 3 := by
      rw [sum_image hi]
      apply sum_congr rfl
      intro n hn
      have hr : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast he n hn
      rw [hr]
    _ ≤ 1 / (16 * (50 : ℝ) ^ 2) := odd_cube_finite (by norm_num) _ hm
    _ = _ := by norm_num

theorem one_sub_sum_le_prod (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ n ∈ s, 0 ≤ f n ∧ f n ≤ 1) :
    1 - ∑ n ∈ s, f n ≤ ∏ n ∈ s, (1 - f n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
    rw [sum_insert hn, prod_insert hn]
    have hn' := hf n (mem_insert_self n s)
    have hs : ∀ j ∈ s, 0 ≤ f j ∧ f j ≤ 1 :=
      fun j hj => hf j (mem_insert_of_mem hj)
    have hsum := sum_nonneg (fun j hj => (hs j hj).1)
    have h := mul_le_mul_of_nonneg_left (ih hs) (sub_nonneg.mpr hn'.2)
    nlinarith [mul_nonneg hn'.1 hsum]

theorem prime_correction_lower (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 100 < p) :
    1 - (3 / 40000 : ℝ) ≤ ∏ p ∈ s, (1 - 3 / (p : ℝ) ^ 3) := by
  have hsum := odd_tail_finite s (by
    intro p hp
    obtain ⟨hp', h100⟩ := hs p hp
    exact ⟨h100, hp'.odd_of_ne_two (by omega)⟩)
  have hf : ∀ p ∈ s, 0 ≤ 3 / (p : ℝ) ^ 3 ∧ 3 / (p : ℝ) ^ 3 ≤ 1 := by
    intro p hp
    have hpR : (100 : ℝ) < p := by exact_mod_cast (hs p hp).2
    constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < (p : ℝ) ^ 3)).mpr
      nlinarith [sq_nonneg (p : ℝ)]
  have h := one_sub_sum_le_prod s (fun p => 3 / (p : ℝ) ^ 3) hf
  have he : (∑ p ∈ s, 3 / (p : ℝ) ^ 3) =
      3 * ∑ p ∈ s, 1 / (p : ℝ) ^ 3 := by rw [mul_sum]; congr 1; ext p; ring
  rw [he] at h
  linarith

end LiuWang.Proof.SingularSeries.Decimal
