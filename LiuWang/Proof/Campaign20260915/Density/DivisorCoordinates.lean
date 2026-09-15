import LiuWang.Proof.Campaign20260915.Density.RightCoefficients
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.NatDivisors

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators

namespace LiuWang.Proof.Campaign20260915.Density

def divisorQuad (x : Σ _n : ℕ, ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let g := Nat.gcd x.2.1 x.2.2
  (g, x.2.1 / g, x.2.2 / g, x.1 / Nat.lcm x.2.1 x.2.2)

def quadProduct (x : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  x.1 * x.2.1 * x.2.2.1 * x.2.2.2

theorem divisorQuad_recover {n a b : ℕ} (hn : 0 < n)
    (ha : a ∣ n) (hb : b ∣ n) :
    let v := divisorQuad ⟨n, (a, b)⟩
    v.1 * v.2.1 = a ∧ v.1 * v.2.2.1 = b ∧ quadProduct v = n := by
  have hga := Nat.gcd_dvd_left a b
  have hgb := Nat.gcd_dvd_right a b
  have hg : 0 < Nat.gcd a b :=
    Nat.gcd_pos_of_pos_left b (Nat.pos_of_dvd_of_pos ha hn)
  have he : Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) =
      Nat.lcm a b := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      _ = (Nat.gcd a b * (a / Nat.gcd a b)) *
          (Nat.gcd a b * (b / Nat.gcd a b)) := by ring
      _ = a * b := by rw [Nat.mul_div_cancel' hga, Nat.mul_div_cancel' hgb]
      _ = _ := (Nat.gcd_mul_lcm a b).symm
  dsimp [divisorQuad, quadProduct]
  exact ⟨Nat.mul_div_cancel' hga, Nat.mul_div_cancel' hgb,
    by rw [he, Nat.mul_div_cancel' (Nat.lcm_dvd ha hb)]⟩

theorem divisorQuad_pos {n a b : ℕ} (hn : 0 < n)
    (ha : a ∣ n) (hb : b ∣ n) :
    let v := divisorQuad ⟨n, (a, b)⟩
    0 < v.1 ∧ 0 < v.2.1 ∧ 0 < v.2.2.1 ∧ 0 < v.2.2.2 := by
  have he := (divisorQuad_recover hn ha hb).2.2
  have h : quadProduct (divisorQuad ⟨n, (a, b)⟩) ≠ 0 := by
    rw [he]
    exact hn.ne'
  simp only [quadProduct, mul_ne_zero_iff] at h
  exact ⟨Nat.pos_of_ne_zero h.1.1.1, Nat.pos_of_ne_zero h.1.1.2,
    Nat.pos_of_ne_zero h.1.2, Nat.pos_of_ne_zero h.2⟩

theorem quad_factors_le {v : ℕ × ℕ × ℕ × ℕ}
    (hv : 0 < v.1 ∧ 0 < v.2.1 ∧ 0 < v.2.2.1 ∧ 0 < v.2.2.2) :
    v.1 ≤ quadProduct v ∧ v.2.1 ≤ quadProduct v ∧
      v.2.2.1 ≤ quadProduct v ∧ v.2.2.2 ≤ quadProduct v := by
  have hp : 0 < quadProduct v := by
    dsimp [quadProduct]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hv.1 hv.2.1) hv.2.2.1) hv.2.2.2
  refine ⟨Nat.le_of_dvd hp ?_, Nat.le_of_dvd hp ?_,
    Nat.le_of_dvd hp ?_, Nat.le_of_dvd hp ?_⟩
  · exact ⟨v.2.1 * v.2.2.1 * v.2.2.2, by simp [quadProduct, mul_assoc]⟩
  · exact ⟨v.1 * v.2.2.1 * v.2.2.2, by dsimp [quadProduct]; ring⟩
  · exact ⟨v.1 * v.2.1 * v.2.2.2, by dsimp [quadProduct]; ring⟩
  · exact ⟨v.1 * v.2.1 * v.2.2.1, by dsimp [quadProduct]; ring⟩

theorem large_divisor_square_weight_le (X : ℕ) (y : ℝ)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    (∑ n ∈ Icc 1 X, ((largeDivisors y n).card : ℝ) ^ 2 * w n) ≤
      ∑ g ∈ Icc 1 X, ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, ∑ k ∈ Icc 1 X,
        if y ≤ (g * a : ℕ) ∧ y ≤ (g * b : ℕ) then w (g * a * b * k) else 0 := by
  classical
  let D := (Icc 1 X).sigma (fun n => (largeDivisors y n).product (largeDivisors y n))
  let R := ((Icc 1 X).product ((Icc 1 X).product ((Icc 1 X).product (Icc 1 X)))).filter
    (fun v => y ≤ (v.1 * v.2.1 : ℕ) ∧ y ≤ (v.1 * v.2.2.1 : ℕ))
  have hmem {x : Σ _n : ℕ, ℕ × ℕ} (hx : x ∈ D) :
      0 < x.1 ∧ x.1 ≤ X ∧ x.2.1 ∣ x.1 ∧ x.2.2 ∣ x.1 ∧
        y ≤ (x.2.1 : ℝ) ∧ y ≤ (x.2.2 : ℝ) := by
    obtain ⟨hn, hab⟩ := mem_sigma.mp hx
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    have hn' := mem_Icc.mp hn
    have ha' := mem_filter.mp ha
    have hb' := mem_filter.mp hb
    exact ⟨hn'.1, hn'.2, (Nat.mem_divisors.mp ha'.1).1,
      (Nat.mem_divisors.mp hb'.1).1, ha'.2, hb'.2⟩
  have hsub : D.image divisorQuad ⊆ R := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
    obtain ⟨hn, hnX, ha, hb, hya, hyb⟩ := hmem hx
    have hr := divisorQuad_recover hn ha hb
    have hp := divisorQuad_pos hn ha hb
    have hl := quad_factors_le hp
    rw [hr.2.2] at hl
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hp.1, hl.1.trans hnX⟩,
      mem_product.mpr ⟨mem_Icc.mpr ⟨hp.2.1, hl.2.1.trans hnX⟩,
        mem_product.mpr ⟨mem_Icc.mpr ⟨hp.2.2.1, hl.2.2.1.trans hnX⟩,
          mem_Icc.mpr ⟨hp.2.2.2, hl.2.2.2.trans hnX⟩⟩⟩⟩,
      by simpa only [hr.1, hr.2.1] using And.intro hya hyb⟩
  have hinj : Set.InjOn divisorQuad D := by
    intro x hx z hz he
    obtain ⟨hn, _, ha, hb, _⟩ := hmem hx
    obtain ⟨hm, _, hc, hd, _⟩ := hmem hz
    have hx' := divisorQuad_recover hn ha hb
    have hz' := divisorQuad_recover hm hc hd
    have hn' : x.1 = z.1 := by
      rw [← hx'.2.2, ← hz'.2.2, he]
    have ha' : x.2.1 = z.2.1 := by rw [← hx'.1, ← hz'.1, he]
    have hb' : x.2.2 = z.2.2 := by rw [← hx'.2.1, ← hz'.2.1, he]
    exact Sigma.ext hn' (heq_of_eq (Prod.ext ha' hb'))
  have he : (∑ n ∈ Icc 1 X, ((largeDivisors y n).card : ℝ) ^ 2 * w n) =
      ∑ x ∈ D.image divisorQuad, w (quadProduct x) := by
    rw [sum_image hinj]
    have hr : (∑ x ∈ D, w (quadProduct (divisorQuad x))) = ∑ x ∈ D, w x.1 :=
      sum_congr rfl (fun x hx => by
        obtain ⟨hn, _, ha, hb, _⟩ := hmem hx
        rw [(divisorQuad_recover hn ha hb).2.2])
    rw [hr]
    simp [D, sum_sigma, pow_two, mul_assoc]
  rw [he]
  have h := sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hw (quadProduct x))
  apply h.trans_eq
  simp only [R, sum_filter, product_eq_sprod, Finset.sum_product, quadProduct]

#print axioms large_divisor_square_weight_le

end LiuWang.Proof.Campaign20260915.Density
