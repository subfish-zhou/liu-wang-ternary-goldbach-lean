import LiuWang.Proof.Campaign20260915.Density.ResidueTail

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.NonprincipalDensityMeans

namespace LiuWang.Proof.Campaign20260915.Density

theorem residue_power_tail_sharp {q : ℕ} [NeZero q] {S : Finset ℕ} (x : ZMod q)
    {X d : ℝ} (hX : 11 * (q : ℝ) ≤ X) (hd : 0 < d) (hd1 : d ≤ 1)
    (hS : ∀ n ∈ S, X ≤ (n : ℝ)) :
    (∑ n ∈ fiber q S x, (n : ℝ) ^ (-(1 + d))) ≤
      (1.1 / q) * X ^ (-d) * (1 + 1 / d) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX0 : 0 < X := by linarith
  have hlow (n : ℕ) (hn : n ∈ fiber q S x) : q ≤ n := by
    have hr : (q : ℝ) ≤ n := by linarith [hS n (mem_filter.mp hn).1]
    exact_mod_cast hr
  have hquot (n : ℕ) (hn : n ∈ fiber q S x) : X / (1.1 * q) ≤ (n / q : ℕ) := by
    have hn' : (n : ℝ) = (n % q : ℕ) + (q : ℝ) * (n / q : ℕ) := by
      exact_mod_cast (Nat.mod_add_div n q).symm
    have hr : ((n % q : ℕ) : ℝ) < q := Nat.cast_lt.mpr (Nat.mod_lt n (NeZero.pos q))
    rw [div_le_iff₀ (by positivity : 0 < 1.1 * (q : ℝ))]
    nlinarith only [hn', hr, hX, hS n (mem_filter.mp hn).1]
  have hpoint (n : ℕ) (hn : n ∈ fiber q S x) :
      (n : ℝ) ^ (-(1 + d)) ≤ (q : ℝ) ^ (-(1 + d)) *
        ((n / q : ℕ) : ℝ) ^ (-(1 + d)) := by
    rw [← Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg (n / q))]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hq0 (Nat.cast_pos.mpr
      (Nat.div_pos (hlow n hn) (NeZero.pos q))))
      (by exact_mod_cast Nat.mul_div_le n q) (by linarith)
  have hsum := sum_le_sum hpoint
  rw [← mul_sum] at hsum
  have himage :
      (∑ n ∈ fiber q S x, ((n / q : ℕ) : ℝ) ^ (-(1 + d))) =
      ∑ k ∈ (fiber q S x).image (fun n => n / q), (k : ℝ) ^ (-(1 + d)) := by
    rw [sum_image (quotient_inj_on_fiber q S x)]
  rw [himage] at hsum
  have ht := power_tail_real
    (show 1 ≤ X / (1.1 * q) by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith)
    hd (fun k hk => by obtain ⟨n, hn, rfl⟩ := mem_image.mp hk; exact hquot n hn)
  have hh := hsum.trans (mul_le_mul_of_nonneg_left ht (by positivity))
  have he : (q : ℝ) ^ (-(1 + d)) * (X / (1.1 * q)) ^ (-d) =
      (1.1 : ℝ) ^ d / q * X ^ (-d) := by
    rw [Real.div_rpow hX0.le (by positivity : 0 ≤ 1.1 * (q : ℝ)),
      Real.rpow_neg (by positivity : 0 ≤ 1.1 * (q : ℝ)), div_inv_eq_mul,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1.1) hq0.le]
    calc
      _ = (1.1 : ℝ) ^ d * X ^ (-d) *
          ((q : ℝ) ^ (-(1 + d)) * (q : ℝ) ^ d) := by ring
      _ = _ := by
        rw [← Real.rpow_add hq0, show -(1 + d) + d = -1 by ring, Real.rpow_neg_one]
        ring
  rw [← mul_assoc, he] at hh
  have hsmall : (1.1 : ℝ) ^ d ≤ 1.1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 1.1) hd1
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsmall hq0.le) (by positivity))
    (by positivity))

end LiuWang.Proof.Campaign20260915.Density
