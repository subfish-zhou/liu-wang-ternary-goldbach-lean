import LiuWang.Proof.Campaign20260915.Density.RightFiniteMean
import LiuWang.Proof.NonprincipalDensityMeans.LogGaps

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.NonprincipalDensityMeans

namespace LiuWang.Proof.Campaign20260915.Density

theorem power_tail_integer {S : Finset ℕ} {N : ℕ} (hN : 0 < N)
    (hS : ∀ n ∈ S, N ≤ n) {d : ℝ} (hd : 0 < d) :
    (∑ n ∈ S, (n : ℝ) ^ (-(1 + d))) ≤ (N : ℝ) ^ (-d) * (1 + 1 / d) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(1 + d))) (Set.Ici (N : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
      (Set.Ici_subset_Ioi.mpr hN0)
  have ht := hanti.tsum_comp_add_le_integral N
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + d) < -1) hN0)
    (fun t ht => Real.rpow_nonneg (hN0.le.trans ht.le) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -(1 + d) < -1) hN0] at ht
  have hs := (summable_nat_add_iff N).mpr
    (Real.summable_nat_rpow.mpr (by linarith : -(1 + d) < -1))
  have he : (∑ n ∈ S, (n : ℝ) ^ (-(1 + d))) =
      ∑ k ∈ S.image (fun n => n - N), ((k + N : ℕ) : ℝ) ^ (-(1 + d)) := by
    rw [sum_image (fun a ha b hb hab => by have := hS a ha; have := hS b hb; omega)]
    exact sum_congr rfl (fun n hn => by rw [Nat.sub_add_cancel (hS n hn)])
  rw [he]
  have hsum := hs.sum_le_tsum (S.image (fun n => n - N)) (fun _ _ => by positivity)
  rw [hs.tsum_eq_zero_add] at hsum
  simp only [zero_add] at hsum
  have hp : (N : ℝ) ^ (-(1 + d)) ≤ (N : ℝ) ^ (-d) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  rw [show -(1 + d) + 1 = -d by ring, div_neg, neg_div, neg_neg] at ht
  have heq : (∑' b : ℕ, ((b + 1 + N : ℕ) : ℝ) ^ (-(1 + d))) =
      ∑' b : ℕ, ((b + N + 1 : ℕ) : ℝ) ^ (-(1 + d)) := by
    exact tsum_congr (fun _ => by congr 2; omega)
  rw [heq] at hsum
  simp only [div_eq_mul_inv] at ht ⊢
  nlinarith only [hsum, ht, hp]

theorem power_tail_real {S : Finset ℕ} {c d : ℝ} (hc : 1 ≤ c) (hd : 0 < d)
    (hS : ∀ n ∈ S, c ≤ (n : ℝ)) :
    (∑ n ∈ S, (n : ℝ) ^ (-(1 + d))) ≤ c ^ (-d) * (1 + 1 / d) := by
  have hN : 0 < ⌈c⌉₊ := by
    have : (1 : ℝ) ≤ ⌈c⌉₊ := hc.trans (Nat.le_ceil c)
    exact_mod_cast this
  exact (power_tail_integer hN (fun n hn => Nat.ceil_le.mpr (hS n hn)) hd).trans
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < c) (Nat.le_ceil c) (by linarith))
      (by positivity))

theorem residue_power_tail {q : ℕ} [NeZero q] {S : Finset ℕ} (x : ZMod q)
    {X d : ℝ} (hX : 2 * (q : ℝ) ≤ X) (hd : 0 < d) (hd1 : d ≤ 1)
    (hS : ∀ n ∈ S, X ≤ (n : ℝ)) :
    (∑ n ∈ fiber q S x, (n : ℝ) ^ (-(1 + d))) ≤
      (2 / q) * X ^ (-d) * (1 + 1 / d) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX0 : 0 < X := by linarith
  have hlow (n : ℕ) (hn : n ∈ fiber q S x) : q ≤ n := by
    have hr : (q : ℝ) ≤ n := by linarith [hS n (mem_filter.mp hn).1]
    exact_mod_cast hr
  have hquot (n : ℕ) (hn : n ∈ fiber q S x) : X / (2 * q) ≤ (n / q : ℕ) := by
    have hk : 0 < n / q := Nat.div_pos (hlow n hn) (NeZero.pos q)
    have hn' := Nat.mod_add_div n q
    have hr := Nat.mod_lt n (NeZero.pos q)
    have hmul : q ≤ q * (n / q) := by nlinarith
    have hh : n ≤ 2 * q * (n / q) := by nlinarith
    rw [div_le_iff₀ (by positivity : 0 < 2 * (q : ℝ))]
    have hh' : (n : ℝ) ≤ 2 * (q : ℝ) * (n / q : ℕ) := by exact_mod_cast hh
    nlinarith [hS n (mem_filter.mp hn).1]
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
    (show 1 ≤ X / (2 * q) by apply (le_div_iff₀ (by positivity)).mpr; simpa using hX)
    hd (fun k hk => by obtain ⟨n, hn, rfl⟩ := mem_image.mp hk; exact hquot n hn)
  have hh := hsum.trans (mul_le_mul_of_nonneg_left ht (by positivity))
  have he : (q : ℝ) ^ (-(1 + d)) * (X / (2 * q)) ^ (-d) =
      (2 : ℝ) ^ d / q * X ^ (-d) := by
    rw [Real.div_rpow hX0.le (by positivity : 0 ≤ 2 * (q : ℝ)),
      Real.rpow_neg (by positivity : 0 ≤ 2 * (q : ℝ)), div_inv_eq_mul,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hq0.le]
    calc
      _ = (2 : ℝ) ^ d * X ^ (-d) *
          ((q : ℝ) ^ (-(1 + d)) * (q : ℝ) ^ d) := by ring
      _ = _ := by
        rw [← Real.rpow_add hq0, show -(1 + d) + d = -1 by ring, Real.rpow_neg_one]
        ring
  rw [← mul_assoc, he] at hh
  have htwo : (2 : ℝ) ^ d ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hd1
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right htwo hq0.le) (by positivity))
    (by positivity))

#print axioms residue_power_tail

end LiuWang.Proof.Campaign20260915.Density
