import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.ConductorSum

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier

theorem reciprocal_totient_ten :
    (∑ k ∈ Icc 1 (10 : ℕ), 1/(k.totient : ℝ)^2) ≤ 3 := by
  norm_num [sum_Icc_succ_top, Nat.totient, range_add_one, filter_insert, filter_singleton,
    Nat.coprime_iff_gcd_eq_one]

theorem reciprocal_totient_seven (X : ℕ) :
    (∑ k ∈ Icc 1 X, 1/(k.totient : ℝ)^2) ≤ 7 := by
  by_cases hX : X ≤ 10
  · have h := sum_le_sum_of_subset_of_nonneg
      (f := fun k : ℕ => 1/(k.totient : ℝ)^2) (s := Icc 1 X) (t := Icc 1 10)
      (Icc_subset_Icc le_rfl hX) (by intros; positivity)
    linarith [reciprocal_totient_ten]
  · have he : (∑ k ∈ Icc 1 X, 1/(k.totient : ℝ)^2) =
        (∑ k ∈ Icc 1 (10 : ℕ), 1/(k.totient : ℝ)^2) +
        ∑ k ∈ Icc 11 X, 1/(k.totient : ℝ)^2 := by
      have h := sum_Ico_consecutive (fun k : ℕ => 1/(k.totient : ℝ)^2)
        (show 1 ≤ 11 by omega) (show 11 ≤ X+1 by omega)
      have hcc (a b : ℕ) : Ico a (b+1) = Icc a b := by ext k; simp
      simpa only [hcc] using h.symm
    rw [he]
    have ht := Uniform.inverse_totient_tail_finite (m := 11) (B := X) (by omega)
    norm_num only [Nat.cast_ofNat, show (44 : ℝ)/11 = 4 by norm_num] at ht
    linarith [reciprocal_totient_ten]

theorem reciprocal_totient_multiples_seven (X : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ Icc 1 X, if d ∣ q then 1/(q.totient : ℝ)^2 else 0) ≤
      7/(d.totient : ℝ)^2 := by
  rw [Uniform.sum_multiples _ X hd]
  have hφ : 0 < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd)
  calc
    _ ≤ ∑ k ∈ Icc 1 (X/d), (1/(d.totient : ℝ)^2) * (1/(k.totient : ℝ)^2) := by
      apply sum_le_sum
      intro k hk
      have hk0 : 0 < (k.totient : ℝ) :=
        Nat.cast_pos.mpr (Nat.totient_pos.mpr (mem_Icc.mp hk).1)
      have he : (d.totient : ℝ)*(k.totient : ℝ) ≤ ((d*k).totient : ℝ) := by
        exact_mod_cast Nat.totient_super_multiplicative d k
      have h := one_div_le_one_div_of_le (sq_pos_of_pos (mul_pos hφ hk0))
        (pow_le_pow_left₀ (mul_nonneg hφ.le hk0.le) he 2)
      simpa only [mul_pow, one_div, mul_inv] using h
    _ = (1/(d.totient : ℝ)^2) *
        ∑ k ∈ Icc 1 (X/d), 1/(k.totient : ℝ)^2 := (mul_sum ..).symm
    _ ≤ (1/(d.totient : ℝ)^2) * 7 :=
      mul_le_mul_of_nonneg_left (reciprocal_totient_seven _) (by positivity)
    _ = _ := by ring

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier
