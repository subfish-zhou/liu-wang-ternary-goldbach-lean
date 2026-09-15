import LiuWang.Proof.SourceRoute.MajorException.Continuation.HeadPrecision
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

def totientMoment (X : ℕ) (s : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 X, (q:ℝ)^s / (q.totient:ℝ)^2

theorem totientMoment_nonneg (X : ℕ) (s : ℝ) : 0 ≤ totientMoment X s :=
  sum_nonneg (fun _ _ => by positivity)

theorem totientMoment_multiples (X : ℕ) {r : ℕ} (hr : 0 < r) (s : ℝ) :
    (∑ q ∈ Icc 1 X, if r ∣ q then (q:ℝ)^s/(q.totient:ℝ)^2 else 0) ≤
      (r:ℝ)^s/(r.totient:ℝ)^2 * totientMoment (X/r) s := by
  rw [Uniform.sum_multiples _ X hr, totientMoment, mul_sum]
  apply sum_le_sum
  intro k hk
  have h := mul_le_mul_of_nonneg_left
    (reciprocal_totient_product hr (mem_Icc.mp hk).1)
    (show 0 ≤ (r:ℝ)^s*(k:ℝ)^s by positivity)
  simpa only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg r) (Nat.cast_nonneg k),
    div_eq_mul_inv, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using h

theorem totientMoment_zero (X : ℕ) :
    totientMoment X 0 ≤ 3.390828 := by
  simpa only [totientMoment, Real.rpow_zero, totientMass] using totientMass_stronger X

theorem totientMoment_abel {X : ℕ} (hX : 1 ≤ X) {s : ℝ} (hs : s ≤ 2) :
    totientMoment X s ≤ 22 * ∑ q ∈ Icc 1 X, (q:ℝ)^(s-2) := by
  have h := Uniform.weighted_sum_le_of_prefix_le Uniform.ratioSquare
    (fun _ => 22) (fun q => (q:ℝ)^(s-2)) hX (by
      intro k hk _
      simpa [sum_const, Nat.card_Icc, Uniform.ratioSquare, mul_comm] using
        Uniform.ratioSquare_sum_le k)
    (by positivity) (by
      intro k hk _
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hk)
        (by exact_mod_cast Nat.le_succ k) (by linarith))
  rw [mul_sum]
  apply le_trans (le_of_eq ?_) h
  apply sum_congr rfl
  intro q hq
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast (mem_Icc.mp hq).1
  rw [Uniform.ratioSquare, div_pow, div_mul_eq_mul_div,
    ← Real.rpow_natCast (q:ℝ) 2, ← Real.rpow_add hq0]
  congr 2
  ring

theorem power_sum_integral {X : ℕ} (hX : 1 ≤ X) {t : ℝ} (ht : t ≤ 0) :
    (∑ q ∈ Icc 1 X, (q:ℝ)^t) ≤ 1 + ∫ x in (1:ℝ)..(X:ℝ), x^t := by
  have ha : AntitoneOn (fun x : ℝ => x^t) (Set.Icc (1:ℝ) X) :=
    fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy ht
  have h := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x^t) hX
    (by simpa only [Nat.cast_one] using ha)
  have he : (∑ q ∈ Icc 1 X, (q:ℝ)^t) =
      1 + ∑ q ∈ Ico 1 X, ((q+1:ℕ):ℝ)^t := by
    rw [sum_Ico_add' (fun q : ℕ => (q:ℝ)^t) 1 X 1]
    rw [show Ico (1+1) (X+1) = Icc 2 X by ext q; simp]
    rw [show Icc 1 X = insert 1 (Icc 2 X) by
      ext q
      simp only [mem_Icc, mem_insert]
      omega, sum_insert (by simp)]
    norm_num
  rw [he]
  simpa only [Nat.cast_one] using add_le_add_right h 1

theorem totientMoment_high {X : ℕ} (hX : 1 ≤ X) {s : ℝ}
    (hs : 1 < s) (hs2 : s ≤ 2) :
    totientMoment X s ≤ (22/(s-1))*(X:ℝ)^(s-1) := by
  have hsum := power_sum_integral hX (show s-2 ≤ 0 by linarith)
  rw [integral_rpow (Or.inl (by linarith : -1 < s-2))] at hsum
  norm_num only [Real.one_rpow] at hsum
  have he : s-2+1 = s-1 := by ring
  rw [he] at hsum
  have h := (totientMoment_abel hX hs2).trans
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 22))
  have hp : 0 < s-1 := by linarith
  have hb : 1+((X:ℝ)^(s-1)-1)/(s-1) ≤ (X:ℝ)^(s-1)/(s-1) := by
    calc
      _ = (s-1+(X:ℝ)^(s-1)-1)/(s-1) := by field_simp; ring
      _ ≤ _ := (div_le_div_iff_of_pos_right hp).mpr (by linarith)
  exact h.trans ((mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 22)).trans_eq
    (by ring))

theorem totientMoment_low {X : ℕ} (hX : 1 ≤ X) {s : ℝ} (hs : s < 1) :
    totientMoment X s ≤ 22*(1+1/(1-s)) := by
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hsum := power_sum_integral hX (show s-2 ≤ 0 by linarith)
  have hi : (0:ℝ) ∉ Set.uIcc (1:ℝ) X := by
    rw [Set.uIcc_of_le hX1]
    simp
  rw [integral_rpow (Or.inr ⟨by linarith, hi⟩)] at hsum
  norm_num only [Real.one_rpow] at hsum
  rw [show s-2+1 = s-1 by ring] at hsum
  have hx : 0 ≤ (X:ℝ)^(s-1) := by positivity
  have hp : 0 < 1-s := by linarith
  have hb : ((X:ℝ)^(s-1)-1)/(s-1) ≤ 1/(1-s) := by
    calc
      _ = (1-(X:ℝ)^(s-1))/(1-s) := by
        rw [show 1-s = -(s-1) by ring, div_neg]
        ring
      _ ≤ _ := (div_le_div_iff_of_pos_right hp).mpr (by linarith)
  exact ((totientMoment_abel hX (by linarith)).trans
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 22))).trans
    (mul_le_mul_of_nonneg_left (add_le_add_right hb 1) (by norm_num))

theorem totientMoment_large {X : ℕ} (hX : 1 ≤ X) {s : ℝ} (hs : 2 ≤ s) :
    totientMoment X s ≤ 22*(X:ℝ)^(s-1) := by
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast hX
  calc
    _ = ∑ q ∈ Icc 1 X, Uniform.ratioSquare q * (q:ℝ)^(s-2) := by
      apply sum_congr rfl
      intro q hq
      have hq0 : 0 < (q:ℝ) := by exact_mod_cast (mem_Icc.mp hq).1
      rw [Uniform.ratioSquare, div_pow, div_mul_eq_mul_div,
        ← Real.rpow_natCast (q:ℝ) 2, ← Real.rpow_add hq0]
      congr 2
      ring
    _ ≤ (∑ q ∈ Icc 1 X, Uniform.ratioSquare q) * (X:ℝ)^(s-2) := by
      rw [sum_mul]
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (Nat.cast_le.mpr (mem_Icc.mp hq).2) (by linarith))
        (Uniform.ratioSquare_nonneg q)
    _ ≤ (22*(X:ℝ)) * (X:ℝ)^(s-2) :=
      mul_le_mul_of_nonneg_right (Uniform.ratioSquare_sum_le X) (by positivity)
    _ = _ := by
      rw [mul_assoc]
      nth_rw 1 [← Real.rpow_one (X:ℝ)]
      rw [← Real.rpow_add hX0]
      congr 2
      ring

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
