import LiuWang.Proof.CharacterExpansion.Finite
import LiuWang.Proof.SingularIntegral.Window
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The literal ternary coefficient

The reduced representatives are `1 ≤ a ≤ q`, including `a = q = 1`.
The zero index is separately set to zero. No binary sieve normalization is used.
-/

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open ArithmeticFunction

namespace LiuWang.Proof.SingularSeries

def reducedResidues (q : ℕ) : Finset ℕ :=
  (Icc 1 q).filter (fun a => Nat.Coprime a q)

def ramanujan (N q : ℕ) : ℂ :=
  ∑ a ∈ reducedResidues q, charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ))

def coefficient (N q : ℕ) : ℂ :=
  if q = 0 then 0 else
    (moebius q : ℂ) / (q.totient : ℂ) ^ 3 * ramanujan N q

theorem coefficient_source {N q : ℕ} (hq : 0 < q) :
    coefficient N q =
      (moebius q : ℂ) / (q.totient : ℂ) ^ 3 *
        ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
          charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ)) := by
  simp [coefficient, hq.ne', ramanujan, reducedResidues]

@[simp] theorem ramanujan_zero (N : ℕ) : ramanujan N 0 = 0 := by
  simp [ramanujan, reducedResidues]

@[simp] theorem coefficient_zero (N : ℕ) : coefficient N 0 = 0 := by
  simp [coefficient]

theorem reducedResidues_card (q : ℕ) : (reducedResidues q).card = q.totient := by
  have he : Icc 1 q = Ico 1 (1 + q) := by ext a; simp; omega
  simpa only [reducedResidues, he, Nat.coprime_comm] using
    Nat.filter_coprime_Ico_eq_totient q 1

theorem stdAddChar_negative_phase {q : ℕ} [NeZero q] (a N : ℕ) :
    ZMod.stdAddChar (-(a : ZMod q) * (N : ZMod q)) =
      charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ)) := by
  have h := ZMod.stdAddChar_coe (N := q) (-(a : ℤ) * (N : ℤ))
  push_cast at h
  rw [h]
  unfold charReal
  congr 1
  push_cast
  ring

theorem sum_Icc_eq_sum_range_of_endpoint {q : ℕ} (hq : 0 < q)
    (f : ℕ → ℂ) (hf : f q = f 0) :
    (∑ a ∈ Icc 1 q, f a) = ∑ a ∈ range q, f a := by
  have he : Icc 1 q = Ico 1 (q + 1) := by ext a; simp
  rw [he, sum_Ico_eq_sub f (by omega), sum_range_succ, sum_range_one, hf]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem ramanujan_eq_zmod (N : ℕ) {q : ℕ} [NeZero q] :
    ramanujan N q =
      ∑ a : ZMod q, if IsUnit a then ZMod.stdAddChar (-a * (N : ZMod q)) else 0 := by
  classical
  let f : ℕ → ℂ := fun a =>
    if Nat.Coprime a q then ZMod.stdAddChar (-(a : ZMod q) * (N : ZMod q)) else 0
  have hf : f q = f 0 := by simp [f]
  calc
    ramanujan N q = ∑ a ∈ Icc 1 q, f a := by
      simp only [ramanujan, reducedResidues, sum_filter, f, stdAddChar_negative_phase]
    _ = ∑ a ∈ range q, f a := sum_Icc_eq_sum_range_of_endpoint (NeZero.pos q) f hf
    _ = ∑ a : Fin q, f a := (Fin.sum_univ_eq_sum_range f q).symm
    _ = _ := Fintype.sum_equiv (ZMod.finEquiv q).toEquiv _ _ (by
      intro a
      have he : (ZMod.finEquiv q) a = (a.val : ZMod q) := by
        obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
        exact (Fin.cast_val_eq_self a).symm
      change f a.val = if IsUnit ((ZMod.finEquiv q) a) then
        ZMod.stdAddChar (-((ZMod.finEquiv q) a) * (N : ZMod q)) else 0
      simp only [he, ZMod.isUnit_iff_coprime, f])

@[simp] theorem ramanujan_one (N : ℕ) : ramanujan N 1 = 1 := by
  rw [ramanujan_eq_zmod]
  rw [Fintype.sum_eq_single (0 : ZMod 1)]
  · have hu : IsUnit (0 : ZMod 1) := by
      rw [Subsingleton.elim (0 : ZMod 1) 1]
      exact isUnit_one
    simp only [if_pos hu, neg_zero, zero_mul, AddChar.map_zero_eq_one]
  · intro b hb
    exact (hb (Subsingleton.elim b 0)).elim

@[simp] theorem coefficient_one (N : ℕ) : coefficient N 1 = 1 := by
  simp [coefficient]

theorem ramanujan_conj (N q : ℕ) : star (ramanujan N q) = ramanujan N q := by
  classical
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  let : NeZero q := ⟨hq⟩
  rw [ramanujan_eq_zmod, star_sum]
  apply Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _
  intro a
  have hu : IsUnit (-a) ↔ IsUnit a := ⟨fun h => by simpa using h.neg, fun h => h.neg⟩
  simp only [Equiv.neg_apply, hu]
  split_ifs
  · change (starRingEnd ℂ) _ = _
    rw [← AddChar.map_neg_eq_conj]
    congr 1
    ring
  · exact star_zero _

theorem ramanujan_im (N q : ℕ) : (ramanujan N q).im = 0 := by
  have h := congrArg Complex.im (ramanujan_conj N q)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

theorem ramanujan_eq_real (N q : ℕ) :
    ramanujan N q = ((ramanujan N q).re : ℂ) := by
  apply Complex.ext <;> simp [ramanujan_im]

theorem coefficient_eq_real (N q : ℕ) :
    coefficient N q =
      ((moebius q : ℝ) / (q.totient : ℝ) ^ 3 * (ramanujan N q).re : ℝ) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  rw [coefficient, if_neg hq, ramanujan_eq_real]
  push_cast
  rfl

theorem coefficient_eq_zero_of_not_squarefree (N : ℕ) {q : ℕ}
    (hq : ¬ Squarefree q) : coefficient N q = 0 := by
  simp [coefficient, moebius_eq_zero_of_not_squarefree hq]

theorem norm_ramanujan_le_totient (N q : ℕ) :
    ‖ramanujan N q‖ ≤ (q.totient : ℝ) := by
  calc
    _ ≤ ∑ a ∈ reducedResidues q, ‖charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ))‖ :=
      norm_sum_le _ _
    _ = _ := by simp [LiuWang.Proof.SingularIntegral.charReal_norm, reducedResidues_card]

theorem norm_coefficient_le (N q : ℕ) :
    ‖coefficient N q‖ ≤ 1 / (q.totient : ℝ) ^ 2 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hφ : 0 < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq))
  have hμ : ‖(moebius q : ℂ)‖ ≤ 1 := by
    rcases moebius_eq_or q with h | h | h <;> rw [h] <;> norm_num
  rw [coefficient, if_neg hq, norm_mul, norm_div, norm_pow,
    Complex.norm_natCast]
  calc
    _ ≤ (1 / (q.totient : ℝ) ^ 3) * (q.totient : ℝ) :=
      mul_le_mul (div_le_div_of_nonneg_right hμ (by positivity))
        (norm_ramanujan_le_totient N q) (norm_nonneg _) (by positivity)
    _ = _ := by field_simp

theorem ramanujan_prime (N : ℕ) {p : ℕ} (hp : p.Prime) :
    ramanujan N p = if p ∣ N then (p : ℂ) - 1 else -1 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hsum := AddChar.sum_mulShift (-(N : ZMod p)) (ZMod.isPrimitive_stdAddChar p)
  have he : ramanujan N p + 1 =
      ∑ a : ZMod p, ZMod.stdAddChar (a * -(N : ZMod p)) := by
    rw [ramanujan_eq_zmod]
    have hz : (∑ a : ZMod p, if a = 0 then (1 : ℂ) else 0) = 1 := by simp
    rw [← hz, ← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · simp [ha, isUnit_iff_ne_zero, neg_mul, mul_neg]
  rw [hsum] at he
  simp only [neg_eq_zero, ZMod.natCast_eq_zero_iff, ZMod.card] at he
  split_ifs with h
  · simpa [h] using eq_sub_of_add_eq he
  · simpa [h] using eq_sub_of_add_eq he

theorem coefficient_prime (N : ℕ) {p : ℕ} (hp : p.Prime) :
    coefficient N p =
      if p ∣ N then (-1 : ℂ) / ((p : ℂ) - 1) ^ 2
      else 1 / ((p : ℂ) - 1) ^ 3 := by
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [coefficient, if_neg hp.ne_zero, moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one, ramanujan_prime N hp]
  split_ifs <;> push_cast <;> field_simp

theorem coefficient_prime_power (N : ℕ) {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    coefficient N (p ^ k) = 0 := by
  have hμ : moebius (p ^ k) = 0 := by
    rw [moebius_apply_prime_pow hp (show k ≠ 0 by omega), if_neg (by omega)]
  simp [coefficient, hμ]

theorem coefficient_two_of_odd {N : ℕ} (hN : Odd N) :
    coefficient N 2 = 1 := by
  have h2 : ¬ 2 ∣ N := by
    obtain ⟨k, hk⟩ := hN
    intro ⟨m, hm⟩
    omega
  rw [coefficient_prime N Nat.prime_two, if_neg h2]
  norm_num

end LiuWang.Proof.SingularSeries
