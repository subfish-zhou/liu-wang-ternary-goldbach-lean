import LiuWang.Proof.CharacterExpansion.Finite
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Gauss sums under actual character induction

At a prime step the full additive pullback vanishes by translation. Removing
the multiples of the new prime gives the exact factor `-chi(p)`. Thus changing
level never increases the norm, including repeated prime factors and level one.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.CharacterExpansion

open LiuWang.Proof.Interfaces
open AnalyticNumberTheory.LargeSieve
open scoped BigOperators

theorem gaussSum_eq_range {q : Nat} [NeZero q] (χ : Character q) :
    gaussSum χ ZMod.stdAddChar =
      ∑ n ∈ Finset.range q, χ (n : ZMod q) * charReal ((n : Real) / (q : Real)) := by
  rw [gaussSum, sum_zmod_eq_sum_range]
  simp_rw [stdAddChar_nat]

theorem sum_pullback_stdAddChar_eq_zero {q m : Nat} [NeZero q] [NeZero m]
    (hd : q ∣ m) (hqm : q < m) (χ : Character q) :
    (∑ x : ZMod m, χ (ZMod.castHom hd (ZMod q) x) * ZMod.stdAddChar x) = 0 := by
  have hq0 : (q : ZMod m) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hqm, (NeZero.ne q)] at hv
  have he : ZMod.stdAddChar (q : ZMod m) ≠ 1 := by
    intro h
    apply hq0
    apply ZMod.injective_stdAddChar
    simpa using h
  apply eq_zero_of_mul_eq_self_left he
  rw [Finset.mul_sum]
  calc
    (∑ x : ZMod m,
        ZMod.stdAddChar (q : ZMod m) *
          (χ (ZMod.castHom hd (ZMod q) x) * ZMod.stdAddChar x)) =
        ∑ x : ZMod m,
          χ (ZMod.castHom hd (ZMod q) ((q : ZMod m) + x)) *
            ZMod.stdAddChar ((q : ZMod m) + x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [map_add, map_natCast (ZMod.castHom hd (ZMod q)) q,
        ZMod.natCast_self, zero_add, AddChar.map_add_eq_mul]
      ring
    _ = _ := Fintype.sum_bijective _ (AddGroup.addLeft_bijective (q : ZMod m))
      _ _ (fun _ => rfl)

theorem changeLevel_prime_apply {q p : Nat} (hp : p.Prime)
    (χ : Character q) (n : Nat) :
    DirichletCharacter.changeLevel (dvd_mul_left q p) χ (n : ZMod (p * q)) =
      χ (n : ZMod q) - if p ∣ n then χ (n : ZMod q) else 0 := by
  classical
  have hd : q ∣ p * q := dvd_mul_left q p
  by_cases hpN : p ∣ n
  · have hn : ¬ Nat.Coprime n (p * q) := by
      intro h
      exact (hp.coprime_iff_not_dvd.mp (h.of_dvd_right (dvd_mul_right p q)).symm) hpN
    have hu : ¬ IsUnit (n : ZMod (p * q)) := by
      simpa [ZMod.isUnit_iff_coprime] using hn
    simp [hpN, MulChar.map_nonunit _ hu]
  · by_cases hqN : Nat.Coprime n q
    · have hcop : Nat.Coprime n (p * q) :=
        ((hp.coprime_iff_not_dvd.mpr hpN).symm).mul_right hqN
      have h := χ.changeLevel_eq_cast_of_dvd' hd
        (Nat.isCoprime_iff_coprime.mpr hcop)
      simpa [hpN, Int.cast_natCast] using h
    · have hu : ¬ IsUnit (n : ZMod q) := by
        simpa [ZMod.isUnit_iff_coprime] using hqN
      have hv : ¬ IsUnit (n : ZMod (p * q)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact fun h => hqN (h.of_dvd_right hd)
      simp [hpN, χ.map_nonunit hu, MulChar.map_nonunit _ hv]

theorem sum_range_multiples {p q : Nat} (hp : 0 < p) (f : Nat → Complex) :
    (∑ n ∈ Finset.range (p * q), if p ∣ n then f n else 0) =
      ∑ n ∈ Finset.range q, f (p * n) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun n _ => p * n)
  · intro n hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hn) hp), dvd_mul_right p n⟩
  · intro n _ m _ h
    exact Nat.eq_of_mul_eq_mul_left hp h
  · intro n hn
    obtain ⟨hr, hd⟩ := Finset.mem_filter.mp hn
    obtain ⟨k, rfl⟩ := hd
    exact ⟨k, Finset.mem_range.mpr
      ((Nat.mul_lt_mul_left hp).mp (Finset.mem_range.mp hr)), rfl⟩
  · intro n _
    rfl

theorem gaussSum_changeLevel_prime {q p : Nat} [NeZero q] [NeZero (p * q)]
    (hp : p.Prime) (χ : Character q) :
    gaussSum (DirichletCharacter.changeLevel (dvd_mul_left q p) χ) ZMod.stdAddChar =
      -χ (p : ZMod q) * gaussSum χ ZMod.stdAddChar := by
  have hp0 : (p : Real) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hzero := sum_pullback_stdAddChar_eq_zero (dvd_mul_left q p)
    (by nlinarith [hp.two_le, NeZero.pos q] : q < p * q) χ
  rw [sum_zmod_eq_sum_range] at hzero
  simp only [map_natCast, stdAddChar_nat] at hzero
  rw [gaussSum_eq_range]
  simp_rw [changeLevel_prime_apply hp, sub_mul, ite_mul, zero_mul]
  rw [Finset.sum_sub_distrib, hzero, zero_sub, sum_range_multiples hp.pos]
  rw [gaussSum_eq_range, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [Nat.cast_mul, map_mul]
  have he : ((p * n : Nat) : Real) / ((p * q : Nat) : Real) =
      (n : Real) / (q : Real) := by
    push_cast
    exact mul_div_mul_left _ _ hp0
  rw [he]
  ring

theorem norm_gaussSum_changeLevel_prime {q p : Nat} [NeZero q] [NeZero (p * q)]
    (hp : p.Prime) (χ : Character q) :
    ‖gaussSum (DirichletCharacter.changeLevel (dvd_mul_left q p) χ) ZMod.stdAddChar‖ ≤
      ‖gaussSum χ ZMod.stdAddChar‖ := by
  rw [gaussSum_changeLevel_prime hp, norm_mul, norm_neg]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem gaussSum_changeLevel_congr {q m n : Nat} [NeZero m] [NeZero n]
    (h : m = n) (hm : q ∣ m) (hn : q ∣ n) (χ : Character q) :
    gaussSum (DirichletCharacter.changeLevel hm χ) ZMod.stdAddChar =
      gaussSum (DirichletCharacter.changeLevel hn χ) ZMod.stdAddChar := by
  subst n
  rfl

theorem norm_gaussSum_changeLevel_mul (k : Nat) :
    ∀ (q : Nat) [NeZero q] [NeZero (k * q)] (χ : Character q),
    ‖gaussSum (DirichletCharacter.changeLevel (dvd_mul_left q k) χ) ZMod.stdAddChar‖ ≤
      ‖gaussSum χ ZMod.stdAddChar‖ := by
  induction k using induction_on_primes with
  | zero =>
    intro q _ hz _
    exact False.elim (hz.out (by simp))
  | one =>
    intro q _ _ χ
    rw [gaussSum_changeLevel_congr (one_mul q) _ (dvd_refl q) χ,
      DirichletCharacter.changeLevel_self]
  | prime_mul p k hp ih =>
    intro q _ hpk χ
    have hk : NeZero (k * q) := ⟨by
      intro hk
      apply hpk.out
      simp [Nat.mul_assoc, hk]⟩
    have hpk' : NeZero (p * (k * q)) := ⟨by
      simpa only [← Nat.mul_assoc] using hpk.out⟩
    have hstep := norm_gaussSum_changeLevel_prime hp
      (DirichletCharacter.changeLevel (dvd_mul_left q k) χ)
    have hbound := hstep.trans (ih q χ)
    rw [← DirichletCharacter.changeLevel_trans] at hbound
    rw [gaussSum_changeLevel_congr (Nat.mul_assoc p k q) _
      ((dvd_mul_left q k).trans (dvd_mul_left (k * q) p)) χ]
    exact hbound

theorem norm_gaussSum_changeLevel {q m : Nat} [NeZero q] [NeZero m]
    (hd : q ∣ m) (χ : Character q) :
    ‖gaussSum (DirichletCharacter.changeLevel hd χ) ZMod.stdAddChar‖ ≤
      ‖gaussSum χ ZMod.stdAddChar‖ := by
  obtain ⟨k, rfl⟩ := hd
  have : NeZero (k * q) := ⟨by simpa [Nat.mul_comm] using NeZero.ne (q * k)⟩
  rw [gaussSum_changeLevel_congr (Nat.mul_comm q k) _ (dvd_mul_left q k) χ]
  exact norm_gaussSum_changeLevel_mul k q χ

theorem primitiveGaussAddChar_eq_std {q : Nat} [NeZero q] :
    primitiveGaussAddChar q = ZMod.stdAddChar := by
  ext x
  rw [primitiveGaussAddChar_apply]
  nth_rw 2 [← ZMod.natCast_zmod_val x]
  exact (stdAddChar_nat x.val).symm

theorem norm_gaussSum_primitive {q : Nat} [NeZero q] (χ : Character q)
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  rw [← primitiveGaussAddChar_eq_std]
  exact primitive_gaussSum_norm ⟨χ, hχ⟩

theorem norm_gaussSum_le_sqrt_conductor {q : Nat} [NeZero q] (χ : Character q) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt χ.conductor := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  calc
    ‖gaussSum χ ZMod.stdAddChar‖ =
        ‖gaussSum (DirichletCharacter.changeLevel χ.conductor_dvd_level
          χ.primitiveCharacter) ZMod.stdAddChar‖ := by
      rw [χ.changeLevel_primitiveCharacter]
    _ ≤ ‖gaussSum χ.primitiveCharacter ZMod.stdAddChar‖ :=
      norm_gaussSum_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    _ = Real.sqrt χ.conductor :=
      norm_gaussSum_primitive χ.primitiveCharacter χ.primitiveCharacter_isPrimitive

theorem G_eq_char_mul_gaussSum {q a : Nat} [NeZero q]
    (ha : Nat.Coprime a q) (χ : Character q) :
    G a χ = χ (a : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have h := gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar (ZMod.unitOfCoprime a ha)
  simpa [G] using h

theorem norm_G_le_sqrt_conductor {q a : Nat} [NeZero q]
    (ha : Nat.Coprime a q) (χ : Character q) :
    ‖G a χ‖ ≤ Real.sqrt χ.conductor := by
  rw [G_eq_char_mul_gaussSum ha, norm_mul]
  have hn : ‖χ (a : ZMod q)‖ = 1 := by
    simpa using χ.unit_norm_eq_one (ZMod.unitOfCoprime a ha)
  rw [hn, one_mul]
  simpa [DirichletCharacter.conductor_inv] using norm_gaussSum_le_sqrt_conductor χ⁻¹

theorem norm_G_induced_le_sqrt {d q a : Nat} [NeZero d] [NeZero q]
    (hd : d ∣ q) (ha : Nat.Coprime a q) (χ : Character d) (hχ : χ.IsPrimitive) :
    ‖G a (DirichletCharacter.changeLevel hd χ)‖ ≤ Real.sqrt d := by
  have h := norm_G_le_sqrt_conductor ha (DirichletCharacter.changeLevel hd χ)
  rwa [DirichletCharacter.conductor_changeLevel, hχ] at h

end LiuWang.Proof.CharacterExpansion
