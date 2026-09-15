import LiuWang.Proof.Campaign20260915.Density.PrimitivePrefix
import LiuWang.Proof.Campaign20260915.Density.MobiusTotient
import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.InducedPrefix

set_option autoImplicit false
noncomputable section

open Finset Complex Classical
open scoped ArithmeticFunction.Moebius
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier

namespace LiuWang.Proof.Campaign20260915.Density

theorem induced_prefix_mobius_bound {d q e : ℕ} (hdq : d ∣ q)
    (psi : Character d) (he : 0 < e) (heq : d * e = q)
    {P : ℝ} (hP : ∀ M : ℕ, ‖∑ n ∈ range M, psi (n : ZMod d)‖ ≤ P) (M : ℕ) :
    ‖∑ n ∈ range M, DirichletCharacter.changeLevel hdq psi (n : ZMod q)‖ ≤
      divisorMobiusMass e * P := by
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0)
  obtain rfl | hM := Nat.eq_zero_or_pos M
  · simp only [range_zero, sum_empty, norm_zero]
    exact mul_nonneg (divisorMobiusMass_nonneg e) hP0
  rw [induced_prefix_eq hdq psi he heq hM]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ e.divisors, |(μ a : ℝ)| * P := by
      apply sum_le_sum
      intro a _
      rw [norm_mul, norm_mul]
      have hm : ‖(μ a : ℂ)‖ = |(μ a : ℝ)| := by
        rw [Complex.norm_intCast, ← Int.cast_abs]
      have ha := mul_le_mul_of_nonneg_left (psi.norm_le_one (a : ZMod d))
        (norm_nonneg (μ a : ℂ))
      rw [mul_one, hm] at ha
      rw [hm]
      exact mul_le_mul ha (hP _) (norm_nonneg _) (abs_nonneg _)
    _ = _ := by rw [← sum_mul, ← divisorMobiusMass_eq]

theorem nonprincipal_conductor_ge_three {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) : 3 ≤ chi.conductor := by
  have hd := Nat.pos_of_ne_zero chi.conductor_ne_zero
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hd1 : chi.conductor ≠ 1 := fun h => hchi (chi.eq_one_iff_conductor_eq_one.mpr h)
  have hp : chi.primitiveCharacter ≠ 1 := by
    intro he
    have h := chi.primitiveCharacter_isPrimitive
    change chi.primitiveCharacter.conductor = chi.conductor at h
    rw [he, DirichletCharacter.conductor_one] at h
    exact hd1 h.symm
  have hd2 : chi.conductor ≠ 2 := by
    intro he
    have hmem := (mem_nonprincipalCharacters chi.primitiveCharacter).mpr hp
    have hset : nonprincipalCharacters chi.conductor = ∅ := by
      apply card_eq_zero.mp
      rw [card_nonprincipalCharacters, he]
      norm_num
    rw [hset] at hmem
    simp at hmem
  omega

theorem nonprincipal_prefix_totient (q : ℕ) [NeZero q] (chi : Character q)
    (hchi : chi ≠ 1) (M : ℕ) :
    (q.totient : ℝ) * ‖∑ n ∈ range M, chi (n : ZMod q)‖ ≤
      (q : ℝ) * Real.sqrt q * Real.log q := by
  let d := chi.conductor
  let e := q / d
  have hd : 0 < d := Nat.pos_of_ne_zero chi.conductor_ne_zero
  let : NeZero d := ⟨hd.ne'⟩
  have heq : d * e = q := Nat.mul_div_cancel' chi.conductor_dvd_level
  have he : 0 < e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level) hd
  have hlog : Real.log d ≤ Real.log q :=
    Real.log_le_log (Nat.cast_pos.mpr hd)
      (Nat.cast_le.mpr (Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level))
  have hlog0 := Real.log_nonneg (Nat.one_le_cast.mpr hd : (1 : ℝ) ≤ d)
  have hp := induced_prefix_mobius_bound chi.conductor_dvd_level chi.primitiveCharacter he heq
    (fun N => primitive_prefix_log chi.primitiveCharacter_isPrimitive
      (nonprincipal_conductor_ge_three hchi) N) M
  rw [chi.changeLevel_primitiveCharacter] at hp
  have h := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg q.totient)
  have hc := divisorMobiusMass_totient_compensation d e
  rw [heq] at hc
  have h1 := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ Real.sqrt d * Real.log d by positivity)
  have h2 := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ (q : ℝ) * Real.sqrt e * Real.sqrt d by positivity)
  have hs : Real.sqrt e * Real.sqrt d = Real.sqrt q := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg e), ← Nat.cast_mul, mul_comm e d, heq]
  calc
    _ ≤ (divisorMobiusMass e * (q.totient : ℝ)) * (Real.sqrt d * Real.log d) := by
      simpa only [d, e, mul_assoc, mul_comm, mul_left_comm] using h
    _ ≤ ((q : ℝ) * Real.sqrt e) * (Real.sqrt d * Real.log d) := h1
    _ ≤ ((q : ℝ) * Real.sqrt e * Real.sqrt d) * Real.log q := by
      simpa only [mul_assoc] using h2
    _ = _ := by rw [mul_assoc (q : ℝ), hs]

theorem nonprincipal_prefix_paid (q : ℕ) [NeZero q] (chi : Character q)
    (hchi : chi ≠ 1) (M : ℕ) :
    ‖∑ n ∈ range M, chi (n : ZMod q)‖ ≤
      (q : ℝ) * Real.sqrt q * Real.log q / q.totient := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q)))).mpr
  simpa only [mul_comm] using nonprincipal_prefix_totient q chi hchi M

#print axioms nonprincipal_prefix_totient
#print axioms nonprincipal_prefix_paid

end LiuWang.Proof.Campaign20260915.Density
