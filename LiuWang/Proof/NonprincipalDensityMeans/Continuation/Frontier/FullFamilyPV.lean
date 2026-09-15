import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.InducedPrefix
import Mathlib.Data.Nat.Sqrt

/-! # An explicit Pólya--Vinogradov bound for every nonprincipal character -/

set_option autoImplicit false
noncomputable section

open Finset Classical
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier

theorem divisor_card_le_two_sqrt (e : ℕ) :
    (e.divisors.card : ℝ) ≤ 2 * Real.sqrt e := by
  obtain rfl | he := Nat.eq_zero_or_pos e
  · simp
  let A := e.divisors.filter (fun a => a ≤ Nat.sqrt e)
  let B := e.divisors.filter (fun a => ¬a ≤ Nat.sqrt e)
  have hA : A.card ≤ Nat.sqrt e := by
    have hsub : A ⊆ Icc 1 (Nat.sqrt e) := by
      intro a ha
      exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors (mem_filter.mp ha).1, (mem_filter.mp ha).2⟩
    simpa using card_le_card hsub
  have hB : B.card ≤ Nat.sqrt e := by
    have hb := card_le_card_of_injOn (fun a => e / a) (s := B) (t := Icc 1 (Nat.sqrt e))
      (fun a ha => by
        have had := (Nat.mem_divisors.mp (mem_filter.mp ha).1).1
        have hap := Nat.pos_of_mem_divisors (mem_filter.mp ha).1
        have heq := Nat.mul_div_cancel' had
        have hle := (Nat.le_sqrt_of_eq_mul heq.symm).resolve_left (mem_filter.mp ha).2
        exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd he had) hap, hle⟩)
      (fun a ha b hb hab => by
        have had := (Nat.mem_divisors.mp (mem_filter.mp ha).1).1
        have hbd := (Nat.mem_divisors.mp (mem_filter.mp hb).1).1
        have hap := Nat.pos_of_mem_divisors (mem_filter.mp ha).1
        have hpos := Nat.div_pos (Nat.le_of_dvd he had) hap
        have h1 := Nat.mul_div_cancel' had
        have h2 := Nat.mul_div_cancel' hbd
        change e / a = e / b at hab
        rw [← hab] at h2
        exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm))
    simpa using hb
  have hcard : e.divisors.card ≤ 2 * Nat.sqrt e := by
    have h := card_filter_add_card_filter_not (s := e.divisors) (fun a => a ≤ Nat.sqrt e)
    change A.card + B.card = e.divisors.card at h
    omega
  have hs : (Nat.sqrt e : ℝ) ≤ Real.sqrt e := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.sqrt_le' e
  have hc := (Nat.cast_le (α := ℝ)).mpr hcard
  push_cast at hc
  linarith

theorem nonprincipal_prefix_PV (q : ℕ) [NeZero q] (chi : Character q)
    (hchi : chi ≠ 1) (M : ℕ) :
    ‖∑ n ∈ range M, chi (n : ZMod q)‖ ≤
      8 * Real.sqrt q * (1 + Real.log q) := by
  let d := chi.conductor
  let e := q / d
  have hd : 0 < d := Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hdq : d ≤ q := Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  have heq : d * e = q := Nat.mul_div_cancel' chi.conductor_dvd_level
  have hlog : 1 + Real.log (d : ℝ) ≤ 1 + Real.log q :=
    add_le_add le_rfl (Real.log_le_log (Nat.cast_pos.mpr hd) (Nat.cast_le.mpr hdq))
  have hL0 : 0 ≤ 1 + Real.log (d : ℝ) := by
    have h := Real.log_nonneg (Nat.one_le_cast.mpr hd)
    linarith
  have h1 := mul_le_mul_of_nonneg_right (divisor_card_le_two_sqrt e)
    (by positivity : 0 ≤ 4 * Real.sqrt d * (1 + Real.log d))
  have h2 := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ 8 * Real.sqrt e * Real.sqrt d)
  have hsqrt : Real.sqrt e * Real.sqrt d = Real.sqrt q := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg e), ← Nat.cast_mul, mul_comm e d, heq]
  have h := nonprincipal_conductor_prefix q chi hchi M
  change _ ≤ (e.divisors.card : ℝ) * (4 * Real.sqrt d * (1 + Real.log d)) at h
  calc
    _ ≤ _ := h.trans h1
    _ = (8 * (Real.sqrt e * Real.sqrt d)) * (1 + Real.log d) := by ring
    _ ≤ (8 * (Real.sqrt e * Real.sqrt d)) * (1 + Real.log q) := by
      simpa only [mul_assoc] using h2
    _ = _ := by rw [hsqrt]

def prefixBudget (q : ℕ) : ℝ := min (q : ℝ) (8 * Real.sqrt q * (1 + Real.log q))

theorem prefixBudget_nonneg (q : ℕ) [NeZero q] : 0 ≤ prefixBudget q := by
  have h := Real.log_nonneg (Nat.one_le_cast.mpr (NeZero.pos q))
  unfold prefixBudget
  positivity

theorem nonprincipal_prefix_budget (q : ℕ) [NeZero q] (chi : Character q)
    (hchi : chi ≠ 1) (M : ℕ) :
    ‖∑ n ∈ range M, chi (n : ZMod q)‖ ≤ prefixBudget q :=
  le_min (DirichletLWeakStripDerivative.norm_sum_range_character_le_modulus chi hchi M)
    (nonprincipal_prefix_PV q chi hchi M)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier
