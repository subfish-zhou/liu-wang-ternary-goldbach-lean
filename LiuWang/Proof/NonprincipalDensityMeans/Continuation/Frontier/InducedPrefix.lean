import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.RightMean
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticPolyaVinogradovExplicit

/-! # Conductor induction with the actual nonunit mask and finite prefix endpoints -/

set_option autoImplicit false
noncomputable section

open Finset Classical
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier

theorem coprime_moebius_mask {e : ℕ} (he : 0 < e) (n : ℕ) :
    (∑ a ∈ e.divisors, if a ∣ n then (ArithmeticFunction.moebius a : ℂ) else 0) =
      if n.Coprime e then 1 else 0 := by
  rw [← sum_filter]
  have hf : e.divisors.filter (fun a => a ∣ n) = (Nat.gcd n e).divisors := by
    ext a
    have hg : Nat.gcd n e ≠ 0 := (Nat.gcd_pos_of_pos_right n he).ne'
    constructor
    · intro ha
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd (mem_filter.mp ha).2
        (Nat.mem_divisors.mp (mem_filter.mp ha).1).1, hg⟩
    · intro ha
      have h := Nat.mem_divisors.mp ha
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨h.1.trans (Nat.gcd_dvd_right n e), he.ne'⟩, h.1.trans (Nat.gcd_dvd_left n e)⟩
  rw [hf]
  have hsum := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd n e))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply, Nat.Coprime] using hsum

theorem induced_character_mask {d q : ℕ} (hdq : d ∣ q)
    (psi : Character d) {e : ℕ} (heq : d * e = q) (n : ℕ) :
    DirichletCharacter.changeLevel hdq psi (n : ZMod q) =
      psi (n : ZMod d) * if n.Coprime e then 1 else 0 := by
  by_cases hd : n.Coprime d
  · by_cases he : n.Coprime e
    · have hq : n.Coprime q := heq ▸ hd.mul_right he
      have h := psi.changeLevel_eq_cast_of_dvd' hdq (Nat.isCoprime_iff_coprime.mpr hq)
      simpa only [Int.cast_natCast, if_pos he, mul_one] using h
    · rw [if_neg he, mul_zero]
      apply MulChar.map_nonunit
      rw [ZMod.isUnit_iff_coprime]
      intro h
      exact he (h.of_dvd_right (heq ▸ dvd_mul_left e d))
  · rw [MulChar.map_nonunit psi ((ZMod.isUnit_iff_coprime n d).not.mpr hd), zero_mul]
    apply MulChar.map_nonunit
    rw [ZMod.isUnit_iff_coprime]
    exact fun h => hd (h.of_dvd_right hdq)

theorem sum_divisible_prefix {a M : ℕ} (ha : 0 < a) (hM : 0 < M)
    (g : ℕ → ℂ) :
    (∑ n ∈ (range M).filter (fun n => a ∣ n), g n) =
      ∑ k ∈ range ((M - 1) / a + 1), g (a * k) := by
  symm
  apply sum_bij (fun k _ => a * k)
  · intro k hk
    have hk' : k ≤ (M - 1) / a := Nat.le_of_lt_succ (mem_range.mp hk)
    have hm := (Nat.le_div_iff_mul_le ha).mp hk'
    rw [mul_comm k a] at hm
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), dvd_mul_right a k⟩
  · intro k _ l _ he
    exact Nat.eq_of_mul_eq_mul_left ha he
  · intro n hn
    have hnM := mem_range.mp (mem_filter.mp hn).1
    have han := (mem_filter.mp hn).2
    have he : a * (n / a) = n := Nat.mul_div_cancel' han
    refine ⟨n / a, mem_range.mpr ?_, he⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : n ≤ M - 1))
  · intro _ _
    rfl

theorem induced_prefix_eq {d q : ℕ} (hdq : d ∣ q)
    (psi : Character d) {e M : ℕ} (he : 0 < e) (heq : d * e = q) (hM : 0 < M) :
    (∑ n ∈ range M, DirichletCharacter.changeLevel hdq psi (n : ZMod q)) =
      ∑ a ∈ e.divisors, (ArithmeticFunction.moebius a : ℂ) * psi (a : ZMod d) *
        ∑ k ∈ range ((M - 1) / a + 1), psi (k : ZMod d) := by
  simp_rw [induced_character_mask hdq psi heq, ← coprime_moebius_mask he, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  have hp := Nat.pos_of_mem_divisors ha
  calc
    _ = (ArithmeticFunction.moebius a : ℂ) *
        ∑ n ∈ (range M).filter (fun n => a ∣ n), psi (n : ZMod d) := by
      rw [mul_sum, sum_filter]
      apply sum_congr rfl
      intro n _
      split_ifs <;> ring
    _ = _ := by
      rw [sum_divisible_prefix hp hM]
      simp only [Nat.cast_mul, map_mul, ← mul_sum, mul_assoc]

theorem induced_prefix_bound {d q : ℕ} (hdq : d ∣ q)
    (psi : Character d) {e : ℕ} (he : 0 < e) (heq : d * e = q)
    {P : ℝ} (hP : ∀ M : ℕ, ‖∑ n ∈ range M, psi (n : ZMod d)‖ ≤ P) (M : ℕ) :
    ‖∑ n ∈ range M, DirichletCharacter.changeLevel hdq psi (n : ZMod q)‖ ≤
      (e.divisors.card : ℝ) * P := by
  have hP0 : 0 ≤ P := by simpa only [range_zero, sum_empty, norm_zero] using hP 0
  obtain rfl | hM := Nat.eq_zero_or_pos M
  · simp only [range_zero, sum_empty, norm_zero]
    positivity
  rw [induced_prefix_eq hdq psi he heq hM]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a ∈ e.divisors, P := by
      apply sum_le_sum
      intro a _
      rw [norm_mul, norm_mul]
      have hm : ‖(ArithmeticFunction.moebius a : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := a))
      have ha : ‖(ArithmeticFunction.moebius a : ℂ)‖ * ‖psi (a : ZMod d)‖ ≤ 1 := by
        exact (mul_le_mul hm (psi.norm_le_one _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      exact (mul_le_mul_of_nonneg_left (hP _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
        (mul_le_of_le_one_left hP0 ha)
    _ = _ := by simp

theorem nonprincipal_conductor_prefix (q : ℕ) [NeZero q] (chi : Character q)
    (hchi : chi ≠ 1) (M : ℕ) :
    ‖∑ n ∈ range M, chi (n : ZMod q)‖ ≤
      ((q / chi.conductor).divisors.card : ℝ) *
        (4 * Real.sqrt chi.conductor * (1 + Real.log chi.conductor)) := by
  have hd : 0 < chi.conductor := Nat.pos_of_ne_zero chi.conductor_ne_zero
  let : NeZero chi.conductor := ⟨hd.ne'⟩
  have hd1 : 1 < chi.conductor := by
    have hn : chi.conductor ≠ 1 := fun h => hchi (chi.eq_one_iff_conductor_eq_one.mpr h)
    omega
  have heq := Nat.mul_div_cancel' chi.conductor_dvd_level
  have he : 0 < q / chi.conductor := Nat.div_pos
    (Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level) hd
  have hb := induced_prefix_bound chi.conductor_dvd_level chi.primitiveCharacter he heq
    (fun m => chi.primitiveCharacter_isPrimitive.norm_sum_range_le_four_mul_sqrt_q_mul_one_add_log hd1 m) M
  simpa only [chi.changeLevel_primitiveCharacter] using hb

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier
