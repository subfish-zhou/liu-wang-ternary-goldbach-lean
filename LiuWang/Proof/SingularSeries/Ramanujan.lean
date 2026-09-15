import LiuWang.Proof.SingularSeries.Source
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerLargeSieve

/-!
# Integer Ramanujan formula and multiplicativity

Möbius inversion of the coprimality indicator is applied to the actual
character sum. The resulting convolution is not a replacement definition.
-/

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.SingularSeries

set_option backward.isDefEq.respectTransparency false in
theorem sum_zmod_eq_sum_range {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, f a) = ∑ a ∈ range q, f (a : ZMod q) := by
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  apply Fintype.sum_equiv (ZMod.finEquiv q).toEquiv
  intro a
  congr 1
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
  exact Fin.cast_val_eq_self a

theorem complete_phase_sum (N : ℕ) {q : ℕ} (hq : 0 < q) :
    (∑ a ∈ Icc 1 q, charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ))) =
      if q ∣ N then (q : ℂ) else 0 := by
  let : NeZero q := ⟨hq.ne'⟩
  simp_rw [← stdAddChar_negative_phase]
  rw [sum_Icc_eq_sum_range_of_endpoint hq _ (by simp),
    ← sum_zmod_eq_sum_range (fun a : ZMod q => ZMod.stdAddChar (-a * (N : ZMod q)))]
  have h := AddChar.sum_mulShift (-(N : ZMod q)) (ZMod.isPrimitive_stdAddChar q)
  simpa only [neg_mul, mul_neg, neg_eq_zero, ZMod.natCast_eq_zero_iff,
    ZMod.card, Nat.cast_ite, Nat.cast_zero] using h

theorem sum_Icc_dvd {q d : ℕ} (hd : 0 < d) (f : ℕ → ℂ) :
    (∑ a ∈ Icc 1 q, if d ∣ a then f a else 0) =
      ∑ b ∈ Icc 1 (q / d), f (d * b) := by
  rw [← sum_filter]
  symm
  apply sum_bij (fun b _ => d * b)
  · intro b hb
    rcases mem_Icc.mp hb with ⟨hb1, hbq⟩
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right _ _⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hbq
  · intro a _ b _ hab
    exact Nat.mul_left_cancel hd hab
  · intro a ha
    rcases mem_filter.mp ha with ⟨ha, ⟨b, rfl⟩⟩
    refine ⟨b, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · have := (mem_Icc.mp ha).1
      by_contra hb
      have : b = 0 := by omega
      simp_all
    · exact (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using (mem_Icc.mp ha).2)
  · intros
    rfl

theorem phase_sum_on_multiples (N : ℕ) {q d : ℕ} (hq : 0 < q) (hd : d ∈ q.divisors) :
    (∑ a ∈ Icc 1 q, if d ∣ a then
      charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ)) else 0) =
      if q / d ∣ N then ((q / d : ℕ) : ℂ) else 0 := by
  have hd0 := Nat.pos_of_mem_divisors hd
  have hdiv := Nat.dvd_of_mem_divisors hd
  have he : d * (q / d) = q := Nat.mul_div_cancel' hdiv
  have hqd : 0 < q / d := by
    apply Nat.div_pos (Nat.le_of_dvd hq hdiv) hd0
  rw [sum_Icc_dvd hd0]
  convert complete_phase_sum N hqd using 1
  apply sum_congr rfl
  intro a _
  congr 1
  have heR : (d : ℝ) * (q / d : ℕ) = (q : ℝ) := by exact_mod_cast he
  have hdR : (d : ℝ) ≠ 0 := by positivity
  rw [← heR, Nat.cast_mul]
  field_simp

def divisorWeight (N : ℕ) : ArithmeticFunction ℤ where
  toFun d := if d ∣ N then (d : ℤ) else 0
  map_zero' := by simp

theorem divisorWeight_apply (N d : ℕ) :
    divisorWeight N d = if d ∣ N then (d : ℤ) else 0 := rfl

theorem divisorWeight_multiplicative (N : ℕ) : (divisorWeight N).IsMultiplicative := by
  constructor
  · simp [divisorWeight]
  · intro a b hab
    have hd : a * b ∣ N ↔ a ∣ N ∧ b ∣ N :=
      ⟨fun h => ⟨dvd_trans (dvd_mul_right a b) h, dvd_trans (dvd_mul_left b a) h⟩,
        fun h => hab.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
    simp only [divisorWeight_apply, hd, Nat.cast_mul]
    split_ifs <;> simp_all

def ramanujanArithmetic (N : ℕ) : ArithmeticFunction ℤ :=
  moebius * divisorWeight N

theorem ramanujanArithmetic_multiplicative (N : ℕ) :
    (ramanujanArithmetic N).IsMultiplicative :=
  isMultiplicative_moebius.mul (divisorWeight_multiplicative N)

theorem ramanujan_integer_formula (N q : ℕ) :
    ramanujan N q =
      ∑ d ∈ q.divisors, (moebius d : ℂ) *
        (if q / d ∣ N then ((q / d : ℕ) : ℂ) else 0) := by
  classical
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  unfold ramanujan reducedResidues
  rw [sum_filter]
  calc
    _ = ∑ a ∈ Icc 1 q,
        (∑ d ∈ q.divisors, if d ∣ a then (moebius d : ℂ) else 0) *
          charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ)) := by
      apply sum_congr rfl
      intro a _
      rw [MathlibNt.SieveTheory.sum_moebius_if_dvd_eq_coprime hq]
      split_ifs <;> simp
    _ = ∑ d ∈ q.divisors, (moebius d : ℂ) *
        ∑ a ∈ Icc 1 q, if d ∣ a then
          charReal (-(a : ℝ) * (N : ℝ) / (q : ℝ)) else 0 := by
      simp only [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = _ := sum_congr rfl fun d hd => by
      rw [phase_sum_on_multiples N (Nat.pos_of_ne_zero hq) hd]

theorem ramanujan_eq_arithmetic (N q : ℕ) :
    ramanujan N q = (ramanujanArithmetic N q : ℂ) := by
  rw [ramanujan_integer_formula]
  simp only [ramanujanArithmetic, mul_apply, divisorWeight_apply]
  push_cast
  exact (Nat.sum_divisorsAntidiagonal (fun d e =>
    (moebius d : ℂ) * (if e ∣ N then (e : ℂ) else 0))).symm

theorem ramanujan_integral (N q : ℕ) : ∃ z : ℤ, ramanujan N q = (z : ℂ) :=
  ⟨ramanujanArithmetic N q, ramanujan_eq_arithmetic N q⟩

theorem ramanujan_mul (N : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) :
    ramanujan N (a * b) = ramanujan N a * ramanujan N b := by
  simp only [ramanujan_eq_arithmetic,
    (ramanujanArithmetic_multiplicative N).map_mul_of_coprime hab, Int.cast_mul]

theorem coefficient_mul (N : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) :
    coefficient N (a * b) = coefficient N a * coefficient N b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  simp only [coefficient, if_neg ha, if_neg hb, if_neg (mul_ne_zero ha hb),
    isMultiplicative_moebius.map_mul_of_coprime hab, Nat.totient_mul hab,
    Int.cast_mul, Nat.cast_mul, ramanujan_mul N hab, mul_pow]
  ring

end LiuWang.Proof.SingularSeries
