import LiuWang.Proof.Parameters.Main
import BombieriVinogradov.Helpers.ArithmeticFunction.NonCoprimeMangoldtBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveCharacters

/-!
# Finite character expansion on the exact Liu--Wang window

The Gauss coefficient uses the conjugate character, whereas `twistedS` uses
the character itself. The error is the actual noncoprime part of `S`, not an
independent remainder parameter. No estimate for psi is used.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.CharacterExpansion

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open AnalyticNumberTheory.LargeSieve
open scoped BigOperators

def twistedS {q : Nat} (N : Nat) (η : Real) (χ : Character q) : Complex :=
  ∑ n ∈ windowFinset N,
    (ArithmeticFunction.vonMangoldt n : Complex) * χ (n : ZMod q) *
      charReal ((n : Real) * η)

def G {q : Nat} [NeZero q] (a : Nat) (χ : Character q) : Complex :=
  gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (a : ZMod q))

def nonCoprimeError (N q : Nat) (α : Real) : Complex :=
  ∑ n ∈ (windowFinset N).filter (fun n => ¬ Nat.Coprime n q),
    (ArithmeticFunction.vonMangoldt n : Complex) * charReal ((n : Real) * α)

theorem stdAddChar_nat {q : Nat} [NeZero q] (n : Nat) :
    ZMod.stdAddChar (n : ZMod q) = charReal ((n : Real) / (q : Real)) := by
  have h := ZMod.stdAddChar_coe (N := q) (n : Int)
  rw [Int.cast_natCast] at h
  rw [h]
  unfold charReal
  congr 1
  push_cast
  ring

theorem rational_phase {q : Nat} [NeZero q] (a n : Nat) :
    ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) =
      charReal ((n : Real) * rationalCenter a q) := by
  rw [← Nat.cast_mul, stdAddChar_nat]
  congr 1
  simp only [Nat.cast_mul, rationalCenter]
  ring

theorem G_eq_conjugate_sum {q : Nat} [NeZero q] (a : Nat) (χ : Character q) :
    G a χ = ∑ l : ZMod q,
      star (χ l) * charReal ((a : Real) * (l.val : Real) / (q : Real)) := by
  unfold G gaussSum
  apply Finset.sum_congr rfl
  intro l _
  rw [MulChar.star_apply', AddChar.mulShift_apply]
  congr 1
  nth_rw 1 [← ZMod.natCast_zmod_val l]
  rw [rational_phase]
  congr 1
  unfold rationalCenter
  ring

theorem G_eq_inverse_gauss {q : Nat} [NeZero q] (a : Nat) (χ : Character q) :
    G a χ = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (a : ZMod q)) :=
  rfl

theorem gauss_twistedS_reindex {q : Nat} [NeZero q] (N a : Nat) (η : Real) :
    (∑ χ : Character q, G a χ * twistedS N η χ) =
      ∑ χ : Character q,
        gaussSum χ (ZMod.stdAddChar.mulShift (a : ZMod q)) *
          twistedS N η χ⁻¹ := by
  exact Fintype.sum_equiv (Equiv.inv (Character q)) _ _ (by intro χ; simp [G])

theorem character_kernel {q : Nat} [NeZero q] (a : Nat) (n : ZMod q) :
    (∑ χ : Character q, G a χ * χ n) =
      if IsUnit n then
        (q.totient : Complex) * ZMod.stdAddChar ((a : ZMod q) * n)
      else 0 := by
  classical
  simp only [G, gaussSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner (l : ZMod q) :
      (∑ χ : Character q,
        χ⁻¹ l * ZMod.stdAddChar.mulShift (a : ZMod q) l * χ n) =
        ZMod.stdAddChar.mulShift (a : ZMod q) l *
          (if IsUnit n ∧ IsUnit l ∧ n = l then (q.totient : Complex) else 0) := by
    calc
      _ = ZMod.stdAddChar.mulShift (a : ZMod q) l *
          ∑ χ : Character q, χ n * star (χ l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ _
        rw [MulChar.star_apply']
        ring
      _ = _ := by
        have h := charOrthSum (NeZero.pos q) n l
        by_cases hp : IsUnit n ∧ IsUnit l ∧ n = l
        · simpa [hp] using congrArg (ZMod.stdAddChar.mulShift (a : ZMod q) l * ·) h
        · simpa [hp] using congrArg (ZMod.stdAddChar.mulShift (a : ZMod q) l * ·) h
  simp_rw [hinner]
  by_cases hn : IsUnit n
  · have hc (l : ZMod q) : (IsUnit n ∧ IsUnit l ∧ n = l) ↔ l = n := by
      constructor
      · exact fun h => h.2.2.symm
      · rintro rfl
        exact ⟨hn, hn, rfl⟩
    simp_rw [hc]
    simp [hn, mul_comm, AddChar.mulShift_apply]
  · simp [hn]

theorem S_character_expansion {q : Nat} [NeZero q] (N a : Nat) (η : Real) :
    S N (rationalCenter a q + η) =
      (q.totient : Complex)⁻¹ *
        (∑ χ : Character q, G a χ * twistedS N η χ) +
      nonCoprimeError N q (rationalCenter a q + η) := by
  classical
  have hφ : (q.totient : Complex) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hsum :
      (∑ χ : Character q, G a χ * twistedS N η χ) =
        (q.totient : Complex) *
          ∑ n ∈ (windowFinset N).filter (fun n => Nat.Coprime n q),
            (ArithmeticFunction.vonMangoldt n : Complex) *
              charReal ((n : Real) * (rationalCenter a q + η)) := by
    simp only [twistedS, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    calc
      (∑ χ : Character q, G a χ *
          ((ArithmeticFunction.vonMangoldt n : Complex) * χ (n : ZMod q) *
            charReal ((n : Real) * η))) =
          (ArithmeticFunction.vonMangoldt n : Complex) * charReal ((n : Real) * η) *
            ∑ χ : Character q, G a χ * χ (n : ZMod q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = _ := by
        rw [character_kernel]
        have hu : IsUnit (n : ZMod q) ↔ Nat.Coprime n q := ZMod.isUnit_iff_coprime n q
        simp only [hu, rational_phase, mul_add, charReal_add]
        split_ifs <;> ring
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hφ, one_mul]
  exact (Finset.sum_filter_add_sum_filter_not (windowFinset N)
    (fun n => Nat.Coprime n q)
    (fun n => (ArithmeticFunction.vonMangoldt n : Complex) *
      charReal ((n : Real) * (rationalCenter a q + η)))).symm

theorem norm_nonCoprimeError_le_mass (N q : Nat) (α : Real) :
    ‖nonCoprimeError N q α‖ ≤
      ∑ n ∈ (windowFinset N).filter (fun n => ¬ Nat.Coprime n q),
        ArithmeticFunction.vonMangoldt n := by
  unfold nonCoprimeError
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro n _
  have he : ‖charReal ((n : Real) * α)‖ = 1 := by
    simp [charReal, Complex.norm_exp]
  rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

theorem window_nonCoprime_mass_le_prefix {N : Nat} (hN : 0 < N) (q : Nat) :
    (∑ n ∈ (windowFinset N).filter (fun n => ¬ Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n) ≤
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hn, hcop⟩ := Finset.mem_filter.mp hn
    have hw := (mem_windowSet_iff N n).1 ((mem_windowFinset_iff N n).1 hn)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hw.1⟩, hcop⟩
  · intro n _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

theorem norm_nonCoprimeError_le_log {N q : Nat} (hN : 0 < N) (hq : 0 < q)
    (α : Real) :
    ‖nonCoprimeError N q α‖ ≤ Real.log q * sourceL N / Real.log 2 :=
  (norm_nonCoprimeError_le_mass N q α).trans
    ((window_nonCoprime_mass_le_prefix hN q).trans
      (BombieriVinogradov.nonCoprimeMangoldtSum_le_log_mul_log hq.ne' hN))

theorem log_modulus_le_sourceL {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 0 < q)
    (hqP : (q : Real) ≤ sourceP1 N) :
    Real.log q ≤ sourceL N := by
  calc
    Real.log q ≤ Real.log (sourceP1 N) :=
      Real.log_le_log (by exact_mod_cast hq) hqP
    _ = 6 * Real.log (sourceL N) := log_sourceP1 N
    _ ≤ sourceL N := (nat_mul_log_lt (k := 6) (sourceL_ge_2000 hN) (by norm_num)).le

theorem norm_nonCoprimeError_le_source {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 0 < q)
    (hqP : (q : Real) ≤ sourceP1 N) (α : Real) :
    ‖nonCoprimeError N q α‖ ≤ sourceL N ^ 2 / Real.log 2 := by
  refine (norm_nonCoprimeError_le_log (nat_pos_of_exp_le hN) hq α).trans ?_
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : Real) < 2)).le
  simpa [pow_two] using mul_le_mul_of_nonneg_right
    (log_modulus_le_sourceL hN hq hqP) (sourceL_pos hN).le

@[simp] theorem nonCoprimeError_one (N : Nat) (α : Real) :
    nonCoprimeError N 1 α = 0 := by
  simp [nonCoprimeError]

theorem S_character_expansion_source {N a q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hi : sourceIndex a q)
    (hqP : (q : Real) ≤ sourceP1 N) (η : Real) :
    let : NeZero q := ⟨by have := hi.1.trans hi.2.1; omega⟩
    S N (rationalCenter a q + η) =
      (q.totient : Complex)⁻¹ * (∑ χ : Character q, G a χ * twistedS N η χ) +
        nonCoprimeError N q (rationalCenter a q + η) ∧
    ‖nonCoprimeError N q (rationalCenter a q + η)‖ ≤
      sourceL N ^ 2 / Real.log 2 := by
  let : NeZero q := ⟨by have := hi.1.trans hi.2.1; omega⟩
  exact ⟨S_character_expansion N a η,
    norm_nonCoprimeError_le_source hN (hi.1.trans hi.2.1) hqP _⟩

end LiuWang.Proof.CharacterExpansion
