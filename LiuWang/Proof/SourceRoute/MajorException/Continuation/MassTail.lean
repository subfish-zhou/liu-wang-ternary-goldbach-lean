import LiuWang.Proof.SourceRoute.MajorException.Continuation.MassLocal

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Classical Finset
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation

theorem zetaCorrection_nonneg (j : MassKind) {p : ℝ} (hp : 1 < p) :
    0 ≤ zetaCorrection j p := by
  have hp1 : 0 < p-1 := by linarith
  have hp2 : 0 < 2*p-1 := by linarith
  cases j <;> dsimp [zetaCorrection] <;> positivity

theorem zetaCorrection_nat_nonneg (j : MassKind) (p : ℕ) :
    0 ≤ zetaCorrection j p := by
  by_cases h0 : p = 0
  · subst p
    cases j <;> norm_num [zetaCorrection]
  by_cases h1 : p = 1
  · subst p
    cases j <;> norm_num [zetaCorrection]
  exact zetaCorrection_nonneg j (by exact_mod_cast (show 1 < p by omega))

theorem zetaCorrection_le_cube (j : MassKind) {p : ℝ} (hp : 5 ≤ p) :
    zetaCorrection j p ≤ 3/p^3 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p-1 := by linarith
  cases j <;> dsimp [zetaCorrection] <;> field_simp <;> nlinarith [sq_nonneg (p-3)]

theorem correction_tail (j : MassKind) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 100 < p) :
    (∑ p ∈ s, zetaCorrection j p) ≤ (3/40000 : ℝ) := by
  have ht := Decimal.odd_tail_finite s (by
    intro p hp
    have h := hs p hp
    exact ⟨h.2, h.1.odd_of_ne_two (by omega)⟩)
  calc
    _ ≤ ∑ p ∈ s, 3/(p : ℝ)^3 := by
      apply sum_le_sum
      intro p hp
      apply zetaCorrection_le_cube
      exact_mod_cast (show 5 ≤ p by have := (hs p hp).2; omega)
    _ = 3 * ∑ p ∈ s, 1/(p : ℝ)^3 := by rw [mul_sum]; congr 1; ext p; ring
    _ ≤ _ := by linarith

theorem correction_tail_product (j : MassKind) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 100 < p) :
    (∏ p ∈ s, (1+zetaCorrection j p)) ≤ 1/(1-(3/40000 : ℝ)) := by
  calc
    _ ≤ Real.exp (∑ p ∈ s, zetaCorrection j p) := by
      apply Real.prod_one_add_le_exp_sum
      exact zetaCorrection_nat_nonneg j
    _ ≤ Real.exp (3/40000) := Real.exp_le_exp.mpr (correction_tail j s hs)
    _ ≤ _ := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)

def correctionHead (j : MassKind) : ℝ :=
  (1+zetaCorrection j 2) * ∏ p ∈ Decimal.oddPrimes 100, (1+zetaCorrection j p)

theorem correctionHead_pos (j : MassKind) : 0 < correctionHead j := by
  apply mul_pos
  · have := zetaCorrection_nonneg j (p := 2) (by norm_num)
    linarith
  · apply prod_pos
    intro p hp
    have := zetaCorrection_nonneg j
      (show (1 : ℝ) < p by exact_mod_cast (Decimal.mem_oddPrimes.mp hp).2.1.one_lt)
    linarith

theorem correction_product_bound (j : MassKind) {B : ℕ} (hB : 100 ≤ B) :
    (∏ p ∈ (range (B+1)).filter Nat.Prime, (1+zetaCorrection j p)) ≤
      correctionHead j / (1-(3/40000 : ℝ)) := by
  rw [Decimal.prime_filter_split (by omega), prod_insert (by simp [Decimal.mem_oddPrimes]),
    Decimal.odd_product_split (fun p => 1+zetaCorrection j p) hB, ← mul_assoc]
  change correctionHead j * _ ≤ _
  have ht := correction_tail_product j
    ((Decimal.oddPrimes B).filter (fun p => 100 < p)) (by
      intro p hp
      exact ⟨(Decimal.mem_oddPrimes.mp (mem_filter.mp hp).1).2.1, (mem_filter.mp hp).2⟩)
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left ht (correctionHead_pos j).le

theorem mass_product_bound (j : MassKind) {B : ℕ} (hB : 100 ≤ B) :
    (∏ p ∈ (range (B+1)).filter Nat.Prime, localMass j p) ≤
      (Real.pi^2/6) * correctionHead j / (1-(3/40000 : ℝ)) := by
  have he :
      (∏ p ∈ (range (B+1)).filter Nat.Prime, localMass j p) =
      (∏ p ∈ (range (B+1)).filter Nat.Prime, Decimal.b p)⁻¹ *
        ∏ p ∈ (range (B+1)).filter Nat.Prime, (1+zetaCorrection j p) := by
    rw [← prod_inv_distrib, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    rw [localMass_zeta_factor j (by exact_mod_cast (mem_filter.mp hp).2.one_lt)]
    ring
  rw [he]
  have hz := Decimal.finite_zeta_inverse_upper (range (B+1))
  have hc := correction_product_bound j hB
  have hc0 : 0 ≤ ∏ p ∈ (range (B+1)).filter Nat.Prime, (1+zetaCorrection j p) := by
    apply prod_nonneg
    intro p hp
    have := zetaCorrection_nonneg j
      (show (1 : ℝ) < p by exact_mod_cast (mem_filter.mp hp).2.one_lt)
    linarith
  exact (mul_le_mul hz hc hc0 (by positivity)).trans_eq (by ring)

theorem totalMass_analytic_bound (j : MassKind) :
    (∑' n : ℕ, massTerm j n) ≤
      (Real.pi^2/6) * correctionHead j / (1-(3/40000 : ℝ)) := by
  apply le_of_tendsto (mass_euler_tendsto j)
  filter_upwards [Filter.eventually_ge_atTop 101] with B hB
  have he : B = (B-1)+1 := by omega
  rw [he, Nat.primesBelow]
  exact mass_product_bound j (by omega)

theorem finiteMass_analytic_bound (j : MassKind) (X : ℕ) :
    (∑ n ∈ Icc 1 X, massTerm j n) ≤
      (Real.pi^2/6) * correctionHead j / (1-(3/40000 : ℝ)) :=
  ((massTerm_summable j).sum_le_tsum (Icc 1 X) (fun n _ => massTerm_nonneg j n)).trans
    (totalMass_analytic_bound j)

end LiuWang.Proof.SourceRoute.MajorException.Continuation
