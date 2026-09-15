import LiuWang.Proof.SourceRoute.MajorException.SourceTotal
import LiuWang.Proof.SingularSeries.Decimal.Kernel

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Classical Finset
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation

inductive MassKind
  | squarefree
  | all
  deriving DecidableEq

def massTerm : MassKind → ℕ → ℝ
  | .squarefree, n => moebiusWeight n / (n.totient : ℝ)^2
  | .all, n => 1 / (n.totient : ℝ)^2

theorem massTerm_nonneg (j : MassKind) (n : ℕ) : 0 ≤ massTerm j n := by
  cases j <;> dsimp [massTerm, moebiusWeight] <;> positivity

theorem massTerm_zero (j : MassKind) : massTerm j 0 = 0 := by
  cases j <;> simp [massTerm, moebiusWeight]

theorem massTerm_one (j : MassKind) : massTerm j 1 = 1 := by
  cases j <;> norm_num [massTerm, moebiusWeight]

theorem massTerm_le_all (j : MassKind) (n : ℕ) :
    massTerm j n ≤ 1/(n.totient : ℝ)^2 := by
  cases j with
  | all => rfl
  | squarefree =>
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    rw [moebiusWeight_eq]
    split_ifs <;> norm_num

theorem massTerm_mul (j : MassKind) {m n : ℕ} (h : Nat.Coprime m n) :
    massTerm j (m*n) = massTerm j m * massTerm j n := by
  cases j with
  | all => simp [massTerm, Nat.totient_mul h, mul_pow, mul_comm]
  | squarefree =>
    simp only [massTerm, moebiusWeight, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h,
      Int.cast_mul, abs_mul, Nat.totient_mul h, Nat.cast_mul, mul_pow, mul_div_mul_comm]

theorem massTerm_summable (j : MassKind) : Summable (massTerm j) := by
  apply summable_of_sum_le (massTerm_nonneg j) (c := 44)
  intro s
  have he : (∑ n ∈ s, massTerm j n) = ∑ n ∈ s.erase 0, massTerm j n := by
    rw [sum_erase _ (massTerm_zero j)]
  rw [he]
  calc
    _ ≤ ∑ n ∈ Icc 1 (s.sup id), massTerm j n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have ht := mem_erase.mp hn
        exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero ht.1, le_sup (f := id) ht.2⟩
      · intro n _ _
        exact massTerm_nonneg j n
    _ ≤ ∑ n ∈ Icc 1 (s.sup id), 1/(n.totient : ℝ)^2 :=
      sum_le_sum (fun n _ => massTerm_le_all j n)
    _ ≤ 44 := by
      simpa using Uniform.inverse_totient_tail_finite (m := 1) (B := s.sup id) (by norm_num)

theorem massTerm_norm_summable (j : MassKind) : Summable (fun n => ‖massTerm j n‖) := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (massTerm_nonneg j _)] using massTerm_summable j

def localMass : MassKind → ℝ → ℝ
  | .squarefree, p => 1 + 1/(p-1)^2
  | .all, p => 1 + p^2/((p-1)^2*(p^2-1))

theorem massTerm_all_prime_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    massTerm .all (p^(k+1)) = (1/((p : ℝ)-1)^2) * (1/(p : ℝ)^2)^k := by
  simp only [massTerm, Nat.totient_prime_pow hp (by omega : 0 < k+1),
    Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one,
    Nat.cast_pow, mul_pow, one_div, mul_inv_rev, inv_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2, mul_comm]

theorem massTerm_all_local {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => massTerm .all (p^k)) (localMass .all p) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr : (1/(p : ℝ)^2) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    nlinarith
  have hg := (hasSum_geometric_of_lt_one (by positivity) hr).mul_left
    (1/((p : ℝ)-1)^2)
  have he : (1/((p : ℝ)-1)^2) * (1-1/(p : ℝ)^2)⁻¹ =
      localMass .all p - massTerm .all (p^0) := by
    simp only [localMass, pow_zero, massTerm_one]
    field_simp
    ring
  rw [he] at hg
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [massTerm_all_prime_succ hp, sum_range_one] using hg

theorem massTerm_squarefree_prime_ge_two {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    massTerm .squarefree (p^k) = 0 := by
  simp [massTerm, moebiusWeight,
    ArithmeticFunction.moebius_apply_prime_pow hp (by omega : k ≠ 0),
    show k ≠ 1 by omega]

theorem localMass_eq_tsum {p : ℕ} (hp : p.Prime) (j : MassKind) :
    localMass j p = ∑' k : ℕ, massTerm j (p^k) := by
  cases j with
  | all => exact (massTerm_all_local hp).tsum_eq.symm
  | squarefree =>
    rw [tsum_eq_sum (s := {0, 1}) (fun k hk =>
      massTerm_squarefree_prime_ge_two hp (by simp only [mem_insert, mem_singleton] at hk; omega))]
    simp [massTerm, moebiusWeight, localMass, ArithmeticFunction.moebius_apply_prime hp,
      Nat.totient_prime hp, Nat.cast_sub hp.one_le]

theorem mass_euler_tendsto (j : MassKind) :
    Filter.Tendsto (fun B : ℕ => ∏ p ∈ B.primesBelow, localMass j p)
      Filter.atTop (nhds (∑' n : ℕ, massTerm j n)) := by
  have h := EulerProduct.eulerProduct (massTerm_one j)
    (fun {_ _} hc => massTerm_mul j hc) (massTerm_norm_summable j) (massTerm_zero j)
  convert h using 1
  ext B
  apply prod_congr rfl
  intro p hp
  exact localMass_eq_tsum (Nat.mem_primesBelow.mp hp).2 j

def zetaCorrection : MassKind → ℝ → ℝ
  | .squarefree, p => 2/(p^2*(p-1))
  | .all, p => (2*p-1)/(p^2*(p-1)^2)

theorem localMass_zeta_factor (j : MassKind) {p : ℝ} (hp : 1 < p) :
    localMass j p = (1+zetaCorrection j p) / Decimal.b p := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p-1 ≠ 0 := by linarith
  have hp2 : p^2-1 ≠ 0 := by nlinarith
  have hb := (Decimal.b_pos hp).ne'
  cases j <;> unfold localMass zetaCorrection Decimal.b at * <;> field_simp <;> ring

end LiuWang.Proof.SourceRoute.MajorException.Continuation
