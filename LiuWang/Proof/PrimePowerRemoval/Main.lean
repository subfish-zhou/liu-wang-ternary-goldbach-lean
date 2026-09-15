import LiuWang.Proof.ParameterComparisons.Main
import LiuWang.Target
import Mathlib.NumberTheory.Chebyshev

/-!
# 素数幂扣除与正计数出口

直接处理 Interfaces 的有序三重和。窗口限制整数项而非素数底数，
三个坐标彼此独立，允许重复素数。非素数 Λ 质量由 Mathlib 的全域
Chebyshev / Costa-Pereira 不等式控制；不在小参数上使用大参数估计。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.PrimePowerRemoval

open Finset ArithmeticFunction
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open scoped BigOperators

/-- 每个整数项的非素数 Λ 质量。 -/
def primePowerWeight (n : ℕ) : ℝ :=
  vonMangoldt n - primeLogWeight n

theorem primePowerWeight_eq_nonprime (n : ℕ) :
    primePowerWeight n = if n.Prime then 0 else vonMangoldt n := by
  classical
  by_cases hn : n.Prime
  · simp [primePowerWeight, primeLogWeight, hn, vonMangoldt_apply_prime hn]
  · simp [primePowerWeight, primeLogWeight, hn]

private theorem primeLogWeight_nonneg (n : ℕ) : 0 ≤ primeLogWeight n := by
  unfold primeLogWeight
  split_ifs
  · exact Real.log_natCast_nonneg n
  · rfl

private theorem primeLogWeight_le_vonMangoldt (n : ℕ) :
    primeLogWeight n ≤ vonMangoldt n := by
  unfold primeLogWeight
  split_ifs with hn
  · exact (vonMangoldt_apply_prime hn).ge
  · exact vonMangoldt_nonneg

theorem primePowerWeight_nonneg (n : ℕ) : 0 ≤ primePowerWeight n :=
  sub_nonneg.mpr (primeLogWeight_le_vonMangoldt n)

/-- 扣除项精确支撑于非素数的素数幂，而非所有非素数。 -/
theorem primePowerWeight_pos_iff (n : ℕ) :
    0 < primePowerWeight n ↔ IsPrimePow n ∧ ¬n.Prime := by
  rw [primePowerWeight_eq_nonprime]
  by_cases hn : n.Prime <;> simp [hn, vonMangoldt_pos_iff]

theorem primePowerWeight_pos_iff_exists_prime_pow (n : ℕ) :
    0 < primePowerWeight n ↔ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ p ^ k = n := by
  rw [primePowerWeight_pos_iff]
  constructor
  · rintro ⟨hpow, hnot⟩
    obtain ⟨p, k, hp, hk, heq⟩ := (isPrimePow_nat_iff n).1 hpow
    refine ⟨p, k, hp, ?_, heq⟩
    have hk1 : k ≠ 1 := by
      intro h
      apply hnot
      exact heq ▸ (show (p ^ k).Prime by simpa [h] using hp)
    omega
  · rintro ⟨p, k, hp, hk, rfl⟩
    exact ⟨(isPrimePow_nat_iff _).2 ⟨p, k, hp, by omega, rfl⟩,
      Nat.Prime.not_prime_pow hk⟩

private theorem window_subset_Ioc {N : ℕ} (hN : 0 < N) :
    windowFinset N ⊆ Ioc 0 N := by
  intro n hn
  have hn' := (mem_windowSet_iff N n).1 ((mem_windowFinset_iff N n).1 hn)
  simp only [mem_Ioc]
  constructor
  · by_contra h
    have : n = 0 := by omega
    simp [this] at hn'
    omega
  · exact hn'.1

/-- 窗口非素数质量由精确的 ψ - θ 恒等式支付。 -/
theorem primePowerMass_le_psi_sub_theta {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ windowFinset N, primePowerWeight n) ≤
      Chebyshev.psi N - Chebyshev.theta N := by
  classical
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter]
  simp_rw [primePowerWeight_eq_nonprime]
  have hsum :
      (∑ n ∈ windowFinset N, if n.Prime then 0 else vonMangoldt n) ≤
        ∑ n ∈ Ioc 0 N, if n.Prime then 0 else vonMangoldt n :=
    sum_le_sum_of_subset_of_nonneg (window_subset_Ioc hN)
      (fun n _ _ => by split_ifs <;> first | exact le_rfl | exact vonMangoldt_nonneg)
  simpa only [ite_not] using hsum

private theorem psi_sub_theta_le_explicit_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      ((Real.log 4 + 4) * 3) * Real.sqrt x := by
  have hroot (n : ℕ) (hn : 2 ≤ n) :
      Chebyshev.psi (x ^ (1 / (n : ℝ))) ≤
        (Real.log 4 + 4) * Real.sqrt x := by
    calc
      _ ≤ (Real.log 4 + 4) * x ^ (1 / (n : ℝ)) :=
        Chebyshev.psi_le_const_mul_self (by positivity)
      _ ≤ (Real.log 4 + 4) * Real.sqrt x := by
        rw [Real.sqrt_eq_rpow]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hx (by
          have : (2 : ℝ) ≤ n := by exact_mod_cast hn
          exact one_div_le_one_div_of_le (by norm_num) this)
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := hroot 2 (by norm_num)
  have h3 := hroot 3 (by norm_num)
  have h5 := hroot 5 (by norm_num)
  simp only [Nat.cast_ofNat, one_div] at h2 h3 h5
  linarith

/-- 显式常数 3(log 4 + 4) 小于 L，故保留原文的系数 3。 -/
theorem primePowerMass_le_sqrt_mul_log {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∑ n ∈ windowFinset N, primePowerWeight n) ≤
      Real.sqrt N * sourceL N := by
  have hpos := nat_pos_of_exp_le hN
  have hL := sourceL_ge_3100 hN
  have hlog : Real.log 4 ≤ (4 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  calc
    _ ≤ Chebyshev.psi N - Chebyshev.theta N :=
      primePowerMass_le_psi_sub_theta hpos
    _ ≤ ((Real.log 4 + 4) * 3) * Real.sqrt N :=
      psi_sub_theta_le_explicit_sqrt (by exact_mod_cast hpos)
    _ ≤ sourceL N * Real.sqrt N :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

private def triple (N : ℕ) (a b c : ℕ → ℝ) : ℝ :=
  ∑ i ∈ windowFinset N, ∑ j ∈ windowFinset N, ∑ k ∈ windowFinset N,
    if i + j + k = N then a i * b j * c k else 0

private theorem triple_swap (N : ℕ) (a b c : ℕ → ℝ) :
    triple N a b c = triple N b a c := by
  unfold triple
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro k hk
  simp only [Nat.add_comm i j, mul_comm (a i) (b j)]

private theorem triple_rotate (N : ℕ) (a b c : ℕ → ℝ) :
    triple N a b c = triple N c a b := by
  unfold triple
  conv_lhs =>
    arg 2
    ext i
    rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [show i + j + k = k + i + j by omega]
  split_ifs <;> ring

private theorem fixed_sum_le (s : Finset ℕ) (m N : ℕ) (w : ℕ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ k ∈ s, w k ≤ C) :
    (∑ k ∈ s, if m + k = N then w k else 0) ≤ C := by
  classical
  by_cases h : ∃ k ∈ s, m + k = N
  · obtain ⟨k, hk, heq⟩ := h
    rw [sum_eq_single k]
    · simpa only [heq, if_true] using hw k hk
    · intro b hb hbk
      rw [if_neg (by omega)]
    · exact fun hnot => (hnot hk).elim
  · have hz : ∀ k ∈ s, ¬m + k = N := by
      intro k hk heq
      exact h ⟨k, hk, heq⟩
    simpa only [sum_congr rfl (fun k hk => if_neg (hz k hk)), sum_const_zero] using hC

private theorem triple_le_mass {N : ℕ} (hN : 0 < N)
    (a b c : ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i ∈ windowFinset N, 0 ≤ b i ∧ b i ≤ L)
    (hc : ∀ i ∈ windowFinset N, 0 ≤ c i ∧ c i ≤ L) :
    triple N a b c ≤ (N : ℝ) * L ^ 2 * ∑ i ∈ windowFinset N, a i := by
  have hcard : ((windowFinset N).card : ℝ) ≤ N := by
    have := card_le_card (window_subset_Ioc hN)
    simpa using (show ((windowFinset N).card : ℝ) ≤ (Ioc 0 N).card by
      exact_mod_cast this)
  calc
    triple N a b c ≤
        ∑ i ∈ windowFinset N, ∑ _j ∈ windowFinset N, a i * L ^ 2 := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      apply fixed_sum_le _ (i + j) N _ (mul_nonneg (ha i) (sq_nonneg L))
      intro k hk
      calc
        a i * b j * c k = a i * (b j * c k) := by ring
        _ ≤ a i * (L * L) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hb j hj).2 (hc k hk).2 (hc k hk).1 hL) (ha i)
        _ = _ := by ring
    _ = ((windowFinset N).card : ℝ) * L ^ 2 *
        ∑ i ∈ windowFinset N, a i := by
      simp only [sum_const, nsmul_eq_mul, ← mul_sum, ← sum_mul]
      ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))
        (sum_nonneg (fun i _ => ha i))

private theorem triple_sub (N : ℕ) (f g : ℕ → ℝ) :
    triple N f f f - triple N g g g =
      triple N (fun n => f n - g n) f f +
      triple N (fun n => f n - g n) g f +
      triple N (fun n => f n - g n) g g := by
  rw [triple_swap N (fun n => f n - g n) g f,
    ← triple_rotate N g g (fun n => f n - g n)]
  unfold triple
  simp only [← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro k hk
  split_ifs <;> ring

theorem I_nonneg (N : ℕ) : 0 ≤ I N := by
  apply sum_nonneg
  intro i hi
  apply sum_nonneg
  intro j hj
  apply sum_nonneg
  intro k hk
  split_ifs
  · exact mul_nonneg (mul_nonneg (primeLogWeight_nonneg i)
      (primeLogWeight_nonneg j)) (primeLogWeight_nonneg k)
  · exact le_rfl

/-- 非负差额：每个有序三元组逐项比较，不作去重。 -/
theorem I_le_lambdaTripleCount (N : ℕ) : I N ≤ lambdaTripleCount N := by
  apply sum_le_sum
  intro i hi
  apply sum_le_sum
  intro j hj
  apply sum_le_sum
  intro k hk
  split_ifs
  · exact mul_le_mul
      (mul_le_mul (primeLogWeight_le_vonMangoldt i) (primeLogWeight_le_vonMangoldt j)
        (primeLogWeight_nonneg j) vonMangoldt_nonneg)
      (primeLogWeight_le_vonMangoldt k) (primeLogWeight_nonneg k)
      (mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)
  · exact le_rfl

/-- 每个有序整数三元组只出现一次；多个高次幂坐标不会重复计入此恒等式。 -/
theorem lambdaTripleCount_sub_I_eq_nonprime_triples (N : ℕ) :
    lambdaTripleCount N - I N =
      ∑ i ∈ windowFinset N, ∑ j ∈ windowFinset N, ∑ k ∈ windowFinset N,
        if i + j + k = N ∧ (¬i.Prime ∨ ¬j.Prime ∨ ¬k.Prime) then
          vonMangoldt i * vonMangoldt j * vonMangoldt k else 0 := by
  classical
  change triple N vonMangoldt vonMangoldt vonMangoldt -
    triple N primeLogWeight primeLogWeight primeLogWeight = _
  unfold triple
  simp only [← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro k hk
  by_cases hi' : i.Prime <;> by_cases hj' : j.Prime <;> by_cases hk' : k.Prime <;>
    by_cases heq : i + j + k = N <;>
    simp [hi', hj', hk', heq, primeLogWeight, vonMangoldt_apply_prime]

/-- 主文 (3.10)--(3.12) 的实际有限和扣除界，保留原系数与实数幂。 -/
theorem lambdaTripleCount_sub_I_le {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    lambdaTripleCount N - I N ≤
      3 * (N : ℝ) ^ ((3 : ℝ) / 2) * sourceL N ^ (3 : ℕ) := by
  have hpos := nat_pos_of_exp_le hN
  have hL : 0 ≤ sourceL N := by linarith [sourceL_ge_3100 hN]
  have hb (n : ℕ) (hn : n ∈ windowFinset N) :
      0 ≤ vonMangoldt n ∧ vonMangoldt n ≤ sourceL N := by
    have hn' := mem_Ioc.mp (window_subset_Ioc hpos hn)
    exact ⟨vonMangoldt_nonneg, vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn'.1) (by exact_mod_cast hn'.2))⟩
  have hg (n : ℕ) (hn : n ∈ windowFinset N) :
      0 ≤ primeLogWeight n ∧ primeLogWeight n ≤ sourceL N :=
    ⟨primeLogWeight_nonneg n, (primeLogWeight_le_vonMangoldt n).trans (hb n hn).2⟩
  have h0 := triple_le_mass hpos (primePowerWeight) vonMangoldt vonMangoldt hL
    primePowerWeight_nonneg hb hb
  have h1 := triple_le_mass hpos (primePowerWeight) primeLogWeight vonMangoldt hL
    primePowerWeight_nonneg hg hb
  have h2 := triple_le_mass hpos (primePowerWeight) primeLogWeight primeLogWeight hL
    primePowerWeight_nonneg hg hg
  have hfinite : lambdaTripleCount N - I N ≤
      (3 * (N : ℝ) * sourceL N ^ 2) * ∑ n ∈ windowFinset N, primePowerWeight n := by
    change triple N vonMangoldt vonMangoldt vonMangoldt -
      triple N primeLogWeight primeLogWeight primeLogWeight ≤ _
    rw [triple_sub]
    change triple N primePowerWeight vonMangoldt vonMangoldt +
      triple N primePowerWeight primeLogWeight vonMangoldt +
      triple N primePowerWeight primeLogWeight primeLogWeight ≤ _
    linarith
  have hr : (N : ℝ) * Real.sqrt N = (N : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    nth_rw 1 [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add (natCast_pos_of_exp_le hN)]
    norm_num
  calc
    _ ≤ (3 * (N : ℝ) * sourceL N ^ 2) *
        ∑ n ∈ windowFinset N, primePowerWeight n := hfinite
    _ ≤ (3 * (N : ℝ) * sourceL N ^ 2) * (Real.sqrt N * sourceL N) :=
      mul_le_mul_of_nonneg_left (primePowerMass_le_sqrt_mul_log hN) (by positivity)
    _ = 3 * ((N : ℝ) * Real.sqrt N) * sourceL N ^ (3 : ℕ) := by ring
    _ = _ := by rw [hr]

theorem primePowerRemoval {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    0 ≤ lambdaTripleCount N - I N ∧
      lambdaTripleCount N -
        3 * (N : ℝ) ^ ((3 : ℝ) / 2) * sourceL N ^ (3 : ℕ) ≤ I N := by
  constructor
  · exact sub_nonneg.mpr (I_le_lambdaTripleCount N)
  · linarith [lambdaTripleCount_sub_I_le hN]

private theorem exists_pos_of_sum_pos {s : Finset ℕ} {f : ℕ → ℝ}
    (h : 0 < ∑ n ∈ s, f n) : ∃ n ∈ s, 0 < f n := by
  contrapose! h
  exact sum_nonpos h

/-- 从真实有限和的正性提取三个窗口内的素数；不预设表示存在。 -/
theorem exists_window_primes_of_I_pos {N : ℕ} (hI : 0 < I N) :
    ∃ p ∈ windowFinset N, ∃ q ∈ windowFinset N, ∃ r ∈ windowFinset N,
      p.Prime ∧ q.Prime ∧ r.Prime ∧ N = p + q + r := by
  unfold I at hI
  obtain ⟨p, hp, hsum⟩ := exists_pos_of_sum_pos hI
  obtain ⟨q, hq, hsum⟩ := exists_pos_of_sum_pos hsum
  obtain ⟨r, hr, hprod⟩ := exists_pos_of_sum_pos hsum
  split_ifs at hprod with heq
  · have hpp : p.Prime := by
      by_contra h
      simp [primeLogWeight, h] at hprod
    have hqp : q.Prime := by
      by_contra h
      simp [primeLogWeight, h] at hprod
    have hrp : r.Prime := by
      by_contra h
      simp [primeLogWeight, h] at hprod
    exact ⟨p, hp, q, hq, r, hr, hpp, hqp, hrp, heq.symm⟩
  · exact (lt_irrefl 0 hprod).elim

private theorem window_member_gt_two {N n : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hn : n ∈ windowFinset N) : 2 < n := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_ge_3100 hN
  have hpow : sourceL N ≤ sourceT N := by
    simpa only [sourceT, pow_one] using
      (pow_le_pow_right₀ (one_le_sourceL h2000) (show 1 ≤ 15 by norm_num))
  have hn' := sourceT_lt_window_member h2000 ((mem_windowFinset_iff N n).1 hn)
  have : (2 : ℝ) < n := by linarith
  exact_mod_cast this

/-- 在目标域，窗口排除素数 2，因此正 I 给出三个奇素数（可重复）。 -/
theorem isThreeOddPrimeSum_of_I_pos {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hI : 0 < I N) :
    LiuWang.IsThreeOddPrimeSum N := by
  obtain ⟨p, hp, q, hq, r, hr, hpp, hqp, hrp, heq⟩ :=
    exists_window_primes_of_I_pos hI
  exact ⟨p, q, r, hpp, hqp, hrp,
    hpp.odd_of_ne_two (ne_of_gt (window_member_gt_two hN hp)),
    hqp.odd_of_ne_two (ne_of_gt (window_member_gt_two hN hq)),
    hrp.odd_of_ne_two (ne_of_gt (window_member_gt_two hN hr)), heq⟩

/-- 实际差额进入已验的原系数末端预算。 -/
theorem lambdaTripleCount_sub_I_lt_budget {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    lambdaTripleCount N - I N < (3 / 1000 : ℝ) * (N : ℝ) ^ (2 : ℕ) :=
  (lambdaTripleCount_sub_I_le hN).trans_lt
    (LiuWang.Proof.ParameterComparisons.primePower_scalar_lt
      (exp_2000_le_of_exp_3100_le hN))

/-- 仅作后续解析生产者的消费出口；这里不证明所假设的 Λ 计数下界。 -/
theorem I_lower_bound_of_lambda_lower_bound {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hLambda : (0.5437 - 0.51 : ℝ) * (N : ℝ) ^ (2 : ℕ) ≤ lambdaTripleCount N) :
    (0.03 : ℝ) * (N : ℝ) ^ (2 : ℕ) ≤ I N := by
  have hremove := (primePowerRemoval hN).2
  have hscalar := LiuWang.Proof.ParameterComparisons.final_scalar_source hN
  linarith

theorem isThreeOddPrimeSum_of_lambda_lower_bound {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hLambda : (0.5437 - 0.51 : ℝ) * (N : ℝ) ^ (2 : ℕ) ≤ lambdaTripleCount N) :
    LiuWang.IsThreeOddPrimeSum N := by
  apply isThreeOddPrimeSum_of_I_pos hN
  exact lt_of_lt_of_le (mul_pos (by norm_num) (sq_pos_of_pos (natCast_pos_of_exp_le hN)))
    (I_lower_bound_of_lambda_lower_bound hN hLambda)

end LiuWang.Proof.PrimePowerRemoval
