import LiuWang.Proof.Campaign20260915.RSMertensTransport.ThetaMoment

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.Mertens
open Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.RSMertensTransport

theorem logarithmicCorrection_window_eq {m n : ℕ} (hmn : m ≤ n) :
    logarithmicCorrection n - logarithmicCorrection m =
      ∑ p ∈ Finset.Ioc m n, logarithmicCorrectionTerm p := by
  have hs := Finset.sum_Ico_eq_sub logarithmicCorrectionTerm (Nat.succ_le_succ hmn)
  simp only [Nat.succ_eq_add_one] at hs
  rw [Finset.Ico_add_one_add_one_eq_Ioc,
    ← logarithmicCorrection_eq_sum_range, ← logarithmicCorrection_eq_sum_range] at hs
  exact hs.symm

theorem logarithmicCorrection_window_le_of_theta {x y C : ℝ}
    (hx : 1 < x) (hxy : x ≤ y) (hC : 0 ≤ C)
    (htheta : ∀ t ∈ Set.Icc x y, Chebyshev.theta t ≤ C * t) :
    logarithmicCorrection ⌊y⌋₊ - logarithmicCorrection ⌊x⌋₊ ≤
      C / ((x - 1) * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hxl := Real.log_pos hx
  have hxm : 0 < x - 1 := by linarith
  let K : ℝ := x / (2 * (x - 1) * Real.log x)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  rw [logarithmicCorrection_window_eq (Nat.floor_le_floor hxy)]
  calc
    (∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, logarithmicCorrectionTerm p) ≤
        ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
          K * (if p.Prime then Real.log p / (p : ℝ) ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hprime : p.Prime
      · rw [if_pos hprime]
        exact logarithmicCorrection_prime_le_weighted_square hx hprime
          ((Nat.floor_lt hx0.le).mp (Finset.mem_Ioc.mp hp).1)
      · simp [logarithmicCorrectionTerm, hprime]
    _ = K * (∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        if p.Prime then Real.log p / (p : ℝ) ^ 2 else 0) := by rw [Finset.mul_sum]
    _ ≤ K * (2 * C / x) :=
      mul_le_mul_of_nonneg_left (prime_log_square_window_le hx0 hxy hC htheta) hK
    _ = C / ((x - 1) * Real.log x) := by
      dsimp [K]
      field_simp

theorem logarithmicCorrection_tail_le_of_theta {x C : ℝ}
    (hx : 1 < x) (hC : 0 ≤ C)
    (htheta : ∀ t ∈ Set.Ici x, Chebyshev.theta t ≤ C * t) :
    logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊ ≤
      C / ((x - 1) * Real.log x) := by
  apply le_of_tendsto (tendsto_logarithmicCorrection.sub_const
    (logarithmicCorrection ⌊x⌋₊))
  filter_upwards [eventually_ge_atTop (⌊x⌋₊ + 1)] with n hn
  have hxn : x ≤ (n : ℝ) :=
    (Nat.lt_floor_add_one x).le.trans (by exact_mod_cast hn)
  simpa only [Nat.floor_natCast] using logarithmicCorrection_window_le_of_theta
    hx hxn hC (fun t ht => htheta t ht.1)

/-- The numerical hypothesis is precisely the needed tail of RS Theorem 9. -/
theorem logarithmicCorrection_tail_le_original_of_theta {x : ℝ}
    (hx : 1 < x)
    (htheta : ∀ t ∈ Set.Ici x, Chebyshev.theta t ≤ 1.02 * t) :
    0 ≤ logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊ ∧
      logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊ ≤
        1.02 / ((x - 1) * Real.log x) :=
  ⟨logarithmicCorrection_tail_nonneg _,
    logarithmicCorrection_tail_le_of_theta hx (by norm_num) htheta⟩

theorem logarithmicCorrection_tail_norm_le_original_of_theta {x : ℝ}
    (hx : 1 < x)
    (htheta : ∀ t ∈ Set.Ici x, Chebyshev.theta t ≤ 1.02 * t) :
    ‖logarithmicCorrectionLimit - logarithmicCorrection ⌊x⌋₊‖ ≤
      1.02 / ((x - 1) * Real.log x) := by
  rw [Real.norm_eq_abs, logarithmicCorrection_tail_abs]
  exact (logarithmicCorrection_tail_le_original_of_theta hx htheta).2

#print axioms logarithmicCorrection_window_eq
#print axioms logarithmicCorrection_window_le_of_theta
#print axioms logarithmicCorrection_tail_le_of_theta
#print axioms logarithmicCorrection_tail_le_original_of_theta
#print axioms logarithmicCorrection_tail_norm_le_original_of_theta

end LiuWang.Proof.Campaign20260915.RSMertensTransport
