import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Finset

namespace LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections

def higherPrimePowers (x : ℝ) : ℝ :=
  Chebyshev.psi x - Chebyshev.theta x - Chebyshev.theta (Real.sqrt x)

theorem psi_sub_theta_eq_sqrt_add_sum {x : ℝ} (hx : 0 ≤ x)
    {N : ℕ} (hN2 : 2 ≤ N) (hN : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    Chebyshev.psi x - Chebyshev.theta x =
      Chebyshev.theta (Real.sqrt x) +
        ∑ k ∈ Icc 3 N, Chebyshev.theta (x ^ (1 / (k : ℝ))) := by
  rw [Chebyshev.psi_eq_sum_theta' hx hN,
    ← add_sum_Ioc_eq_sum_Icc (by omega : 1 ≤ N),
    show Ioc 1 N = Icc 2 N by ext k; simp only [mem_Ioc, mem_Icc]; omega,
    ← add_sum_Ioc_eq_sum_Icc hN2,
    show Ioc 2 N = Icc 3 N by ext k; simp only [mem_Ioc, mem_Icc]; omega]
  simp only [Nat.cast_one, div_one, Real.rpow_one, Nat.cast_ofNat]
  rw [← Real.sqrt_eq_rpow]
  ring

theorem higherPrimePowers_eq_sum {x : ℝ} (hx : 0 ≤ x)
    {N : ℕ} (hN2 : 2 ≤ N) (hN : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    higherPrimePowers x =
      ∑ k ∈ Icc 3 N, Chebyshev.theta (x ^ (1 / (k : ℝ))) := by
  unfold higherPrimePowers
  rw [psi_sub_theta_eq_sqrt_add_sum hx hN2 hN]
  ring

theorem higherPrimePowers_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ higherPrimePowers x := by
  rw [higherPrimePowers_eq_sum hx (le_max_left 2 _)
    (le_max_right 2 ⌊Real.log x / Real.log 2⌋₊)]
  exact sum_nonneg fun k _ => Chebyshev.theta_nonneg _

theorem sqrt_theta_le_psi_sub_theta {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.theta (Real.sqrt x) ≤ Chebyshev.psi x - Chebyshev.theta x :=
  sub_nonneg.mp (higherPrimePowers_nonneg hx)

theorem higherPrimePowers_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    higherPrimePowers x ≤ higherPrimePowers y := by
  let N := max 2 (max ⌊Real.log x / Real.log 2⌋₊ ⌊Real.log y / Real.log 2⌋₊)
  have hN2 : 2 ≤ N := le_max_left _ _
  rw [higherPrimePowers_eq_sum hx hN2
      ((le_max_left _ _).trans (le_max_right _ _)),
    higherPrimePowers_eq_sum (hx.trans hxy) hN2
      ((le_max_right _ _).trans (le_max_right _ _))]
  apply sum_le_sum
  intro k _
  exact Chebyshev.theta_mono (Real.rpow_le_rpow hx hxy (by positivity))

theorem higherPrimePowers_le_elementary_sum {x : ℝ} (hx : 0 ≤ x)
    {N : ℕ} (hN2 : 2 ≤ N) (hN : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    higherPrimePowers x ≤
      Real.log 4 * ∑ k ∈ Icc 3 N, x ^ (1 / (k : ℝ)) := by
  rw [higherPrimePowers_eq_sum hx hN2 hN, mul_sum]
  exact sum_le_sum fun k _ =>
    Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg hx _)

theorem higherPrimePowers_le_local_sum {x B : ℝ} (hx : 1 ≤ x)
    (hB : x ^ (1 / (3 : ℝ)) ≤ B)
    (htheta : ∀ y : ℝ, 0 ≤ y → y ≤ B → Chebyshev.theta y ≤ y)
    {N : ℕ} (hN2 : 2 ≤ N) (hN : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    higherPrimePowers x ≤ ∑ k ∈ Icc 3 N, x ^ (1 / (k : ℝ)) := by
  rw [higherPrimePowers_eq_sum (by linarith) hN2 hN]
  apply sum_le_sum
  intro k hk
  apply htheta _ (Real.rpow_nonneg (by linarith) _)
  apply le_trans _ hB
  apply Real.rpow_le_rpow_of_exponent_le hx
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (mem_Icc.mp hk).1)

theorem log_cutoff_of_lt_pow_two {x : ℝ} (hx : 0 < x)
    {N : ℕ} (hN : x < (2 : ℝ) ^ (N + 1)) :
    ⌊Real.log x / Real.log 2⌋₊ ≤ N := by
  by_cases hx1 : 1 ≤ x
  · apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (div_nonneg (Real.log_nonneg hx1)
      (Real.log_nonneg (by norm_num)))).mpr
    rw [div_lt_iff₀ (Real.log_pos (by norm_num)), ← Real.log_pow]
    exact Real.log_lt_log hx hN
  have hf : ⌊Real.log x / Real.log 2⌋₊ = 0 :=
    Nat.floor_eq_zero.mpr (by
      have hlx := Real.log_neg hx (lt_of_not_ge hx1)
      have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      exact (div_neg_of_neg_of_pos hlx hl2).trans (by norm_num))
  simp [hf]

theorem theta_lower_of_psi_lower {x L C : ℝ}
    (hpsi : L ≤ Chebyshev.psi x)
    (hcorrection : higherPrimePowers x ≤ C) :
    L - Chebyshev.theta (Real.sqrt x) - C ≤ Chebyshev.theta x := by
  unfold higherPrimePowers at hcorrection
  linarith

theorem theta_lower_of_psi_lower_elementary {x L : ℝ} (hx : 0 ≤ x)
    (hpsi : L ≤ Chebyshev.psi x) {N : ℕ} (hN2 : 2 ≤ N)
    (hN : ⌊Real.log x / Real.log 2⌋₊ ≤ N) :
    L - Real.log 4 * Real.sqrt x -
      Real.log 4 * (∑ k ∈ Icc 3 N, x ^ (1 / (k : ℝ))) ≤
        Chebyshev.theta x := by
  have hc := theta_lower_of_psi_lower hpsi (higherPrimePowers_le_elementary_sum hx hN2 hN)
  have hs := Chebyshev.theta_le_log4_mul_x (Real.sqrt_nonneg x)
  linarith

#print axioms psi_sub_theta_eq_sqrt_add_sum
#print axioms higherPrimePowers_mono
#print axioms higherPrimePowers_le_elementary_sum
#print axioms higherPrimePowers_le_local_sum
#print axioms theta_lower_of_psi_lower_elementary

end LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections
