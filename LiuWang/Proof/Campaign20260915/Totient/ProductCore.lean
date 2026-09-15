import LiuWang.Proof.Campaign20260915.Totient.ProductData

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.Totient

noncomputable section

def productEnvelope (x : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * (Real.log x + 1 / (2 * Real.log x))

theorem productEnvelope_monotone : MonotoneOn productEnvelope (Set.Ici 3) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by linarith [show 3 ≤ x from hx]
  have hlogx : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le hx0).mpr
    exact Real.exp_one_lt_three.le.trans hx
  have hlogy := Real.log_le_log hx0 hxy
  have hlogx0 : 0 < Real.log x := by linarith
  have hlogy0 : 0 < Real.log y := hlogx0.trans_le hlogy
  have hp : 0 < 2 * Real.log x * Real.log y := by positivity
  unfold productEnvelope
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply (mul_le_mul_iff_right₀ hp).mp
  field_simp [hlogx0.ne', hlogy0.ne']
  have hprod : 1 ≤ Real.log x * Real.log y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlogx)
      (sub_nonneg.mpr (hlogx.trans hlogy))]
  nlinarith [mul_nonneg (sub_nonneg.mpr hlogy)
    (show 0 ≤ 2 * Real.log x * Real.log y - 1 by linarith)]

theorem prefixEuler_step (n : ℕ) :
    prefixEuler (n + 1) =
      if (n + 1).Prime then prefixEuler n * ((n + 1 : ℕ) : ℚ) / n else prefixEuler n := by
  unfold prefixEuler
  rw [Nat.primesLE_succ]
  split_ifs with hp
  · rw [Finset.prod_insert (by simp [Nat.mem_primesLE])]
    push_cast
    ring
  · rfl

theorem prefixEuler_le_units (n : ℕ) :
    (prefixEuler n : ℝ) ≤ (eulerUnits n : ℝ) / 10000000000 := by
  induction n with
  | zero => simp [prefixEuler, eulerUnits]
  | succ n ih =>
    rw [prefixEuler_step, eulerUnits]
    by_cases hp : (n + 1).Prime
    · simp only [if_pos hp, eulerStep]
      have hn : 0 < n := by have := hp.two_le; omega
      have ht : eulerUnits n * (n + 1) <
          (eulerUnits n * (n + 1) / n + 1) * n := by
        exact (Nat.div_lt_iff_lt_mul hn).mp (Nat.lt_succ_self _)
      have htr : (eulerUnits n : ℝ) * (n + 1) <
          ((eulerUnits n * (n + 1) / n + 1 : ℕ) : ℝ) * n := by exact_mod_cast ht
      push_cast
      have hm := mul_le_mul_of_nonneg_right ih
        (show 0 ≤ (n + 1 : ℝ) / n by positivity)
      rw [← mul_div_assoc] at hm
      apply hm.trans
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have h := div_le_div_of_nonneg_right ((div_lt_iff₀ hnR).mpr htr).le
        (by norm_num : (0 : ℝ) ≤ 10000000000)
      push_cast at h
      convert h using 1
      ring
    · simpa only [if_neg hp, eulerStep] using ih


end
end LiuWang.Proof.Campaign20260915.Totient
