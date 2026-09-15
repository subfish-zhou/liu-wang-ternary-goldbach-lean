import LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.RealAxis

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaLehmanKernel

def referencePair (a y : ℝ) : ℝ :=
  (1 + a) / ((1 + a) ^ 2 + y ^ 2) + (1 - a) / ((1 - a) ^ 2 + y ^ 2)

theorem lehman_polynomial_nonneg {q v : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (1 / 4))
    (hv : 0 ≤ v) :
    0 ≤ 37 * (1 - q + v) * (1 + v) ^ 2 -
      (35 + 25 * v) * ((1 + q + v) ^ 2 - 4 * q) := by
  have hq' : 0 ≤ 1 - 4 * q := by linarith [hq.2]
  have hquad : 0 ≤ 68 * v ^ 2 - 145 * v + 129 := by
    nlinarith [sq_nonneg (136 * v - 145)]
  have h0 : 0 ≤ 2 * (v + 1) ^ 2 * (6 * v + 1) := by positivity
  have h1 : 0 ≤ (192 * v ^ 3 + 68 * v ^ 2 - 145 * v + 129) / 16 := by
    have hc : 0 ≤ v ^ 3 := pow_nonneg hv _
    linarith
  have he :
      37 * (1 - q + v) * (1 + v) ^ 2 -
          (35 + 25 * v) * ((1 + q + v) ^ 2 - 4 * q) =
        (1 - 4 * q) * (2 * (v + 1) ^ 2 * (6 * v + 1)) +
          4 * q * ((192 * v ^ 3 + 68 * v ^ 2 - 145 * v + 129) / 16) +
          5 / 4 * q * (1 - 4 * q) * (5 * v + 7) := by ring
  rw [he]
  exact add_nonneg (add_nonneg (mul_nonneg hq' h0)
    (mul_nonneg (mul_nonneg (by norm_num) hq.1) h1))
    (by have := hq.1; positivity)

theorem lehman_rational_budget {q v : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (1 / 4))
    (hv : 0 ≤ v) :
    (14 / 5 + 2 * v) / (1 + v) ^ 2 ≤
      37 / 25 * (2 * (1 - q + v) / ((1 + q + v) ^ 2 - 4 * q)) := by
  have hd : 0 < (1 + q + v) ^ 2 - 4 * q := by
    have hs : 0 < (1 - q) ^ 2 := sq_pos_of_pos (by linarith [hq.2])
    nlinarith [mul_nonneg hv hq.1, sq_nonneg v]
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) hd]
  nlinarith [lehman_polynomial_nonneg hq hv]

theorem referencePair_eq {a : ℝ} (ha : |a| ≤ (1 / 2 : ℝ)) (y : ℝ) :
    referencePair a y =
      2 * (1 - a ^ 2 + y ^ 2) / ((1 + a ^ 2 + y ^ 2) ^ 2 - 4 * a ^ 2) := by
  have ha' := abs_le.mp ha
  have hp : 0 < (1 + a) ^ 2 + y ^ 2 := by
    have : 0 < 1 + a := by linarith [ha'.1]
    positivity
  have hm : 0 < (1 - a) ^ 2 + y ^ 2 := by
    have : 0 < 1 - a := by linarith [ha'.2]
    positivity
  have he : (1 + a ^ 2 + y ^ 2) ^ 2 - 4 * a ^ 2 =
      ((1 + a) ^ 2 + y ^ 2) * ((1 - a) ^ 2 + y ^ 2) := by ring
  rw [he]
  unfold referencePair
  field_simp [hp.ne', hm.ne']
  ring

theorem zeroLoss_pair_lehman {a : ℝ} (ha : |a| ≤ (1 / 2 : ℝ)) (y : ℝ) :
    zeroLoss a y + zeroLoss (-a) y ≤ (37 / 25 : ℝ) * referencePair a y := by
  refine (zeroLoss_pair_lift ha y).trans ?_
  rw [referencePair_eq ha]
  apply lehman_rational_budget ⟨sq_nonneg a, ?_⟩ (sq_nonneg y)
  nlinarith [sq_abs a, abs_nonneg a]

#print axioms lehman_polynomial_nonneg
#print axioms zeroLoss_pair_lehman

end LiuWang.Proof.Campaign20260915.ZetaLehmanKernel
