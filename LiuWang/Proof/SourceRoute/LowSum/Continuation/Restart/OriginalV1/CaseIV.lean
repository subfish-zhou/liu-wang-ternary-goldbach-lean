import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.TripleEuler
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.EulerCost
import LiuWang.Proof.MultiZeroRepulsion.Continuation.RepeatedLabel

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1

def lwdSourceA (x : ℝ) : ℝ :=
  (Real.sqrt 3 - 1) / (7 * stechkinConductorCoeff + 2.4998 / Real.log x)

def lwdSourceSigma (x : ℝ) : ℝ := 1 + lwdSourceA x / Real.log x

theorem lwd_source_parameters {x : ℝ} (hx : 8000000000 ≤ x) :
    0 < lwdSourceA x ∧ lwdSourceA x ≤ 0.3784 ∧
      1 < lwdSourceSigma x ∧ lwdSourceSigma x ≤ 1.02 := by
  have hL := source_log_twenty_two hx
  have hL0 : 0 < Real.log x := by linarith
  have hr := Real.sqrt_nonneg 3
  have hr2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hden : 0 < 7 * stechkinConductorCoeff + 2.4998 / Real.log x := by
    have := lwd_kappa_bounds.1
    positivity
  have ha : 0 < lwdSourceA x := div_pos (by nlinarith) hden
  have ha1 : lwdSourceA x ≤ 0.3784 := by
    apply (div_le_iff₀ hden).mpr
    have hn : 0 ≤ (2.4998 : ℝ) / Real.log x := by positivity
    nlinarith [lwd_kappa_bounds.1]
  have hb : 0 < lwdSourceA x / Real.log x := div_pos ha hL0
  have hb1 : lwdSourceA x / Real.log x ≤ 0.02 :=
    (div_le_iff₀ hL0).mpr (by linarith)
  exact ⟨ha, ha1, by dsimp [lwdSourceSigma]; linarith,
    by dsimp [lwdSourceSigma]; linarith⟩

theorem lwd_2_22_on_source_sigma {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 1.02) :
    dampedLogDeriv (1 : DirichletCharacter ℂ 1) sigma (stechkinSigma sigma) stechkinK 0 ≤
      1 / (sigma - 1) - 0.8973 := by
  have ht := stechkinSigma_ge hs
  have he := stechkinSigma_equation sigma
  have ht1 : stechkinSigma sigma ≤ 1.64 := by nlinarith
  have hquot : 0.69875 ≤ stechkinK / (stechkinSigma sigma - 1) :=
    (le_div_iff₀ (by linarith)).mpr (by linarith [lwd_kappa_bounds.2.2])
  have hh := zeta_real_function hs (by linarith : sigma ≤ 23 / 20)
  have hh' : zetaDamped sigma 0 ≤ 1 / (sigma - 1) - 0.8973 := by linarith
  simpa only [dampedLogDeriv, zetaDamped, DirichletCharacter.LFunction_modOne_eq] using hh'

theorem lwd_log_pi : 1.144729 ≤ Real.log Real.pi := by
  apply (Real.le_log_iff_exp_le Real.pi_pos).mpr
  have hs := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.144729)
    (by norm_num : (0.144729 : ℝ) ≤ 1) (by norm_num : 0 < (8 : ℕ))
  calc
    Real.exp 1.144729 = Real.exp 1 * Real.exp 0.144729 := by
      rw [← Real.exp_add]
      norm_num
    _ ≤ (2.7182818286 : ℝ) *
        ((∑ i ∈ Finset.range 8, (0.144729 : ℝ) ^ i / i.factorial) +
          0.144729 ^ 8 * (8 + 1) / ((8 : ℕ).factorial * 8)) :=
      mul_le_mul Real.exp_one_lt_d9.le hs (Real.exp_pos _).le (by norm_num)
    _ ≤ 3.14159265358979323846 := by norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.pi := Real.pi_gt_d20.le

theorem lwd_2_27_constant :
    -0.8973 + 7 * 0.3918 + 4 * 0.4977 +
      stechkinConductorCoeff * (3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi) ≤ 2.4998 := by
  have hlog : 3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi ≤
      3 * 0.693147181 + 1.098612289 - 7 * 1.144729 := by
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, lwd_log_pi]
  have hh := mul_le_mul_of_nonneg_left hlog conductorCoeff_bounds.1
  have hk := mul_le_mul_of_nonpos_right lwd_kappa_bounds.1
    (by norm_num : 3 * (0.693147181 : ℝ) + 1.098612289 - 7 * 1.144729 ≤ 0)
  linarith

theorem lwd_nonprincipal_cost {d : ℕ} [NeZero d] (chi : DirichletCharacter ℂ d)
    (hc : chi ≠ 1) {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma < 1.15) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t ≤
      stechkinConductorCoeff * (Real.log d + Real.log (max 1 |t|) - Real.log Real.pi) +
        0.3918 + 0.4977 := by
  have hh := imprimitive_damped_bound chi hc hs (by linarith : sigma ≤ 23 / 20) t
  have he := lwd_2_9 chi hs
  linarith

theorem lwd_height_log {d q : ℕ} [NeZero d] [NeZero q] {x t : ℝ}
    (hdq : d ∣ q) (hq : (q : ℝ) ≤ x) (ht : |t| ≤ x / q) :
    Real.log d + Real.log (max 1 |t|) ≤ Real.log x := by
  have hd : Real.log d ≤ Real.log q := Real.log_le_log
    (by exact_mod_cast NeZero.pos d) (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) hdq)
  linarith [conductor_height_log_max_le hq ht]

theorem lwd_2_24 {d q : ℕ} [NeZero d] [NeZero q] {x sigma : ℝ}
    (hdq : d ∣ q) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {rho : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    (hz : chi.LFunction rho = 0) (ht : |rho.im| ≤ x / q)
    (hs : 1 < sigma) (hs1 : sigma < 1.15) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK rho.im ≤
      stechkinConductorCoeff * Real.log x - stechkinConductorCoeff * Real.log Real.pi +
        0.3918 - 1 / (sigma - rho.re) := by
  have hh := primitive_multiplicity_bound hc hp hr hr1 hs (by linarith : sigma ≤ 23 / 20)
  have hm : (1 : ℝ) ≤ analyticOrderNatAt chi.LFunction rho := by
    exact_mod_cast ordinary_zero_order_pos chi (by intro h; simp [h] at hr1) hz
  have hi := div_le_div_of_nonneg_right hm (show 0 ≤ sigma - rho.re by linarith)
  have hl := mul_le_mul_of_nonneg_left (lwd_height_log hdq hq ht) conductorCoeff_bounds.1
  nlinarith only [hh, hi, hl]

theorem lwd_2_25 {d q : ℕ} [NeZero d] [NeZero q] {x sigma t u : ℝ}
    (hdq : d ∣ q) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1)
    (ht : |t| ≤ x / q) (hu : |u| ≤ x / q)
    (hs : 1 < sigma) (hs1 : sigma < 1.15) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK (t + u) ≤
      stechkinConductorCoeff * (Real.log x + Real.log 2) -
        stechkinConductorCoeff * Real.log Real.pi + 0.3918 + 0.4977 := by
  have hh := lwd_nonprincipal_cost chi hc hs hs1 (t + u)
  have hd : Real.log d ≤ Real.log q := Real.log_le_log
    (by exact_mod_cast NeZero.pos d) (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) hdq)
  have hl : Real.log d + Real.log (max 1 |t + u|) ≤ Real.log x + Real.log 2 := by
    linarith [(paired_height_logs hq ht hu).1]
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  nlinarith only [hh, hm]

theorem lwd_2_26 {d q : ℕ} [NeZero d] [NeZero q] {x sigma t u v : ℝ}
    (hdq : d ∣ q) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1)
    (ht : |t| ≤ x / q) (hu : |u| ≤ x / q) (hv : |v| ≤ x / q)
    (hs : 1 < sigma) (hs1 : sigma < 1.15) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK (t + u + v) ≤
      stechkinConductorCoeff * (Real.log x + Real.log 3) -
        stechkinConductorCoeff * Real.log Real.pi + 0.3918 + 0.4977 := by
  have hx : 0 < x := (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q).trans_le hq
  have htuv : |t + u + v| ≤ (3 * x) / q := by
    rw [mul_div_assoc]
    linarith [abs_add_le t u, abs_add_le (t + u) v]
  have hl := lwd_height_log hdq (show (q : ℝ) ≤ 3 * x by linarith) htuv
  rw [Real.log_mul (by norm_num) hx.ne'] at hl
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  have hh := lwd_nonprincipal_cost chi hc hs hs1 (t + u + v)
  nlinarith only [hh, hm]

theorem lwd_2_27_case_iv {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x : ℝ} (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hdq : d ∣ q) (heq : e ∣ q) (hfq : f ∣ q)
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f)
    (hc : chi ≠ 1) (hp : psi ≠ 1) (he : eta ≠ 1)
    (hpc : chi.IsPrimitive) (hpp : psi.IsPrimitive) (hpe : eta.IsPrimitive)
    (hcp : lwdProduct chi psi ≠ 1) (hce : lwdProduct chi eta ≠ 1)
    (hpe' : lwdProduct psi eta ≠ 1) (hcpe : lwdProduct (lwdProduct chi psi) eta ≠ 1)
    {rho tau upsilon : ℂ}
    (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1) (hzr : chi.LFunction rho = 0)
    (ht : 1 / 2 < tau.re) (ht1 : tau.re < 1) (hzt : psi.LFunction tau = 0)
    (hu : 1 / 2 < upsilon.re) (hu1 : upsilon.re < 1) (hzu : eta.LFunction upsilon = 0)
    (hyr : |rho.im| ≤ x / q) (hyt : |tau.im| ≤ x / q) (hyu : |upsilon.im| ≤ x / q) :
    lwdG chi psi eta (lwdSourceSigma x) rho.im tau.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - rho.re) + 1 / (lwdSourceSigma x - tau.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 2.4998 := by
  have hs := (lwd_source_parameters hx).2.2
  have hs1 : lwdSourceSigma x < 1.15 := by linarith [hs.2]
  have h0 := lwd_2_22_on_source_sigma hs.1 hs.2
  have h1 := lwd_2_24 hdq hq chi hc hpc hr hr1 hzr hyr hs.1 hs1
  have h2 := lwd_2_24 heq hq psi hp hpp ht ht1 hzt hyt hs.1 hs1
  have h3 := lwd_2_24 hfq hq eta he hpe hu hu1 hzu hyu hs.1 hs1
  have h4 := lwd_2_25 (Nat.lcm_dvd hdq heq) hq (lwdProduct chi psi) hcp hyr hyt hs.1 hs1
  have h5 := lwd_2_25 (Nat.lcm_dvd hdq hfq) hq (lwdProduct chi eta) hce hyr hyu hs.1 hs1
  have h6 := lwd_2_25 (Nat.lcm_dvd heq hfq) hq (lwdProduct psi eta) hpe' hyt hyu hs.1 hs1
  have h7 := lwd_2_26 (Nat.lcm_dvd (Nat.lcm_dvd hdq heq) hfq) hq
    (lwdProduct (lwdProduct chi psi) eta) hcpe hyr hyt hyu hs.1 hs1
  dsimp only [lwdG]
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, lwd_2_27_constant]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1
