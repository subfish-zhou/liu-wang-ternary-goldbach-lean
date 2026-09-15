import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Holder

set_option autoImplicit false
noncomputable section
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularIntegral
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.MajorZeroMomentPayment.Continuation

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

def lowWeight (N : ℕ) (rho : ℂ) : ℝ :=
  ((1-(0.001 : ℝ)^rho.re)/rho.re)*baseWeight N rho.re

def highWeight (N : ℕ) (rho : ℂ) : ℝ := baseWeight N rho.re/|rho.im|

def regularWeight (N q : ℕ) (rho : ℂ) : ℝ :=
  if |rho.im| ≤ omegaCutoff N q then lowWeight N rho else 5*highWeight N rho

def radiusRoot (N q : ℕ) : ℝ := cubeRoot (2*deltaRadius N q*(N : ℝ))

def principalRoot : ℝ := cubeRoot (2.994006/Real.pi)

def exceptionalRoot : ℝ := cubeRoot (3*1.0302*1.0033^2/Real.pi)

theorem baseWeight_pos {N : ℕ} (hN : 0 < N) (beta : ℝ) : 0 < baseWeight N beta :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _

theorem lowWeight_pos {N : ℕ} (hN : 0 < N) {rho : ℂ} (hr : 0 < rho.re) :
    0 < lowWeight N rho := by
  have h : (0.001 : ℝ)^rho.re < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hr
  exact mul_pos (div_pos (sub_pos.mpr h) hr) (baseWeight_pos hN _)

theorem regularWeight_pos {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {rho : ℂ} (hr : 0 < rho.re) : 0 < regularWeight N q rho := by
  unfold regularWeight
  split_ifs with hg
  · exact lowWeight_pos (nat_pos_of_exp_le hN) hr
  · have hi : 0 < |rho.im| := (omegaCutoff_pos hN hq).trans (lt_of_not_ge hg)
    exact mul_pos (by norm_num) (div_pos (baseWeight_pos (nat_pos_of_exp_le hN) _) hi)

theorem roots_pos {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q) :
    0 < principalRoot ∧ 0 < exceptionalRoot ∧ 0 < radiusRoot N q := by
  have hn := natCast_pos_of_exp_le hN
  have hd := deltaRadius_pos hN hq
  exact ⟨cubeRoot_pos (by positivity), cubeRoot_pos (by positivity),
    cubeRoot_pos (by positivity)⟩

theorem regular_Jrho_bound {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {rho : ℂ} (hr : 0 < rho.re) {eta : ℝ} (he : |eta| ≤ deltaRadius N q) :
    ‖Jrho N rho eta‖ ≤ (N : ℝ)*regularWeight N q rho := by
  have hn := natCast_pos_of_exp_le hN
  have hp : (N : ℝ)^rho.re = (N : ℝ)*baseWeight N rho.re := by
    rw [baseWeight, Real.rpow_sub_one hn.ne']
    field_simp
  unfold regularWeight
  split_ifs with hg
  · apply (OscillatoryBounds.Jrho_weight (nat_pos_of_exp_le hN) hr eta).trans_eq
    rw [hp]
    unfold lowWeight
    ring
  · have hi : 0 < |rho.im| := (omegaCutoff_pos hN hq).trans (lt_of_not_ge hg)
    have he' : |eta| ≤ |rho.im|/(10*Real.pi*(N : ℝ)) := by
      rw [deltaRadius_eq_omega] at he
      exact he.trans (div_le_div_of_nonneg_right (lt_of_not_ge hg).le (by positivity))
    apply (OscillatoryBounds.Jrho_near (nat_pos_of_exp_le hN) hr.le
      (abs_pos.mp hi) he').trans_eq
    rw [hp]
    unfold highWeight
    ring

theorem regular_cubic_bound {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {rho : ℂ} (hr : 0 < rho.re) :
    (∫ eta in -deltaRadius N q..deltaRadius N q, ‖Jrho N rho eta‖^3) ≤
      (N : ℝ)^2*(radiusRoot N q*regularWeight N q rho)^3 := by
  have hn := natCast_pos_of_exp_le hN
  have hd := deltaRadius_pos hN hq
  have hm := intervalIntegral.integral_mono_on (by linarith : -deltaRadius N q ≤ deltaRadius N q)
    (((Jrho_continuous (nat_pos_of_exp_le hN) rho).norm.pow 3).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume))
    (fun eta he => pow_le_pow_left₀ (norm_nonneg _) (regular_Jrho_bound hN hq hr
      (abs_le.mpr he)) 3)
  apply hm.trans_eq
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_neg_eq_add]
  simp only [mul_pow, radiusRoot]
  rw [cubeRoot_cube (by positivity)]
  ring

theorem principal_cubic_bound {N : ℕ} (hN : 0 < N) {delta : ℝ} (hd : 0 ≤ delta) :
    (∫ eta in -delta..delta, ‖Jrho N 1 eta‖^3) ≤ (N : ℝ)^2*principalRoot^3 := by
  rw [principalRoot, cubeRoot_cube (by positivity)]
  simpa only [Jrho_one_eq_J, mul_comm] using J_cubic_source hN hd

theorem exceptional_cubic_bound {N : ℕ} (hN : 0 < N) {beta delta : ℝ}
    (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) (hd : 0 ≤ delta) :
    (∫ eta in -delta..delta, ‖Jrho N (beta : ℂ) eta‖^3) ≤
      (N : ℝ)^2*(exceptionalRoot*baseWeight N beta)^3 := by
  rw [mul_pow, exceptionalRoot, cubeRoot_cube (by positivity)]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using Jrho_cubic_source_scaled hN hb hb1 hd

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
