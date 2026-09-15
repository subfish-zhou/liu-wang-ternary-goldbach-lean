import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.RegularCubic

set_option autoImplicit false
noncomputable section
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularIntegral LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

def exceptionalScale (N : ℕ) (beta : ℝ) : ℝ := exceptionalRoot*baseWeight N beta
def regularScale (N q : ℕ) (rho : ℂ) : ℝ := radiusRoot N q*regularWeight N q rho

theorem scales_pos {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    (beta : ℝ) {rho : ℂ} (hr : 0 < rho.re) :
    0 < exceptionalScale N beta ∧ 0 < regularScale N q rho :=
  ⟨mul_pos (roots_pos hN hq).2.1 (baseWeight_pos (nat_pos_of_exp_le hN) _),
    mul_pos (roots_pos hN hq).2.2 (regularWeight_pos hN hq hr)⟩

theorem mixed_absolute_one_each {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {beta : ℝ} (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) {rho : ℂ} (hr : 0 < rho.re) :
    (∫ eta in -deltaRadius N q..deltaRadius N q, ‖tripleKernel N 1 beta rho eta‖) ≤
      (N : ℝ)^2*principalRoot*exceptionalScale N beta*regularScale N q rho :=
  absolute_finite_holder (nat_pos_of_exp_le hN) 1 beta rho (deltaRadius_pos hN hq).le
    (roots_pos hN hq).1 (scales_pos hN hq beta hr).1 (scales_pos hN hq beta hr).2
    (principal_cubic_bound (nat_pos_of_exp_le hN) (deltaRadius_pos hN hq).le)
    (exceptional_cubic_bound (nat_pos_of_exp_le hN) hb hb1 (deltaRadius_pos hN hq).le)
    (regular_cubic_bound hN hq hr)

theorem mixed_absolute_two_exceptional {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {beta : ℝ} (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) {rho : ℂ} (hr : 0 < rho.re) :
    (∫ eta in -deltaRadius N q..deltaRadius N q, ‖tripleKernel N beta beta rho eta‖) ≤
      (N : ℝ)^2*(exceptionalScale N beta)^2*regularScale N q rho := by
  have h := absolute_finite_holder (nat_pos_of_exp_le hN) beta beta rho
    (deltaRadius_pos hN hq).le
    (scales_pos hN hq beta hr).1 (scales_pos hN hq beta hr).1 (scales_pos hN hq beta hr).2
    (exceptional_cubic_bound (nat_pos_of_exp_le hN) hb hb1 (deltaRadius_pos hN hq).le)
    (exceptional_cubic_bound (nat_pos_of_exp_le hN) hb hb1 (deltaRadius_pos hN hq).le)
    (regular_cubic_bound hN hq hr)
  simpa only [pow_two, mul_assoc] using h

theorem mixed_absolute_one_exceptional {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {beta : ℝ} (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1)
    {rho sigma : ℂ} (hr : 0 < rho.re) (hs : 0 < sigma.re) :
    (∫ eta in -deltaRadius N q..deltaRadius N q, ‖tripleKernel N beta rho sigma eta‖) ≤
      (N : ℝ)^2*exceptionalScale N beta*regularScale N q rho*regularScale N q sigma :=
  absolute_finite_holder (nat_pos_of_exp_le hN) beta rho sigma (deltaRadius_pos hN hq).le
    (scales_pos hN hq beta hr).1 (scales_pos hN hq beta hr).2 (scales_pos hN hq beta hs).2
    (exceptional_cubic_bound (nat_pos_of_exp_le hN) hb hb1 (deltaRadius_pos hN hq).le)
    (regular_cubic_bound hN hq hr) (regular_cubic_bound hN hq hs)

theorem mixed_finite_one_each {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {beta : ℝ} (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) {rho : ℂ} (hr : 0 < rho.re) :
    ‖finiteMoment N (deltaRadius N q) 1 beta rho‖ ≤
      (N : ℝ)^2*principalRoot*exceptionalScale N beta*regularScale N q rho :=
  (intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := tripleKernel N 1 beta rho) (by linarith [deltaRadius_pos hN hq])).trans
    (mixed_absolute_one_each hN hq hb hb1 hr)

theorem mixed_finite_two_exceptional {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {beta : ℝ} (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1) {rho : ℂ} (hr : 0 < rho.re) :
    ‖finiteMoment N (deltaRadius N q) beta beta rho‖ ≤
      (N : ℝ)^2*(exceptionalScale N beta)^2*regularScale N q rho :=
  (intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := tripleKernel N beta beta rho) (by linarith [deltaRadius_pos hN hq])).trans
    (mixed_absolute_two_exceptional hN hq hb hb1 hr)

theorem mixed_finite_one_exceptional {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    {beta : ℝ} (hb : 0.9957 ≤ beta) (hb1 : beta ≤ 1)
    {rho sigma : ℂ} (hr : 0 < rho.re) (hs : 0 < sigma.re) :
    ‖finiteMoment N (deltaRadius N q) beta rho sigma‖ ≤
      (N : ℝ)^2*exceptionalScale N beta*regularScale N q rho*regularScale N q sigma :=
  (intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := tripleKernel N beta rho sigma) (by linarith [deltaRadius_pos hN hq])).trans
    (mixed_absolute_one_exceptional hN hq hb hb1 hr hs)

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
