import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.PurePayment
import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.Budget.TotientPower

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

def conductorMass (r : ℕ) : ℝ := (r:ℝ)*Real.sqrt r/(r.totient:ℝ)^2

theorem conductorMass_nonneg (r : ℕ) : 0 ≤ conductorMass r := by
  unfold conductorMass
  positivity

theorem conductorMass_le {r : ℕ} (hr : 987 ≤ (r:ℝ)) : conductorMass r ≤ 1.4 := by
  have hr0 : 0 < r := by exact_mod_cast (show (0:ℝ)<r by linarith)
  have hp : 0 < (r.totient:ℝ)^2 := by
    exact sq_pos_of_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hr0))
  have h := MajorZeroMomentPayment.Continuation.Frontier.Budget.totient_large_sqrt_ratio
    (r := r) (a := 5) (by norm_num) (by nlinarith)
  unfold conductorMass
  apply (div_le_iff₀ hp).mpr
  linarith

theorem conductorMass_cubic {N r : ℕ} {beta : ℝ}
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hd : paperDomain r (sourceL N))
    (hphi : (r:ℝ)/(r.totient:ℝ) ≤ nu r)
    (hgap : Real.pi/(0.4923*Real.sqrt r*(Real.log r)^2) ≤ 1-beta) :
    conductorMass r * baseWeight N beta^3 ≤ 0.028 := by
  have hr : 0 < (r:ℝ) := by linarith [hd.1]
  have hp : 0 ≤ (r:ℝ)/(r.totient:ℝ) := by positivity
  have h1 := pow_le_pow_left₀ hp hphi 2
  have h2 := beta_gap_power hN hgap .cubic
  have h := mul_le_mul (mul_le_mul_of_nonneg_left h1
    (Real.rpow_nonneg hr.le (-decayPower .cubic))) h2
    (by unfold baseWeight; positivity) (by positivity)
  have hi := conductor_ratio_identity .cubic hr (r.totient:ℝ)
  change conductorMass r = (r:ℝ)^(-decayPower .cubic)*((r:ℝ)/(r.totient:ℝ))^2 at hi
  rw [← hi] at h
  change conductorMass r*baseWeight N beta^3 ≤ conductorScalar .cubic r (sourceL N) at h
  exact (h.trans (paper_scalar_stronger .cubic hd)).trans (by norm_num [certifiedValue])

theorem conductorMass_linear {N r : ℕ} {beta : ℝ}
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hd : paperDomain r (sourceL N))
    (hphi : (r:ℝ)/(r.totient:ℝ) ≤ nu r)
    (hgap : Real.pi/(0.4923*Real.sqrt r*(Real.log r)^2) ≤ 1-beta) :
    conductorMass r * baseWeight N beta ≤ 0.4 := by
  have hc := conductorMass_le hd.1
  have hc0 := conductorMass_nonneg r
  have hb : 0 ≤ baseWeight N beta := by unfold baseWeight; positivity
  have hh := conductorMass_cubic hN hd hphi hgap
  have hsq := pow_le_pow_left₀ hc0 hc 2
  have hm := mul_le_mul hsq hh (mul_nonneg hc0 (pow_nonneg hb 3)) (by norm_num)
  have he : (conductorMass r*baseWeight N beta)^3 =
      conductorMass r^2*(conductorMass r*baseWeight N beta^3) := by ring
  apply (pow_le_pow_iff_left₀ (mul_nonneg hc0 hb)
    (by norm_num : (0:ℝ)≤0.4) (by norm_num : 3≠0)).mp
  rw [he]
  exact hm.trans (by norm_num)

theorem totient_ratio_quarter {r : ℕ} (hr : 0 < r) :
    ((r:ℝ)/(r.totient:ℝ))^2 ≤ 7*(r:ℝ)^(1/4:ℝ) := by
  have hp : 0 < (r.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have h : (r:ℝ)^7 ≤ 2401*(r.totient:ℝ)^8 := by
    exact_mod_cast MajorZeroMomentPayment.Continuation.Frontier.Budget.totient_seven_eighth r
  apply (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity)
    (by norm_num : 4≠0)).mp
  rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg r)]
  norm_num only [show (1/4:ℝ)*(4:ℕ)=1 by norm_num, Real.rpow_one]
  rw [← pow_mul, div_pow, div_le_iff₀ (pow_pos hp 8)]
  norm_num only [show (2:ℕ)*4=8 by norm_num]
  nlinarith [mul_le_mul_of_nonneg_right h (Nat.cast_nonneg r : (0:ℝ) ≤ r)]

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
