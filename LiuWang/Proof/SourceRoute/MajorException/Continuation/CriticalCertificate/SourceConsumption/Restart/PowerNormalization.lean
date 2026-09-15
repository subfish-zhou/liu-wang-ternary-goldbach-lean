import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.AnalyticCost
import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.ConductorPayment

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

theorem source_power_quotient {N : ℕ} (hN : Real.exp 2000 ≤ (N:ℝ))
    (s : ℝ) (k : ℕ) :
    sourceP N^s/sourceL N^k = sourceL N^(3*s-k) := by
  rw [Real.rpow_sub (sourceL_pos hN), Real.rpow_natCast]
  change (sourceL N^3)^s/sourceL N^k = sourceL N^((3:ℕ)*s)/sourceL N^k
  rw [Real.rpow_natCast_mul (sourceL_pos hN).le]

theorem mass_power {r : ℕ} (hr : 0 < r) (s : ℝ) :
    Real.sqrt r*(r:ℝ)^s/(r.totient:ℝ)^2 = conductorMass r*(r:ℝ)^(s-1) := by
  have hr0 : (r:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  rw [Real.rpow_sub_one hr0]
  unfold conductorMass
  field_simp

theorem firstMoment_normalized {N r : ℕ}
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hr : 0 < r) :
    Real.sqrt r*firstMomentBudget N r =
      (48.4*8.2e-10)*conductorMass r*(r:ℝ)^(-5/6:ℝ) +
        8.316*conductorMass r*sourceL N^(-5/2:ℝ) := by
  have hm := mass_power hr (1/6)
  norm_num only [show (1/6:ℝ)-1 = -5/6 by norm_num] at hm
  have hP := source_power_quotient hN (1/6) 3
  norm_num only [show (3:ℝ)*(1/6)-(3:ℕ) = -5/2 by norm_num] at hP
  calc
    _ = (48.4*8.2e-10)*(Real.sqrt r*(r:ℝ)^(1/6:ℝ)/(r.totient:ℝ)^2) +
        8.316*conductorMass r*(sourceP N^(1/6:ℝ)/sourceL N^3) := by
      unfold firstMomentBudget conductorMass
      ring
    _ = _ := by rw [hm, hP]; ring

theorem secondMoment_normalized {N r : ℕ}
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hr : 0 < r) :
    Real.sqrt r*secondMomentBudget N r =
      (55*(8.2e-10:ℝ)^2)*conductorMass r*(r:ℝ)^(-2/3:ℝ) +
        (132*8.2e-10*0.063+22*0.063^2)*conductorMass r*sourceL N^(-2:ℝ) := by
  have hm := mass_power hr (1/3)
  norm_num only [show (1/3:ℝ)-1 = -2/3 by norm_num] at hm
  have hP := source_power_quotient hN (1/3) 3
  have hQ := source_power_quotient hN (4/3) 6
  norm_num only [show (3:ℝ)*(1/3)-(3:ℕ) = -2 by norm_num] at hP
  norm_num only [show (3:ℝ)*(4/3)-(6:ℕ) = -2 by norm_num] at hQ
  calc
    _ = (55*(8.2e-10:ℝ)^2)*(Real.sqrt r*(r:ℝ)^(1/3:ℝ)/(r.totient:ℝ)^2) +
        (132*8.2e-10*0.063)*conductorMass r*(sourceP N^(1/3:ℝ)/sourceL N^3) +
        (22*0.063^2)*conductorMass r*(sourceP N^(4/3:ℝ)/sourceL N^6) := by
      unfold secondMomentBudget conductorMass
      ring
    _ = _ := by rw [hm, hP, hQ]; ring

theorem twoExceptionalMoment_normalized {N r : ℕ}
    (hN : Real.exp 2000 ≤ (N:ℝ)) (hr : 0 < r) :
    (r:ℝ)*firstMomentBudget N r =
      (48.4*8.2e-10)*conductorMass r*(r:ℝ)^(-1/3:ℝ) +
        8.316*((r:ℝ)/(r.totient:ℝ))^2*sourceL N^(-5/2:ℝ) := by
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast hr
  have he : Real.sqrt r*(r:ℝ)^(-1/3:ℝ) = (r:ℝ)^(1/6:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hr0]
    norm_num
  have hm : (r:ℝ)*(r:ℝ)^(1/6:ℝ)/(r.totient:ℝ)^2 =
      conductorMass r*(r:ℝ)^(-1/3:ℝ) := by
    rw [← he]
    unfold conductorMass
    ring
  have hP := source_power_quotient hN (1/6) 3
  norm_num only [show (3:ℝ)*(1/6)-(3:ℕ) = -5/2 by norm_num] at hP
  calc
    _ = (48.4*8.2e-10)*((r:ℝ)*(r:ℝ)^(1/6:ℝ)/(r.totient:ℝ)^2) +
        8.316*((r:ℝ)/(r.totient:ℝ))^2*(sourceP N^(1/6:ℝ)/sourceL N^3) := by
      unfold firstMomentBudget
      ring
    _ = _ := by rw [hm, hP]; ring

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
