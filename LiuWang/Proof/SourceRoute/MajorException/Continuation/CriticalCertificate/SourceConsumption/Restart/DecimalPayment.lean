import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.PowerNormalization
import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.PowerBounds

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroMomentPayment

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

def mixedBudget : MixedKind → ℝ
  | .oneEach => 0.00000003
  | .oneExceptionalTwoRegular => 0.00000002
  | .twoExceptionalOneRegular => 0.00008452

def originalMixedBudget : MixedKind → ℝ
  | .oneEach => 0.00000004
  | .oneExceptionalTwoRegular => 0.00318
  | .twoExceptionalOneRegular => 0.0001

theorem mixedBudget_original (j : MixedKind) : mixedBudget j ≤ originalMixedBudget j := by
  cases j <;> norm_num [mixedBudget, originalMixedBudget]

theorem first_paid {N r : ℕ} {beta : ℝ}
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hd : paperDomain r (sourceL N))
    (hphi : (r:ℝ)/(r.totient:ℝ) ≤ nu r)
    (hgap : Real.pi/(0.4923*Real.sqrt r*(Real.log r)^2) ≤ 1-beta) :
    baseWeight N beta*(Real.sqrt r*firstMomentBudget N r) ≤ 0.00000003/3.6 := by
  have hr : 0 < r := by exact_mod_cast (show (0:ℝ)<r by linarith [hd.1])
  have hc := conductorMass_linear hN hd hphi hgap
  have hc0 : 0 ≤ conductorMass r*baseWeight N beta :=
    mul_nonneg (conductorMass_nonneg r) (by unfold baseWeight; positivity)
  have hpow := conductor_negative_powers hd.1
  have hlog := logarithmic_negative_powers hd.2.1
  have hl : 0 < sourceL N := by linarith [hd.2.1]
  calc
    _ = (48.4*8.2e-10)*(conductorMass r*baseWeight N beta)*(r:ℝ)^(-5/6:ℝ) +
        8.316*(conductorMass r*baseWeight N beta)*sourceL N^(-5/2:ℝ) := by
      rw [firstMoment_normalized (exp_2000_le_of_exp_3100_le hN) hr]
      ring
    _ ≤ (48.4*8.2e-10)*0.4*(1/30:ℝ)+8.316*0.4*(1/(3100^2*55:ℝ)) := by
      gcongr
      · exact hpow.1
      · exact hlog.1
    _ ≤ _ := by norm_num

theorem second_paid {N r : ℕ} {beta : ℝ}
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hd : paperDomain r (sourceL N))
    (hphi : (r:ℝ)/(r.totient:ℝ) ≤ nu r)
    (hgap : Real.pi/(0.4923*Real.sqrt r*(Real.log r)^2) ≤ 1-beta) :
    baseWeight N beta*(Real.sqrt r*secondMomentBudget N r) ≤ 0.00000002/1.08 := by
  have hr : 0 < r := by exact_mod_cast (show (0:ℝ)<r by linarith [hd.1])
  have hc := conductorMass_linear hN hd hphi hgap
  have hc0 : 0 ≤ conductorMass r*baseWeight N beta :=
    mul_nonneg (conductorMass_nonneg r) (by unfold baseWeight; positivity)
  have hpow := conductor_negative_powers hd.1
  have hlog := logarithmic_negative_powers hd.2.1
  have hl : 0 < sourceL N := by linarith [hd.2.1]
  calc
    _ = (55*(8.2e-10:ℝ)^2)*(conductorMass r*baseWeight N beta)*(r:ℝ)^(-2/3:ℝ) +
        (132*8.2e-10*0.063+22*0.063^2)*(conductorMass r*baseWeight N beta)*sourceL N^(-2:ℝ) := by
      rw [secondMoment_normalized (exp_2000_le_of_exp_3100_le hN) hr]
      ring
    _ ≤ (55*(8.2e-10:ℝ)^2)*0.4*1+
        (132*8.2e-10*0.063+22*0.063^2)*0.4*(1/(3100^2:ℝ)) := by
      gcongr
      · exact hpow.2.1
      · exact hlog.2.1
    _ ≤ _ := by norm_num

theorem twoExceptional_paid {N r : ℕ} {beta : ℝ}
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hd : paperDomain r (sourceL N)) (hbeta : beta ≤ 1) :
    baseWeight N beta^2*((r:ℝ)*firstMomentBudget N r) ≤ 0.00008452/1.8 := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hr : 0 < r := by exact_mod_cast (show (0:ℝ)<r by linarith [hd.1])
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN'
  have hb : baseWeight N beta ≤ 1 := by
    simpa only [baseWeight, Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hN1 (show beta-1 ≤ 0 by linarith)
  have hb0 : 0 ≤ baseWeight N beta := by unfold baseWeight; positivity
  have hb2 : baseWeight N beta^2 ≤ 1 := by nlinarith [sq_nonneg (baseWeight N beta)]
  have hf : 0 ≤ (r:ℝ)*firstMomentBudget N r := by
    have hl := sourceL_pos hN'
    have hp := sourceP_pos hN'
    unfold firstMomentBudget
    positivity
  have hc := conductorMass_le hd.1
  have hc0 := conductorMass_nonneg r
  have hpow := (conductor_negative_powers hd.1).2.2
  have hratio := conductor_ratio_high hr hd.2.1 hd.2.2
  calc
    _ ≤ (r:ℝ)*firstMomentBudget N r :=
      (mul_le_mul_of_nonneg_right hb2 hf).trans_eq (one_mul _)
    _ = (48.4*8.2e-10)*conductorMass r*(r:ℝ)^(-1/3:ℝ) +
        8.316*(((r:ℝ)/(r.totient:ℝ))^2*sourceL N^(-5/2:ℝ)) := by
      rw [twoExceptionalMoment_normalized hN' hr]
      ring
    _ ≤ (48.4*8.2e-10)*1.4*(1/9:ℝ)+8.316*(7/(3100*400:ℝ)) := by gcongr
    _ ≤ _ := by norm_num

theorem analyticCost_numeric {N r : ℕ} {beta : ℝ}
    (hN : Real.exp 3100 ≤ (N:ℝ)) (hd : paperDomain r (sourceL N))
    (hphi : (r:ℝ)/(r.totient:ℝ) ≤ nu r)
    (hgap : Real.pi/(0.4923*Real.sqrt r*(Real.log r)^2) ≤ 1-beta)
    (hbeta : beta ≤ 1) (j : MixedKind) :
    analyticCost N r beta j ≤ mixedBudget j*(N:ℝ)^2 := by
  cases j with
  | oneEach =>
    calc
      _ = 3.6*(baseWeight N beta*(Real.sqrt r*firstMomentBudget N r))*(N:ℝ)^2 := by
        unfold analyticCost
        ring
      _ ≤ 3.6*(0.00000003/3.6)*(N:ℝ)^2 := by
        gcongr
        exact first_paid hN hd hphi hgap
      _ = _ := by unfold mixedBudget; ring
  | oneExceptionalTwoRegular =>
    calc
      _ = 1.08*(baseWeight N beta*(Real.sqrt r*secondMomentBudget N r))*(N:ℝ)^2 := by
        unfold analyticCost
        ring
      _ ≤ 1.08*(0.00000002/1.08)*(N:ℝ)^2 := by
        gcongr
        exact second_paid hN hd hphi hgap
      _ = _ := by unfold mixedBudget; ring
  | twoExceptionalOneRegular =>
    calc
      _ = 1.8*(baseWeight N beta^2*((r:ℝ)*firstMomentBudget N r))*(N:ℝ)^2 := by
        unfold analyticCost
        ring
      _ ≤ 1.8*(0.00008452/1.8)*(N:ℝ)^2 := by
        gcongr
        exact twoExceptional_paid hN hd hbeta
      _ = _ := by unfold mixedBudget; ring

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
