import LiuWang.Proof.Campaign20260915.ZetaMordell.ContourShift
import LiuWang.Proof.Campaign20260915.ZetaMordell.CorrectionIntegral

set_option autoImplicit false
noncomputable section

open Complex
open scoped Real ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

theorem mordellGaussian_phase :
    (1 / 2 : ℂ) ^ (1 / 2 : ℂ) * (1 + I) = exp (Real.pi * I / 4) := by
  have hc := mordellIntegral_contour_shift (1 / 2)
  have hd := mordellIntegral_difference (-1 / 2)
  have hneg : exp (-2 * (Real.pi : ℂ) * I * (1 / 2)) = -1 := by
    rw [show -2 * (Real.pi : ℂ) * I * (1 / 2) = -(Real.pi * I) by ring,
      exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [hneg] at hc
  norm_num only [show (1 / 2 : ℂ) - 1 = -1 / 2 by ring,
    show (-1 / 2 : ℂ) + 1 = 1 / 2 by ring] at hc hd
  have he : ((1 / 2 : ℂ) ^ (1 / 2 : ℂ) * exp (-Real.pi * I / 4)) * (1 + I) = 1 := by
    rw [show -Real.pi * I / 4 = -Real.pi * I * (1 / 4 : ℂ) by ring]
    linear_combination hc - hd
  have hx : exp (-Real.pi * I / 4) * exp (Real.pi * I / 4) = 1 := by
    rw [← exp_add, show -Real.pi * I / 4 + Real.pi * I / 4 = 0 by ring, exp_zero]
  calc
    _ = (((1 / 2 : ℂ) ^ (1 / 2 : ℂ) * exp (-Real.pi * I / 4)) * (1 + I)) *
        exp (Real.pi * I / 4) := by
      rw [show (((1 / 2 : ℂ) ^ (1 / 2 : ℂ) * exp (-Real.pi * I / 4)) * (1 + I)) *
          exp (Real.pi * I / 4) =
          ((1 / 2 : ℂ) ^ (1 / 2 : ℂ) * (1 + I)) *
            (exp (-Real.pi * I / 4) * exp (Real.pi * I / 4)) by ring, hx, mul_one]
    _ = _ := by rw [he, one_mul]

theorem mordellIntegral_difference_exp (a : ℂ) :
    mordellIntegral (a + 1) - mordellIntegral a =
      exp (Real.pi * I / 4 - Real.pi * I * a ^ 2) := by
  rw [mordellIntegral_difference,
    show ((1 / 2 : ℂ) ^ (1 / 2 : ℂ) * exp (-Real.pi * I * a ^ 2)) * (1 + I) =
      ((1 / 2 : ℂ) ^ (1 / 2 : ℂ) * (1 + I)) * exp (-Real.pi * I * a ^ 2) by ring,
    mordellGaussian_phase, ← exp_add]
  congr 1
  ring

theorem siegelIntegral_difference (u : ℂ) :
    siegelIntegral u - siegelIntegral (u + 1) = exp (Real.pi * I * (u ^ 2 + u)) := by
  have h := congrArg conj (mordellIntegral_difference_exp (-1 / 2 - conj u))
  simp only [map_sub, map_div₀, map_mul, map_pow, map_neg, map_one, conj_ofNat, conj_ofReal,
    conj_I, ← exp_conj, conj_conj] at h
  have h1 : (-1 / 2 : ℂ) - conj u + 1 = 1 / 2 - conj u := by ring
  have h2 : (-1 / 2 : ℂ) - conj u = 1 / 2 - conj (u + 1) := by simp; ring
  rw [h1, h2, ← siegelIntegral_conj, ← siegelIntegral_conj] at h
  convert h using 1
  congr 1
  ring

theorem siegelIntegral_closed_identity (u : ℂ) :
    siegelIntegral u * (exp (Real.pi * I * u) - exp (-Real.pi * I * u)) =
      exp (Real.pi * I * u) - exp (Real.pi * I * u ^ 2) := by
  have hc := congrArg (fun z : ℂ => z * exp (Real.pi * I * u))
    (siegelIntegral_contour_shift u)
  have hd := congrArg (fun z : ℂ => z * exp (-Real.pi * I * u))
    (siegelIntegral_difference u)
  have he1 : exp (-2 * Real.pi * I * u) * exp (Real.pi * I * u) =
      exp (-Real.pi * I * u) := by rw [← exp_add]; congr 1; ring
  have he2 : exp (Real.pi * I * (u ^ 2 + u)) * exp (-Real.pi * I * u) =
      exp (Real.pi * I * u ^ 2) := by rw [← exp_add]; congr 1; ring
  rw [add_mul, one_mul, mul_right_comm (exp (-2 * Real.pi * I * u)), he1] at hc
  rw [he2] at hd
  linear_combination hc - hd

theorem siegelIntegral_closed_form {u : ℂ}
    (hu : exp (Real.pi * I * u) - exp (-Real.pi * I * u) ≠ 0) :
    siegelIntegral u =
      (exp (Real.pi * I * u) - exp (Real.pi * I * u ^ 2)) /
        (exp (Real.pi * I * u) - exp (-Real.pi * I * u)) :=
  (eq_div_iff hu).mpr (siegelIntegral_closed_identity u)

theorem siegelIntegral_at_removable {u : ℂ}
    (hu : exp (Real.pi * I * u) - exp (-Real.pi * I * u) = 0) :
    siegelIntegral u = 1 / 2 - u := by
  have hs := siegelMoment_hasDerivAt 0 u
  rw [siegelMoment_zero] at hs
  have ha := ((hasDerivAt_id u).const_mul (Real.pi * I)).cexp
  have hb := ((hasDerivAt_id u).const_mul (-Real.pi * I)).cexp
  have hc := (((hasDerivAt_id u).pow 2).const_mul (Real.pi * I)).cexp
  simp only [id_eq, Pi.pow_apply, mul_one, Nat.cast_ofNat, Nat.reduceSub, pow_one] at ha hb hc
  have h := congrArg (fun f : ℂ → ℂ => deriv f u) (funext siegelIntegral_closed_identity)
  have hp := hs.mul (ha.sub hb)
  have hn := ha.sub hc
  change HasDerivAt (fun x : ℂ => siegelIntegral x *
    (exp (Real.pi * I * x) - exp (-Real.pi * I * x))) _ u at hp
  change HasDerivAt (fun x : ℂ => exp (Real.pi * I * x) -
    exp (Real.pi * I * x ^ 2)) _ u at hn
  rw [hp.deriv, hn.deriv] at h
  simp only [Pi.sub_apply] at h
  have h0 := siegelIntegral_closed_identity u
  rw [hu, mul_zero] at h0
  have hBA := (sub_eq_zero.mp hu).symm
  have hCA := (sub_eq_zero.mp h0.symm).symm
  rw [hu, mul_zero, zero_add, hBA, hCA] at h
  apply mul_right_cancel₀ (mul_ne_zero (exp_ne_zero (Real.pi * I * u))
    (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero))
  linear_combination h / 2

theorem siegelIntegral_closed_form_all (u : ℂ) :
    siegelIntegral u =
      if exp (Real.pi * I * u) - exp (-Real.pi * I * u) = 0 then 1 / 2 - u
      else (exp (Real.pi * I * u) - exp (Real.pi * I * u ^ 2)) /
        (exp (Real.pi * I * u) - exp (-Real.pi * I * u)) := by
  split_ifs with hu
  · exact siegelIntegral_at_removable hu
  · exact siegelIntegral_closed_form hu

end LiuWang.Proof.Campaign20260915.ZetaMordell
