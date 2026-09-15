import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Set

namespace LiuWang.Proof.Campaign20260915.RSSection8Scalar

/-- RS1962 (8.5), in the original `x` variable. -/
def M (x a : ℝ) : ℝ :=
  Real.log x * Real.log (1 + 1 / (2 * Real.log x ^ 2)) - a / Real.log x

def logM (t a : ℝ) : ℝ :=
  t * Real.log (1 + 1 / (2 * t ^ 2)) - a / t

theorem M_eq_logM (x a : ℝ) : M x a = logM (Real.log x) a := rfl

theorem logM_deriv {t : ℝ} (ht : 0 < t) (a : ℝ) :
    HasDerivAt (fun u => logM u a)
      (Real.log (1 + 1 / (2 * t ^ 2)) - 2 / (2 * t ^ 2 + 1) + a / t ^ 2) t := by
  have hden : 2 * t ^ 2 ≠ 0 := by positivity
  have harg : 0 < 1 + 1 / (2 * t ^ 2) := by positivity
  have hden' : 2 * t ^ 2 + 1 ≠ 0 := by positivity
  have hi := ((hasDerivAt_pow 2 t).const_mul 2).inv hden
  have hl := (hi.const_add 1).log (by simpa only [Pi.inv_apply, one_div] using harg.ne')
  have hd := ((hasDerivAt_id t).mul hl).sub
    ((hasDerivAt_const t a).div (hasDerivAt_id t) ht.ne')
  convert! hd using 1
  · ext u
    simp [logM, one_div]
  · dsimp
    field_simp
    ring

theorem logM_deriv_nonpos {t a : ℝ} (ht : 0 < t)
    (hdom : (1 / 2 + a) ≤ (1 - 2 * a) * t ^ 2) :
    Real.log (1 + 1 / (2 * t ^ 2)) - 2 / (2 * t ^ 2 + 1) + a / t ^ 2 ≤ 0 := by
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (2 * t ^ 2) by positivity)
  have halg : 1 / (2 * t ^ 2) - 2 / (2 * t ^ 2 + 1) + a / t ^ 2 =
      ((1 / 2 + a) - (1 - 2 * a) * t ^ 2) / (t ^ 2 * (2 * t ^ 2 + 1)) := by
    field_simp
    ring
  have hn : ((1 / 2 + a) - (1 - 2 * a) * t ^ 2) /
      (t ^ 2 * (2 * t ^ 2 + 1)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdom) (by positivity)
  rw [← halg] at hn
  linarith

theorem logM_antitoneOn {T a : ℝ} (hT : 0 < T) (ha : a < 1 / 2)
    (hdom : (1 / 2 + a) ≤ (1 - 2 * a) * T ^ 2) :
    AntitoneOn (fun t => logM t a) (Ici T) := by
  have hd (t : ℝ) (ht : t ∈ Ici T) := logM_deriv (hT.trans_le ht) a
  apply antitoneOn_of_deriv_nonpos (convex_Ici T)
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have htT : T ≤ t := interior_subset ht
    rw [(hd t htT).deriv]
    apply logM_deriv_nonpos (hT.trans_le htT)
    exact hdom.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT.le htT 2)
      (by linarith))

theorem M_antitoneOn_of_square {A a : ℝ} (hA : 1 < A) (ha : a < 1 / 2)
    (hdom : (1 / 2 + a) ≤ (1 - 2 * a) * Real.log A ^ 2) :
    AntitoneOn (fun x => M x a) (Ici A) := by
  intro x hx y hy hxy
  change A ≤ x at hx
  change A ≤ y at hy
  apply logM_antitoneOn (Real.log_pos hA) ha hdom
  · exact Real.log_le_log (by linarith) hx
  · exact Real.log_le_log (by linarith) hy
  · exact Real.log_le_log (by linarith) hxy

theorem M_antitoneOn {A a : ℝ} (hA : 1 < A) (ha : a < 1 / 2)
    (hdom : Real.sqrt ((1 / 2) * (1 + 2 * a) / (1 - 2 * a)) ≤ Real.log A) :
    AntitoneOn (fun x => M x a) (Ici A) := by
  apply M_antitoneOn_of_square hA ha
  have hd : 0 < 1 - 2 * a := by linarith
  by_cases hnum : 0 ≤ (1 / 2) * (1 + 2 * a)
  · have hs := Real.sq_sqrt (div_nonneg hnum hd.le)
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hdom 2
    rw [hs] at hsq
    have hh := (div_le_iff₀ hd).mp hsq
    nlinarith
  · have hpos := mul_nonneg hd.le (sq_nonneg (Real.log A))
    linarith

theorem M_endpoint_le {A B x a : ℝ} (hA : 1 < A) (ha : a < 1 / 2)
    (hdom : Real.sqrt ((1 / 2) * (1 + 2 * a) / (1 - 2 * a)) ≤ Real.log A)
    (hx : x ∈ Icc A B) : M B a ≤ M x a :=
  M_antitoneOn hA ha hdom hx.1 (hx.1.trans hx.2) hx.2

#print axioms M_antitoneOn
#print axioms M_endpoint_le

end LiuWang.Proof.Campaign20260915.RSSection8Scalar
