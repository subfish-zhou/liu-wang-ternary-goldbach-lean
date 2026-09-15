import LiuWang.Proof.ExplicitPerron.Centered
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Transport from the half-integer cutoff to the actual real endpoint

The arithmetic sum is unchanged, while the actual complex power in the
vertical integrand is changed with an explicit integral estimate.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace LiuWang.Proof.ExplicitPerron

def halfCutoff (t : ℝ) : ℝ := (⌊t⌋₊ : ℝ) + 1 / 2

theorem psi_halfCutoff {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) :
    psi chi (halfCutoff t) = psi chi t := by
  simp only [psi, halfCutoff, floor_halfInteger]

theorem halfCutoff_pos (t : ℝ) : 0 < halfCutoff t := by
  unfold halfCutoff
  positivity

theorem abs_sub_halfCutoff_le {t : ℝ} (ht : 0 ≤ t) :
    |t - halfCutoff t| ≤ 1 / 2 := by
  have hlo := Nat.floor_le ht
  have hhi := Nat.lt_floor_add_one t
  rw [abs_le]
  dsimp [halfCutoff]
  constructor <;> linarith

theorem norm_cpow_sub_div_le {x t b u : ℝ}
    (hx : 0 < x) (ht : 0 < t) (hb : 1 < b) :
    ‖((t : ℂ) ^ ((b : ℂ) + u * Complex.I) -
        (x : ℂ) ^ ((b : ℂ) + u * Complex.I)) / ((b : ℂ) + u * Complex.I)‖ ≤
      (max x t) ^ (b - 1) * |t - x| := by
  have heq := integral_cpow (a := x) (b := t)
    (r := ((b : ℂ) + u * Complex.I) - 1)
    (Or.inl (by simp; linarith : -1 < (((b : ℂ) + u * Complex.I) - 1).re))
  simp only [sub_add_cancel] at heq
  rw [← heq]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro v hv
  have hv0 : 0 < v := (lt_min hx ht).trans hv.1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hv0]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
    add_zero, Complex.one_re]
  exact Real.rpow_le_rpow hv0.le hv.2 (by linarith)

theorem norm_centered_vertical_transport_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {x t y b : ℝ}
    (hx : 0 < x) (ht : 0 < t) (hy : 0 < y) (hb : 1 < b) (lo hi : ℝ) :
    ‖vertical (centeredIntegrand chi t y) b lo hi -
      vertical (centeredIntegrand chi x y) b lo hi‖ ≤
      ((Real.log 4 + 4) * b / (b - 1)) * (max x t) ^ (b - 1) *
        |t - x| * |hi - lo| / (2 * Real.pi) := by
  have heq : vertical (centeredIntegrand chi t y) b lo hi -
      vertical (centeredIntegrand chi x y) b lo hi =
      vertical (fun s => centeredIntegrand chi t y s - centeredIntegrand chi x y s)
        b lo hi := by
    unfold vertical
    rw [intervalIntegral.integral_sub
      ((continuous_centeredIntegrand chi ht hy hb).intervalIntegrable lo hi)
      ((continuous_centeredIntegrand chi hx hy hb).intervalIntegrable lo hi), mul_sub]
  rw [heq]
  apply norm_vertical_le_const
  intro u hu
  have heq' : centeredIntegrand chi t y ((b : ℂ) + u * Complex.I) -
      centeredIntegrand chi x y ((b : ℂ) + u * Complex.I) =
      (-logDeriv chi.LFunction ((b : ℂ) + u * Complex.I)) *
        (((t : ℂ) ^ ((b : ℂ) + u * Complex.I) -
          (x : ℂ) ^ ((b : ℂ) + u * Complex.I)) / ((b : ℂ) + u * Complex.I)) := by
    unfold centeredIntegrand
    ring
  rw [heq', norm_mul]
  have hlog := norm_logDeriv_le chi (s := (b : ℂ) + u * Complex.I) (by simpa using hb)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] at hlog
  calc
    _ ≤ ((Real.log 4 + 4) * b / (b - 1)) * ((max x t) ^ (b - 1) * |t - x|) :=
      mul_le_mul hlog (norm_cpow_sub_div_le hx ht hb) (norm_nonneg _) (by positivity)
    _ = _ := by ring

def transportCorrection (t b lo hi : ℝ) : ℝ :=
  ((Real.log 4 + 4) * b / (b - 1)) * (max (halfCutoff t) t) ^ (b - 1) *
    (1 / 2) * |hi - lo| / (2 * Real.pi)

def realEndpointError (t b T Hminus Hplus : ℝ) : ℝ :=
  effectiveError (halfCutoff t) b T + effectiveError (5 / 2) b T + Real.log 2 +
    heightCorrection (halfCutoff t) (5 / 2) b T + transportCorrection t b Hminus Hplus

theorem norm_realEndpoint_perron_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {t b T Hminus Hplus : ℝ}
    (ht : 0 < t) (hb : 1 < b) (hT : 1 < T)
    (hminus : |Hminus + T| ≤ 1) (hplus : |Hplus - T| ≤ 1) :
    ‖vertical (centeredIntegrand chi t (5 / 2)) b Hminus Hplus - psi chi t‖ ≤
      realEndpointError t b T Hminus Hplus := by
  have hh := norm_asymmetric_centered_perron_le chi (halfCutoff_pos t)
    (halfInteger_ne_nat ⌊t⌋₊) hb hT hminus hplus
  rw [psi_halfCutoff] at hh
  have ht' := norm_centered_vertical_transport_le chi
    (halfCutoff_pos t) ht (by norm_num : (0 : ℝ) < 5 / 2) hb Hminus Hplus
  have htrans :
      ‖vertical (centeredIntegrand chi t (5 / 2)) b Hminus Hplus -
        vertical (centeredIntegrand chi (halfCutoff t) (5 / 2)) b Hminus Hplus‖ ≤
        transportCorrection t b Hminus Hplus := by
    apply ht'.trans
    unfold transportCorrection
    gcongr
    exact abs_sub_halfCutoff_le ht.le
  have htri := norm_sub_le
    (vertical (centeredIntegrand chi t (5 / 2)) b Hminus Hplus -
      vertical (centeredIntegrand chi (halfCutoff t) (5 / 2)) b Hminus Hplus)
    (psi chi t - vertical (centeredIntegrand chi (halfCutoff t) (5 / 2)) b Hminus Hplus)
  rw [norm_sub_rev (psi chi t)] at htri
  have heq :
      (vertical (centeredIntegrand chi t (5 / 2)) b Hminus Hplus -
        vertical (centeredIntegrand chi (halfCutoff t) (5 / 2)) b Hminus Hplus) -
      (psi chi t - vertical (centeredIntegrand chi (halfCutoff t) (5 / 2)) b Hminus Hplus) =
      vertical (centeredIntegrand chi t (5 / 2)) b Hminus Hplus - psi chi t := by ring
  rw [heq] at htri
  unfold realEndpointError
  linarith

end LiuWang.Proof.ExplicitPerron
