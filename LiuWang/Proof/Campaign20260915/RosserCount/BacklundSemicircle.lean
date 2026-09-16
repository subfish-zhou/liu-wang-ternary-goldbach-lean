import LiuWang.Proof.Campaign20260915.RosserCount.BacklundEnvelope

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex Metric MeasureTheory MeromorphicOn
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.Totient

private theorem shifted_zeta_conj (T : ℝ) (s : ℂ) :
    riemannZeta (conj s + 5 / 4 + (T : ℂ) * I) =
      conj (riemannZeta (s + 5 / 4 - (T : ℂ) * I)) ∧
    riemannZeta (conj s + 5 / 4 - (T : ℂ) * I) =
      conj (riemannZeta (s + 5 / 4 + (T : ℂ) * I)) := by
  have hp : conj s + 5 / 4 + (T : ℂ) * I = conj (s + 5 / 4 - (T : ℂ) * I) := by
    simp [map_sub, map_add, map_div₀, map_mul, conj_ofNat]
  have hm : conj s + 5 / 4 - (T : ℂ) * I = conj (s + 5 / 4 + (T : ℂ) * I) := by
    simp [map_add, map_div₀, map_mul, conj_ofNat, sub_eq_add_neg]
  exact ⟨by rw [hp, riemannZeta_conj], by rw [hm, riemannZeta_conj]⟩

theorem backlundAux_conj (T : ℝ) (n : ℕ) (s : ℂ) :
    backlundAux T n (conj s) = conj (backlundAux T n s) := by
  have h := shifted_zeta_conj T s
  simp only [backlundAux, h.1, h.2, map_div₀, map_add, map_pow, conj_ofNat]
  ring

theorem backlundCircleEnvelope_conj (T : ℝ) (s : ℂ) :
    backlundCircleEnvelope T (conj s) = backlundCircleEnvelope T s := by
  have h := shifted_zeta_conj T s
  simp only [backlundCircleEnvelope, h.1, h.2, Complex.norm_conj, max_comm]

private theorem half_circle_integral {f : ℂ → ℝ} {r : ℝ}
    (hi : CircleIntegrable f 0 r) (hf : ∀ s : ℂ, f (conj s) = f s) :
    (∫ θ in (0 : ℝ)..Real.pi, f (circleMap 0 r θ)) =
      Real.pi * Real.circleAverage f 0 r := by
  let g : ℝ → ℝ := fun θ => f (circleMap 0 r θ)
  have hg : ∀ θ : ℝ, g (2 * Real.pi - θ) = g θ := by
    intro θ
    dsimp [g]
    rw [show 2 * Real.pi - θ = -θ + 2 * Real.pi by ring,
      periodic_circleMap 0 r (-θ), ← conj_circleMap_zero, hf]
  have hs := intervalIntegral.integral_comp_sub_left g (a := 0) (b := Real.pi)
    (2 * Real.pi)
  simp only [hg, sub_zero, show 2 * Real.pi - Real.pi = Real.pi by ring] at hs
  have hp : Real.pi ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) := by
    rw [Set.uIcc_of_le (by positivity)]
    constructor <;> linarith [Real.pi_pos]
  have h1 := hi.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc hp)
  have h2 := hi.mono_set (Set.uIcc_subset_uIcc hp Set.right_mem_uIcc)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  change (∫ θ in (0 : ℝ)..Real.pi, g θ) +
    (∫ θ in Real.pi..2 * Real.pi, g θ) = ∫ θ in (0 : ℝ)..2 * Real.pi, g θ at hadd
  rw [← hs] at hadd
  have hall : (∫ θ in (0 : ℝ)..2 * Real.pi, g θ) =
      2 * (∫ θ in (0 : ℝ)..Real.pi, g θ) := by linarith
  change (∫ θ in (0 : ℝ)..Real.pi, g θ) =
    Real.pi * ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, g θ)
  rw [hall]
  field_simp

theorem backlundAux_half_circle_integral {T : ℝ} (hT : rsA ≤ T) (n : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.log ‖backlundAux T n (circleMap 0 (33 / 25 : ℝ) θ)‖) =
      Real.pi * Real.circleAverage (fun s => Real.log ‖backlundAux T n s‖)
        0 (33 / 25 : ℝ) := by
  apply half_circle_integral (backlundAux_circleIntegrable_log_norm hT n)
  intro s
  rw [backlundAux_conj, Complex.norm_conj]

theorem backlundEnvelope_half_circle_integral {T : ℝ} (hT : rsA ≤ T) :
    (∫ θ in (0 : ℝ)..Real.pi,
      backlundCircleEnvelope T (circleMap 0 (33 / 25 : ℝ) θ)) =
      Real.pi * Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) :=
  half_circle_integral (backlundCircleEnvelope_circleIntegrable hT)
    (backlundCircleEnvelope_conj T)

def backlundSourceJensenTerm (T : ℝ) (n : ℕ) : ℝ :=
  (∫ θ in (0 : ℝ)..Real.pi, Real.log ‖backlundAux T n (circleMap 0 (33 / 25 : ℝ) θ)‖) /
    (2 * Real.pi * Real.log (44 / 25 : ℝ) * (n : ℝ)) -
      Real.log ‖backlundAux T n 0‖ / (2 * Real.log (44 / 25 : ℝ) * (n : ℝ))

theorem backlundSourceJensenTerm_eq_average {T : ℝ} (hT : rsA ≤ T) (n : ℕ) :
    backlundSourceJensenTerm T n =
      (Real.circleAverage (fun s => Real.log ‖backlundAux T n s‖) 0 (33 / 25 : ℝ) -
        Real.log ‖backlundAux T n 0‖) / (2 * Real.log (44 / 25 : ℝ) * (n : ℝ)) := by
  unfold backlundSourceJensenTerm
  rw [backlundAux_half_circle_integral hT n]
  by_cases hn : n = 0
  · simp [hn]
  · have hq : 0 < Real.log (44 / 25 : ℝ) := Real.log_pos (by norm_num)
    field_simp

theorem backlundSourceJensenTerm_eq_divisor {T : ℝ} (hT : rsA ≤ T) {n : ℕ}
    (hn : backlundAux T n 0 ≠ 0) :
    backlundSourceJensenTerm T n =
      (∑ᶠ z, (divisor (backlundAux T n) (closedBall 0 (33 / 25 : ℝ)) z : ℝ) *
        Real.log ((33 / 25 : ℝ) * ‖z‖⁻¹)) /
      (2 * Real.log (44 / 25 : ℝ) * (n : ℝ)) := by
  rw [backlundSourceJensenTerm_eq_average hT n, backlundAux_jensen_formula hT hn,
    add_sub_cancel_right]

theorem backlundSourceJensenTerm_le_envelope {T : ℝ} (hT : rsA ≤ T) {n : ℕ}
    (hn : backlundAux T n 0 ≠ 0) :
    backlundSourceJensenTerm T n ≤
      ((n : ℝ) * Real.circleAverage (backlundCircleEnvelope T) 0 (33 / 25 : ℝ) -
        Real.log ‖backlundAux T n 0‖) / (2 * Real.log (44 / 25 : ℝ) * (n : ℝ)) := by
  rw [backlundSourceJensenTerm_eq_average hT n]
  apply div_le_div_of_nonneg_right
    (sub_le_sub_right (backlundAux_circleAverage_le_envelope hT hn) _)
  have hq : 0 < Real.log (44 / 25 : ℝ) := Real.log_pos (by norm_num)
  positivity

#print axioms backlundAux_conj
#print axioms backlundCircleEnvelope_conj
#print axioms backlundAux_half_circle_integral
#print axioms backlundEnvelope_half_circle_integral
#print axioms backlundSourceJensenTerm_eq_average
#print axioms backlundSourceJensenTerm_eq_divisor
#print axioms backlundSourceJensenTerm_le_envelope

end LiuWang.Proof.Campaign20260915.RosserCount
