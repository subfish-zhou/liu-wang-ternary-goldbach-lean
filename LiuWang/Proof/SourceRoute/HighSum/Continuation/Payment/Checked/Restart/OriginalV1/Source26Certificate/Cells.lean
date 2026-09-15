import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate.Kernel

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate

def coeffA (v : ℝ) : ℝ := 17102 * (3100 / (3100 - 4 * v)) * 6.77 + 16541
def coeffB (v : ℝ) : ℝ := 254231 * (3100 / (3100 - 4 * v)) * 6.77

def cellSlope (u v : ℝ) : ℝ :=
  5 / ((u + v) / 2) + coeffA v / (coeffA v * ((u + v) / 2) + coeffB v) +
    1481.8 / ((u + v) / 2) ^ (2 : ℕ) - 1

def cellMass (u v : ℝ) : ℝ :=
  (3100 : ℝ) ^ (4 : ℕ) * ((u + v) / 2) ^ (5 : ℕ) *
    (coeffA v * ((u + v) / 2) + coeffB v)

def cellPhase (u v s : ℝ) : ℝ :=
  phase 1481.8 ((u + v) / 2) + cellSlope u v * (s - (u + v) / 2)

def cellBound (u v : ℝ) : ℝ :=
  (v - u) / 2 * cellMass u v * (Real.exp (cellPhase u v u) + Real.exp (cellPhase u v v))

theorem base_polynomial_upper {u v s : ℝ} (hu : 0 < u)
    (hv : v ≤ 100) (hs : s ∈ Set.Icc u v) :
    integrand 3100 s ≤ (3100 : ℝ) ^ (4 : ℕ) * s ^ (5 : ℕ) *
      (coeffA v * s + coeffB v) * Real.exp (phase 1481.8 s) := by
  have hs0 := hu.trans_le hs.1
  have hd : 0 < 3100 - 4 * s := by linarith [hs.2]
  have hdv : 0 < 3100 - 4 * v := by linarith
  have hr : 3100 / (3100 - 4 * s) ≤ 3100 / (3100 - 4 * v) := by
    gcongr
    exact hs.2
  have hc := mul_le_mul
    (mul_le_mul_of_nonneg_left hr (show 0 ≤ 17102 + 254231 / s by positivity))
    exp_1912_upper (Real.exp_pos _).le (by positivity)
  rw [integrand_factor 3100 hs0.ne']
  have hm := mul_le_mul_of_nonneg_left (add_le_add hc (le_refl (16541 : ℝ)))
    (show 0 ≤ s ^ (6 : ℕ) * Real.exp (-s) by positivity)
  have h := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ (3100 : ℝ) ^ (4 : ℕ) * Real.exp (-(0.478 / s) * 3100) by positivity)
  apply h.trans_eq
  unfold coeffA coeffB phase
  rw [show -s - (1481.8 : ℝ) / s = -s + -(0.478 / s) * 3100 by ring, Real.exp_add]
  field_simp
  ring

theorem polynomial_exp_tangent {A B m s : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (hm : 0 < m) (hs : 0 < s) :
    s ^ (5 : ℕ) * (A * s + B) * Real.exp (phase 1481.8 s) ≤
      m ^ (5 : ℕ) * (A * m + B) *
        Real.exp (phase 1481.8 m +
          (5 / m + A / (A * m + B) + 1481.8 / m ^ (2 : ℕ) - 1) * (s - m)) := by
  have hM : 0 < A * m + B := by positivity
  have hS : 0 < A * s + B := by positivity
  have hratio : s / m ≤ Real.exp ((s - m) / m) := by
    convert Real.add_one_le_exp ((s - m) / m) using 1
    field_simp
    ring
  have hp := pow_le_pow_left₀ (div_nonneg hs.le hm.le) hratio 5
  rw [← Real.exp_nat_mul] at hp
  have hp' : s ^ (5 : ℕ) ≤ m ^ (5 : ℕ) * Real.exp (5 * ((s - m) / m)) := by
    have h := mul_le_mul_of_nonneg_left hp (pow_nonneg hm.le 5)
    simpa only [div_pow, mul_div_cancel₀ _ (pow_ne_zero 5 hm.ne'), Nat.cast_ofNat] using h
  have haff : (A * s + B) / (A * m + B) ≤ Real.exp (A * (s - m) / (A * m + B)) := by
    convert Real.add_one_le_exp (A * (s - m) / (A * m + B)) using 1
    field_simp
    ring
  have haff' := (div_le_iff₀ hM).mp haff
  have hphase := Real.exp_le_exp.mpr (phase_le_tangent (by norm_num : (0 : ℝ) ≤ 1481.8) hm hs)
  have h := mul_le_mul (mul_le_mul hp' haff' hS.le (by positivity)) hphase
    (Real.exp_pos _).le (by positivity)
  apply h.trans_eq
  unfold tangent
  calc
    _ = m ^ (5 : ℕ) * (A * m + B) *
        (Real.exp (5 * ((s - m) / m)) * Real.exp (A * (s - m) / (A * m + B)) *
          Real.exp (phase 1481.8 m + (1481.8 / m ^ (2 : ℕ) - 1) * (s - m))) := by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

theorem cell_pointwise {u v s : ℝ} (hu : 0 < u) (huv : u < v) (hv : v ≤ 100)
    (hs : s ∈ Set.Icc u v) :
    integrand 3100 s ≤ cellMass u v * Real.exp (cellPhase u v s) := by
  have hm : 0 < (u + v) / 2 := by linarith
  have hd : 0 < 3100 - 4 * v := by linarith
  have hA : 0 ≤ coeffA v := by unfold coeffA; positivity
  have hB : 0 < coeffB v := by unfold coeffB; positivity
  have h := mul_le_mul_of_nonneg_left
    (polynomial_exp_tangent hA hB hm (hu.trans_le hs.1))
    (by norm_num : (0 : ℝ) ≤ 3100 ^ (4 : ℕ))
  exact (base_polynomial_upper hu hv hs).trans (by
    simpa only [cellMass, cellPhase, cellSlope, mul_assoc] using h)

theorem cell_integral_upper {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v ≤ 100) :
    (∫ s in u..v, integrand 3100 s) ≤ cellBound u v := by
  have hb : v ≤ 18 * Real.log (3100 : ℝ) := by linarith [log_3100_bounds.1]
  have hd : 0 < v - u := sub_pos.mpr huv
  have hden : 0 < 3100 - 4 * v := by linarith
  have hM : 0 ≤ cellMass u v := by
    unfold cellMass coeffA coeffB
    have : 0 < (u + v) / 2 := by linarith
    positivity
  have hp (s : ℝ) (hs : s ∈ Set.Icc u v) :
      integrand 3100 s ≤ cellMass u v *
        chord u v (Real.exp (cellPhase u v u)) (Real.exp (cellPhase u v v)) s := by
    have hw : (v - s) / (v - u) + (s - u) / (v - u) = 1 := by field_simp; ring
    have hh := convexOn_exp.2 (Set.mem_univ (cellPhase u v u)) (Set.mem_univ (cellPhase u v v))
      (div_nonneg (sub_nonneg.mpr hs.2) hd.le)
      (div_nonneg (sub_nonneg.mpr hs.1) hd.le) hw
    have he : (v - s) / (v - u) * cellPhase u v u +
        (s - u) / (v - u) * cellPhase u v v = cellPhase u v s := by
      unfold cellPhase
      field_simp
      ring
    simp only [smul_eq_mul, he] at hh
    exact (cell_pointwise hu huv hv hs).trans (mul_le_mul_of_nonneg_left hh hM)
  have hi := intervalIntegral.integral_mono_on huv.le
    (integrand_integrable (by norm_num) hu huv.le hb)
    ((chord_integrable u v _ _).const_mul (cellMass u v)) hp
  rw [intervalIntegral.integral_const_mul, integral_chord huv] at hi
  exact hi.trans_eq (by unfold cellBound; ring)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate
