import LiuWang.Proof.PerronRecovery.Actual
import LiuWang.Proof.PerronBudget.ScalarBounds

/-! Closed majorants retain the actual half-cutoff, the base point 2.5,
the literal power of two and the pole-plus-eight series factor. -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.PerronRecovery

open ExplicitPerron Interfaces Parameters

def halfError (x b T C : ℝ) : ℝ :=
  (x ^ b / Real.log 2 * C +
    x * (2 ^ b * Real.log x * (Real.log x + 3) +
      Real.log (2 * x) * (Real.log (2 * x) + 3))) / (Real.pi * T)

def closedError (t b T lo hi C : ℝ) : ℝ :=
  halfError (halfCutoff t) b T C + halfError (5 / 2) b T C + Real.log 2 +
    heightError (halfCutoff t) (5 / 2) b T C + endpointError t b lo hi C

def errorFunction (t b T C : ℝ) : ℝ :=
  halfError (halfCutoff t) b T C + halfError (5 / 2) b T C + Real.log 2 +
    heightError (halfCutoff t) (5 / 2) b T C +
    C * (max (halfCutoff t) t) ^ (b - 1) * (T + 1) / (2 * Real.pi)

theorem truncationError_le_halfError {q : ℕ} (chi : DirichletCharacter ℂ q)
    {m : ℕ} (hm : 1 ≤ m) {b T C : ℝ} (hb : 1 ≤ b) (hT : 0 < T) :
    truncationError chi ((m : ℝ) + 1 / 2) b T C ≤
      halfError ((m : ℝ) + 1 / 2) b T C := by
  unfold truncationError halfError
  gcongr
  exact (centralCost_twisted_le chi (by positivity) b).trans
    (logCentralCost_halfInteger_le hm hb)

theorem actualError_le_closedError {q : ℕ} (chi : DirichletCharacter ℂ q)
    {t b T lo hi C : ℝ} (ht : 1 ≤ t) (hb : 1 ≤ b) (hT : 0 < T) :
    actualError chi t b T lo hi C ≤ closedError t b T lo hi C := by
  have hm : 1 ≤ ⌊t⌋₊ := (Nat.le_floor_iff (zero_le_one.trans ht)).2 (by simpa using ht)
  have hx := truncationError_le_halfError chi hm (C := C) hb hT
  have hy := truncationError_le_halfError chi (m := 2) (C := C) (by norm_num) hb hT
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) + 1 / 2 = 5 / 2 by norm_num] at hy
  change truncationError chi (halfCutoff t) b T C ≤ halfError (halfCutoff t) b T C at hx
  unfold actualError closedError
  linarith

theorem closedError_le_errorFunction {t b T lo hi C : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hlo : |lo + T| ≤ 1) (hhi : |hi - T| ≤ 1) :
    closedError t b T lo hi C ≤ errorFunction t b T C := by
  have hgap : |hi - lo| ≤ 2 * (T + 1) := by
    rw [abs_le]
    obtain ⟨hl, hl'⟩ := abs_le.mp hlo
    obtain ⟨hh, hh'⟩ := abs_le.mp hhi
    constructor <;> linarith
  have hp : 0 ≤ (max (halfCutoff t) t) ^ (b - 1) :=
    Real.rpow_nonneg ((halfCutoff_pos t).le.trans (le_max_left _ _)) _
  have hnum : C * (max (halfCutoff t) t) ^ (b - 1) * (1 / 2) * |hi - lo| ≤
      C * (max (halfCutoff t) t) ^ (b - 1) * (T + 1) := by
    calc
      _ ≤ C * (max (halfCutoff t) t) ^ (b - 1) * (1 / 2) * (2 * (T + 1)) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = _ := by ring
  exact add_le_add le_rfl
    (div_le_div_of_nonneg_right hnum (show 0 ≤ 2 * Real.pi by positivity))

theorem norm_perron_le_errorFunction {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {t b T lo hi : ℝ}
    (ht : 1 ≤ t) (hb : 1 < b) (hb' : b ≤ 5 / 4) (hT : 1 < T)
    (hlo : |lo + T| ≤ 1) (hhi : |hi - T| ≤ 1) :
    ‖vertical (centeredIntegrand chi t (5 / 2)) b lo hi - psi chi t‖ ≤
      errorFunction t b T (seriesBound b) :=
  (norm_actual_perron_le_strong chi (zero_lt_one.trans_le ht) hb hb' hT hlo hhi).trans
    ((actualError_le_closedError chi ht hb.le (zero_lt_one.trans hT)).trans
      (closedError_le_errorFunction (seriesBound_nonneg hb) (by linarith) hlo hhi))

def sourceError (N : ℕ) (t : ℝ) : ℝ :=
  errorFunction t (1 + 1 / sourceL N) (sourceT N) (sourceL N + 8)

theorem source_right_perron_function {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hN : Real.exp 2000 ≤ (N : ℝ))
    {t lo hi : ℝ} (ht : sourceWindowLower N ≤ t)
    (hlo : |lo + sourceT N| ≤ 1) (hhi : |hi - sourceT N| ≤ 1) :
    ‖vertical (centeredIntegrand chi t (5 / 2)) (1 + 1 / sourceL N) lo hi -
      psi chi t‖ ≤ sourceError N t := by
  have hL := sourceL_ge_2000 hN
  have hb := source_abscissa_mem (by linarith : 4 ≤ sourceL N)
  have hpow : sourceL N ≤ sourceT N := by
    simpa only [pow_one, sourceT] using
      pow_le_pow_right₀ (one_le_sourceL hN) (show (1 : ℕ) ≤ 15 by norm_num)
  have hT : 1 < sourceT N := by linarith
  have ht1 : 1 ≤ t := by have := sourceT_lt_real_endpoint hN ht; linarith
  simpa only [sourceError, seriesBound_source] using
    norm_perron_le_errorFunction chi ht1 hb.1 hb.2 hT hlo hhi

end LiuWang.Proof.PerronRecovery
