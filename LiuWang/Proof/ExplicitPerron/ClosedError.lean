import LiuWang.Proof.ExplicitPerron.Transport
import LiuWang.Proof.ExplicitPerron.NearSum
import LiuWang.Proof.ExplicitPerron.SourceConstants

/-!
# Closed, effective error for the actual real-endpoint integrand

All series and finite arithmetic sums in the error are eliminated. The
remaining expression contains only powers, logarithms and the chosen heights.
It is not asserted here to be at most the paper's decimal budget.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace LiuWang.Proof.ExplicitPerron

def closedHalfError (x b T : ℝ) : ℝ :=
  (x ^ b / Real.log 2 * ((Real.log 4 + 4) * b / (b - 1)) +
    x * (2 ^ b * Real.log x * (Real.log x + 3) +
      Real.log (2 * x) * (Real.log (2 * x) + 3))) / (Real.pi * T)

theorem logCentralCost_halfInteger_le {m : ℕ} (hm : 1 ≤ m) {b : ℝ} (hb : 1 ≤ b) :
    logCentralCost ((m : ℝ) + 1 / 2) b ≤
      ((m : ℝ) + 1 / 2) *
        (2 ^ b * Real.log ((m : ℝ) + 1 / 2) * (Real.log ((m : ℝ) + 1 / 2) + 3) +
          Real.log (2 * ((m : ℝ) + 1 / 2)) * (Real.log (2 * ((m : ℝ) + 1 / 2)) + 3)) := by
  let x : ℝ := (m : ℝ) + 1 / 2
  let a : ℕ → ℂ := fun n => (Real.log n : ℂ)
  let A : ℝ → ℝ := fun u => Real.log (max 1 u)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx1 : 1 ≤ x := by dsimp [x]; linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hA : Monotone A := by
    intro u v huv
    exact Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _)) (max_le_max_left 1 huv)
  have ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ A n := by
    intro n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [a, A, max_eq_right hnR, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg hnR), le_refl]
  have heq : logCentralCost x b = centralCost a x b := by
    apply sum_congr rfl
    intro n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hn).1).1
    simp only [a, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hnR)]
  have h := centralCost_halfInteger_le a A hA ha hm hb
  change centralCost a x b ≤
    2 ^ b * A x * x * halfHarmonic m + A (2 * x) * x * halfHarmonic (m + 1) at h
  simp only [A, max_eq_right hx1, max_eq_right (show 1 ≤ 2 * x by linarith)] at h
  have hlo : halfHarmonic m ≤ Real.log x + 3 := by
    have hlog := Real.log_le_log (by linarith : (0 : ℝ) < m)
      (show (m : ℝ) ≤ x by dsimp [x]; linarith)
    linarith [halfHarmonic_le_log_of_pos hm]
  have hhi : halfHarmonic (m + 1) ≤ Real.log (2 * x) + 3 := by
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < m + 1)
      (show (m : ℝ) + 1 ≤ 2 * x by dsimp [x]; linarith)
    linarith [halfHarmonic_le_log m]
  rw [heq]
  apply h.trans
  change 2 ^ b * Real.log x * x * halfHarmonic m +
    Real.log (2 * x) * x * halfHarmonic (m + 1) ≤
      x * (2 ^ b * Real.log x * (Real.log x + 3) +
        Real.log (2 * x) * (Real.log (2 * x) + 3))
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hl := mul_le_mul_of_nonneg_left hlo
    (show 0 ≤ 2 ^ b * Real.log x * x by positivity)
  have hu := mul_le_mul_of_nonneg_left hhi
    (show 0 ≤ Real.log (2 * x) * x by
      exact mul_nonneg (Real.log_nonneg (by linarith)) hx0.le)
  nlinarith

theorem effectiveError_halfInteger_le_closed {m : ℕ} (hm : 1 ≤ m)
    {b T : ℝ} (hb : 1 ≤ b) (hT : 0 < T) :
    effectiveError ((m : ℝ) + 1 / 2) b T ≤
      closedHalfError ((m : ℝ) + 1 / 2) b T := by
  unfold effectiveError closedHalfError
  gcongr
  exact logCentralCost_halfInteger_le hm hb

def closedRealEndpointError (t b T Hminus Hplus : ℝ) : ℝ :=
  closedHalfError (halfCutoff t) b T + closedHalfError (5 / 2) b T + Real.log 2 +
    heightCorrection (halfCutoff t) (5 / 2) b T + transportCorrection t b Hminus Hplus

theorem norm_realEndpoint_perron_le_closed {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {t b T Hminus Hplus : ℝ}
    (ht : 1 ≤ t) (hb : 1 < b) (hT : 1 < T)
    (hminus : |Hminus + T| ≤ 1) (hplus : |Hplus - T| ≤ 1) :
    ‖vertical (centeredIntegrand chi t (5 / 2)) b Hminus Hplus - psi chi t‖ ≤
      closedRealEndpointError t b T Hminus Hplus := by
  apply (norm_realEndpoint_perron_le chi (zero_lt_one.trans_le ht) hb hT hminus hplus).trans
  have hm : 1 ≤ ⌊t⌋₊ := (Nat.le_floor_iff (zero_le_one.trans ht)).2 (by simpa using ht)
  have h1 := effectiveError_halfInteger_le_closed hm hb.le (zero_lt_one.trans hT)
  have h2 := effectiveError_halfInteger_le_closed (m := 2) (by norm_num) hb.le
    (zero_lt_one.trans hT)
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) + 1 / 2 = 5 / 2 by norm_num] at h2
  unfold realEndpointError closedRealEndpointError
  change effectiveError (halfCutoff t) b T ≤ closedHalfError (halfCutoff t) b T at h1
  linarith

end LiuWang.Proof.ExplicitPerron
