import LiuWang.Proof.PerronRecovery.Series

/-! Parameterized errors for the actual vertical integral. The parameter
majorizes the actual Mangoldt norm sum, not the desired Perron error.
The finite central costs, both half-integer cutoffs and all transports remain. -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Interval

namespace LiuWang.Proof.PerronRecovery

open ExplicitPerron BombieriVinogradov.SiegelWalfisz

def truncationError {q : ℕ} (chi : DirichletCharacter ℂ q) (x b T C : ℝ) : ℝ :=
  (x ^ b / Real.log 2 * C + centralCost (twistedMangoldtSequence chi) x b) /
    (Real.pi * T)

def heightError (x y b T C : ℝ) : ℝ :=
  C * (x ^ b + y ^ b) / (Real.pi * (T - 1))

def endpointError (t b lo hi C : ℝ) : ℝ :=
  C * (max (halfCutoff t) t) ^ (b - 1) * (1 / 2) * |hi - lo| / (2 * Real.pi)

def actualError {q : ℕ} (chi : DirichletCharacter ℂ q) (t b T lo hi C : ℝ) : ℝ :=
  truncationError chi (halfCutoff t) b T C + truncationError chi (5 / 2) b T C +
    Real.log 2 + heightError (halfCutoff t) (5 / 2) b T C + endpointError t b lo hi C

theorem normSum_twisted_le_of_majorant {q : ℕ} (chi : DirichletCharacter ℂ q)
    {b C : ℝ} (hb : 1 < b) (hC : vonMangoldtLSeriesNormSum b ≤ C) :
    (∑' n, ‖LSeries.term (twistedMangoldtSequence chi) (b : ℂ) n‖) ≤ C := by
  apply le_trans _ hC
  apply (twisted_summable chi (by simpa using hb)).norm.tsum_le_tsum
  · intro n
    apply LSeries.norm_term_le
    simpa only [Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      using norm_twistedMangoldtSequence_le_vonMangoldt chi n
  · exact (ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (b : ℂ)) (by simpa using hb)).norm

theorem norm_logDeriv_le_of_majorant {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} {C : ℝ}
    (hs : 1 < s.re) (hC : vonMangoldtLSeriesNormSum s.re ≤ C) :
    ‖-logDeriv chi.LFunction s‖ ≤ C := by
  have h := norm_neg_logDeriv_LFunction_le_zeta_re chi hs
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (s.re : ℂ)) (by simpa using hs), ← mangoldt_normSum_eq_norm] at h
  simpa only [logDeriv_apply, neg_div] using h.trans hC

theorem norm_character_perron_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {x b T C : ℝ}
    (hx : 0 < x) (hxn : ∀ n : ℕ, x ≠ n) (hb : 1 < b) (hT : 0 < T)
    (hC : vonMangoldtLSeriesNormSum b ≤ C) :
    ‖vertical (characterIntegrand chi x) b (-T) T - psi chi x‖ ≤
      truncationError chi x b T C := by
  rw [character_vertical_eq_series chi x hb, psi_eq_sum_twisted]
  apply (norm_vertical_sub_sum_le_dyadic (twistedMangoldtSequence chi)
    hx hxn (zero_lt_one.trans hb) hT (twisted_summable chi (by simpa using hb))).trans
  unfold truncationError
  gcongr
  exact normSum_twisted_le_of_majorant chi hb hC

theorem norm_vertical_shift_le (f : ℂ → ℂ) {b T lo hi K : ℝ}
    (hc : Continuous (fun u : ℝ => f (b + u * Complex.I)))
    (hK : 0 ≤ K) (hlo : |lo + T| ≤ 1) (hhi : |hi - T| ≤ 1)
    (hf : ∀ u : ℝ, T - 1 ≤ |u| → ‖f (b + u * Complex.I)‖ ≤ K) :
    ‖vertical f b lo hi - vertical f b (-T) T‖ ≤ K / Real.pi := by
  have heq : vertical f b lo hi - vertical f b (-T) T =
      vertical f b T hi - vertical f b (-T) lo := by
    simp only [vertical, ← mul_sub]
    congr 1
    exact intervalIntegral.integral_interval_sub_interval_comm'
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have hp : ‖vertical f b T hi‖ ≤ K / (2 * Real.pi) := by
    apply (norm_vertical_le_const f b T hi K ?_).trans
    · exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    · intro u hu
      apply hf
      have hmin : T - 1 ≤ min T hi :=
        le_min (by linarith) (by linarith [(abs_le.mp hhi).1])
      exact (hmin.trans hu.1.le).trans (le_abs_self _)
  have hm : ‖vertical f b (-T) lo‖ ≤ K / (2 * Real.pi) := by
    apply (norm_vertical_le_const f b (-T) lo K ?_).trans
    · rw [show lo - -T = lo + T by ring]
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    · intro u hu
      apply hf
      have hmax : max (-T) lo ≤ -(T - 1) :=
        max_le (by linarith) (by linarith [(abs_le.mp hlo).2])
      exact (by linarith [hu.2.trans hmax] : T - 1 ≤ -u).trans (neg_le_abs _)
  rw [heq]
  calc
    _ ≤ ‖vertical f b T hi‖ + ‖vertical f b (-T) lo‖ := norm_sub_le _ _
    _ ≤ K / (2 * Real.pi) + K / (2 * Real.pi) := add_le_add hp hm
    _ = _ := by ring

theorem norm_height_shift_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {x y b T lo hi C : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hb : 1 < b) (hT : 1 < T)
    (hlo : |lo + T| ≤ 1) (hhi : |hi - T| ≤ 1)
    (hC : vonMangoldtLSeriesNormSum b ≤ C) :
    ‖vertical (centeredIntegrand chi x y) b lo hi -
      vertical (centeredIntegrand chi x y) b (-T) T‖ ≤ heightError x y b T C := by
  have hC0 : 0 ≤ C := (tsum_nonneg (fun _ => norm_nonneg _)).trans hC
  have h := norm_vertical_shift_le (centeredIntegrand chi x y)
    (continuous_centeredIntegrand chi hx hy hb)
    (show 0 ≤ C * (x ^ b + y ^ b) / (T - 1) by positivity) hlo hhi ?_
  · convert h using 1
    unfold heightError
    rw [div_div, mul_comm Real.pi]
  intro u hu
  have hr : ((b : ℂ) + u * Complex.I).re = b := by simp
  have hd : T - 1 ≤ ‖(b : ℂ) + u * Complex.I‖ :=
    hu.trans (by simpa using Complex.abs_im_le_norm ((b : ℂ) + u * Complex.I))
  have hp : ‖(x : ℂ) ^ ((b : ℂ) + u * Complex.I) -
      (y : ℂ) ^ ((b : ℂ) + u * Complex.I)‖ ≤ x ^ b + y ^ b := by
    simpa only [Complex.norm_cpow_eq_rpow_re_of_pos hx,
      Complex.norm_cpow_eq_rpow_re_of_pos hy, hr] using
      norm_sub_le ((x : ℂ) ^ ((b : ℂ) + u * Complex.I))
        ((y : ℂ) ^ ((b : ℂ) + u * Complex.I))
  have hl := norm_logDeriv_le_of_majorant chi (s := (b : ℂ) + u * Complex.I)
    (by simpa using hb) (by simpa using hC)
  rw [centeredIntegrand, norm_div, norm_mul]
  gcongr

theorem norm_endpoint_shift_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {t y b lo hi C : ℝ}
    (ht : 0 < t) (hy : 0 < y) (hb : 1 < b)
    (hC : vonMangoldtLSeriesNormSum b ≤ C) :
    ‖vertical (centeredIntegrand chi t y) b lo hi -
      vertical (centeredIntegrand chi (halfCutoff t) y) b lo hi‖ ≤
      endpointError t b lo hi C := by
  have hC0 : 0 ≤ C := (tsum_nonneg (fun _ => norm_nonneg _)).trans hC
  have heq : vertical (centeredIntegrand chi t y) b lo hi -
      vertical (centeredIntegrand chi (halfCutoff t) y) b lo hi =
      vertical (fun s => centeredIntegrand chi t y s -
        centeredIntegrand chi (halfCutoff t) y s) b lo hi := by
    unfold vertical
    rw [intervalIntegral.integral_sub
      ((continuous_centeredIntegrand chi ht hy hb).intervalIntegrable lo hi)
      ((continuous_centeredIntegrand chi (halfCutoff_pos t) hy hb).intervalIntegrable lo hi),
      mul_sub]
  rw [heq]
  apply norm_vertical_le_const
  intro u _
  have he : centeredIntegrand chi t y ((b : ℂ) + u * Complex.I) -
      centeredIntegrand chi (halfCutoff t) y ((b : ℂ) + u * Complex.I) =
      (-logDeriv chi.LFunction ((b : ℂ) + u * Complex.I)) *
        (((t : ℂ) ^ ((b : ℂ) + u * Complex.I) -
          (halfCutoff t : ℂ) ^ ((b : ℂ) + u * Complex.I)) /
            ((b : ℂ) + u * Complex.I)) := by
    unfold centeredIntegrand
    ring
  rw [he, norm_mul]
  have hl := norm_logDeriv_le_of_majorant chi (s := (b : ℂ) + u * Complex.I)
    (by simpa using hb) (by simpa using hC)
  calc
    _ ≤ C * ((max (halfCutoff t) t) ^ (b - 1) * |t - halfCutoff t|) :=
      mul_le_mul hl (norm_cpow_sub_div_le (halfCutoff_pos t) ht hb)
        (norm_nonneg _) hC0
    _ ≤ C * ((max (halfCutoff t) t) ^ (b - 1) * (1 / 2)) := by
      gcongr
      exact abs_sub_halfCutoff_le ht.le
    _ = _ := by ring

theorem norm_actual_perron_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {t b T lo hi C : ℝ}
    (ht : 0 < t) (hb : 1 < b) (hT : 1 < T)
    (hlo : |lo + T| ≤ 1) (hhi : |hi - T| ≤ 1)
    (hC : vonMangoldtLSeriesNormSum b ≤ C) :
    ‖vertical (centeredIntegrand chi t (5 / 2)) b lo hi - psi chi t‖ ≤
      actualError chi t b T lo hi C := by
  have hx := halfCutoff_pos t
  have hy : (0 : ℝ) < 5 / 2 := by norm_num
  have hp := norm_character_perron_le chi hx (halfInteger_ne_nat ⌊t⌋₊) hb
    (zero_lt_one.trans hT) hC
  have hp' := norm_character_perron_le chi hy
    (by intro n; convert halfInteger_ne_nat 2 n using 1; norm_num) hb
    (zero_lt_one.trans hT) hC
  have hs : ‖vertical (centeredIntegrand chi (halfCutoff t) (5 / 2)) b (-T) T -
      (psi chi t - psi chi (5 / 2))‖ ≤
      truncationError chi (halfCutoff t) b T C + truncationError chi (5 / 2) b T C := by
    rw [centered_vertical_eq_sub chi hx hy hb, ← psi_halfCutoff chi t]
    convert (norm_sub_le _ _).trans (add_le_add hp hp') using 1
    congr 1
    ring
  have hh := norm_height_shift_le chi hx hy hb hT hlo hhi hC
  have he := norm_endpoint_shift_le chi ht hy hb (lo := lo) (hi := hi) hC
  have hbase := norm_psi_two_half_le chi
  have hid :
      vertical (centeredIntegrand chi t (5 / 2)) b lo hi - psi chi t =
      ((vertical (centeredIntegrand chi t (5 / 2)) b lo hi -
        vertical (centeredIntegrand chi (halfCutoff t) (5 / 2)) b lo hi) +
      (vertical (centeredIntegrand chi (halfCutoff t) (5 / 2)) b lo hi -
        vertical (centeredIntegrand chi (halfCutoff t) (5 / 2)) b (-T) T)) +
      (vertical (centeredIntegrand chi (halfCutoff t) (5 / 2)) b (-T) T -
        (psi chi t - psi chi (5 / 2))) - psi chi (5 / 2) := by ring
  rw [hid]
  exact ((norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)).trans
      (by dsimp [actualError]; linarith)

theorem norm_actual_perron_le_strong {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {t b T lo hi : ℝ}
    (ht : 0 < t) (hb : 1 < b) (hb' : b ≤ 5 / 4) (hT : 1 < T)
    (hlo : |lo + T| ≤ 1) (hhi : |hi - T| ≤ 1) :
    ‖vertical (centeredIntegrand chi t (5 / 2)) b lo hi - psi chi t‖ ≤
      actualError chi t b T lo hi (seriesBound b) :=
  norm_actual_perron_le chi ht hb hT hlo hhi (mangoldt_normSum_le hb hb')

end LiuWang.Proof.PerronRecovery
