import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.SmallHeightIntegral

/-! # Exact same-q logarithmic normalization of the actual (2.25) bound -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart

def source25LogKernel (L q s : ℝ) : ℝ :=
  (s / Real.pi - 0.874 + q * (6.8423 * s + 15) * Real.exp (-s)) *
    (Real.exp (-0.478 * L / s) - Real.exp (-L / 20))

theorem source25LogKernel_continuousOn (L q : ℝ) :
    ContinuousOn (source25LogKernel L q) (Set.Ioi 0) := by
  have hs : ∀ s ∈ Set.Ioi (0 : ℝ), s ≠ 0 := fun s hs => ne_of_gt hs
  unfold source25LogKernel
  fun_prop

theorem source25_log_substitution {N q : ℕ} [NeZero q] {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hqu : 1 < (q : ℝ) * u) :
    (∫ y in u..v, heightKernel y * ((q.totient : ℝ) * source25Bound q y) *
      (Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) -
        Real.exp (-sourceL N / 20))) =
      (q.totient : ℝ) * ∫ s in Real.log ((q : ℝ) * u)..Real.log ((q : ℝ) * v),
        source25LogKernel (sourceL N) q s := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hy0 (y : ℝ) (hy : y ∈ Set.uIcc u v) : 0 < y := by
    rw [Set.uIcc_of_le huv] at hy
    exact hu.trans_le hy.1
  have hd (y : ℝ) (hy : y ∈ Set.uIcc u v) :
      HasDerivAt (fun y => Real.log ((q : ℝ) * y)) (1 / y) y := by
    have hh := ((hasDerivAt_id y).const_mul (q : ℝ)).log (mul_pos hq (hy0 y hy)).ne'
    simp only [id_eq, mul_one] at hh
    convert! hh using 1
    field_simp
  have hc : ContinuousOn (source25LogKernel (sourceL N) q)
      ((fun y => Real.log ((q : ℝ) * y)) '' Set.uIcc u v) := by
    apply (source25LogKernel_continuousOn _ _).mono
    rintro s ⟨y, hy, rfl⟩
    rw [Set.uIcc_of_le huv] at hy
    exact Real.log_pos (hqu.trans_le (mul_le_mul_of_nonneg_left hy.1 hq.le))
  have hi := intervalIntegral.integral_comp_mul_deriv' hd
    (continuousOn_const.div continuousOn_id (fun y hy => (hy0 y hy).ne')) hc
  rw [← hi, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  have hy' : y ≠ 0 := (hy0 y hy).ne'
  dsimp only [Function.comp_def]
  unfold heightKernel source25Bound source25LogKernel
  rw [Real.exp_neg (Real.log ((q : ℝ) * y)), Real.exp_log (mul_pos hq (hy0 y hy))]
  field_simp [hy']
  ring

theorem actual_smallAlpha_log_signed {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {v : ℝ} (huv : omegaCutoff N q ≤ v) (hvT : v ≤ sourceT N) :
    (∫ y in omegaCutoff N q..v, heightKernel y *
      ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
        layerKernel N alpha * (familyCount q alpha y : ℝ)) ≤
      (q.totient : ℝ) *
        ∫ s in Real.log (3.36 * sourceP N)..Real.log ((q : ℝ) * v),
          source25LogKernel (sourceL N) q s := by
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have hp := original_product_ge hN (q := q) le_rfl
  have h := actual_source25_outer_signed hN hq huv hvT
  rw [source25_log_substitution hu huv (by linarith),
    (original_log_height_bounds hN hq).1] at h
  exact h

theorem small_height_log_upper {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y)
    (hyq : y ≤ max (100000 / (q : ℝ)) (10000 * Real.log q)) :
    Real.log ((q : ℝ) * y) ≤
      Real.log (10000 * sourceL N ^ (3 : ℕ) * Real.log (sourceL N ^ (3 : ℕ))) := by
  have hg := small_height_gate hN hy hyq
  rw [hg.2] at hyq
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hp := original_product_ge hN hy
  have hq1 : 1 ≤ q := NeZero.pos q
  have hlog0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
  have hlog := Real.log_le_log hq0 hq
  have hm := mul_le_mul hq hlog hlog0 (by
    unfold sourceP
    have hL := Parameters.sourceL_ge_3100 hN
    positivity)
  apply Real.log_le_log (by linarith)
  have hh := mul_le_mul_of_nonneg_left hyq hq0.le
  change (q : ℝ) * Real.log q ≤ sourceL N ^ (3 : ℕ) *
    Real.log (sourceL N ^ (3 : ℕ)) at hm
  nlinarith

theorem source25_log_coefficient_identity (q phi s : ℝ) (hq : q ≠ 0) :
    phi / q * (s / Real.pi - 0.874 + q * (6.8423 * s + 15) * Real.exp (-s)) =
      phi / q * (s / Real.pi - 0.874) +
        phi * (6.8423 * s + 15) * Real.exp (-s) := by
  field_simp

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
