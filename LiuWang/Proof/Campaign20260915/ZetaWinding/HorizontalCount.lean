import LiuWang.Proof.Campaign20260915.ZetaWinding.LocalLog
import LiuWang.Proof.Campaign20260915.ZetaValidation.CompleteSixteen

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.DirichletZeroCount

def horizontalAt (H x : ℝ) : ℂ := (x : ℂ) + (H : ℂ) * I

def horizontalPrimitiveSum (H : ℝ) (x : ℕ → ℝ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n,
    (localXiPrimitive (c j) (horizontalAt H (x (j + 1))) -
      localXiPrimitive (c j) (horizontalAt H (x j)))

theorem horizontal_ball_of_endpoint_deriv {H a b L e : ℝ} {z : ℂ}
    (hH : 0 < H) (hL : 0 ≤ L)
    (he : ‖riemannZeta (horizontalAt H a) - z‖ ≤ e)
    (hd : ∀ t ∈ Set.Icc a b, ‖deriv riemannZeta (horizontalAt H t)‖ ≤ L) :
    ∀ t ∈ Set.Icc a b, ‖riemannZeta (horizontalAt H t) - z‖ ≤ e + L * (b - a) := by
  have hder (t : ℝ) :
      HasDerivAt (fun u : ℝ => riemannZeta (horizontalAt H u))
        (deriv riemannZeta (horizontalAt H t)) t := by
    have hs1 : horizontalAt H t ≠ 1 := by
      intro hh
      have hi := congrArg Complex.im hh
      simp only [horizontalAt, add_im, ofReal_im, mul_im, ofReal_re,
        I_im, I_re, mul_one, mul_zero, add_zero, zero_add, one_im] at hi
      linarith
    simpa [horizontalAt, Function.comp_def, smul_eq_mul] using
      (differentiableAt_riemannZeta hs1).hasDerivAt.scomp t
        ((Complex.ofRealCLM.hasDerivAt (x := t)).add_const ((H : ℂ) * I))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t (_ : t ∈ Set.Icc a b) => (hder t).hasDerivWithinAt)
    (fun t (ht : t ∈ Set.Ico a b) => hd t ⟨ht.1, ht.2.le⟩)
  intro t ht
  have hn := norm_add_le
    (riemannZeta (horizontalAt H t) - riemannZeta (horizontalAt H a))
    (riemannZeta (horizontalAt H a) - z)
  rw [sub_add_sub_cancel] at hn
  have hb := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hL
  linarith [hm t ht]

theorem horizontal_rotated_pos_of_endpoint_deriv {H a b L e : ℝ} {z c : ℂ}
    (hH : 0 < H) (hL : 0 ≤ L)
    (he : ‖riemannZeta (horizontalAt H a) - z‖ ≤ e)
    (hd : ∀ t ∈ Set.Icc a b, ‖deriv riemannZeta (horizontalAt H t)‖ ≤ L)
    (hm : ‖c‖ * (e + L * (b - a)) < (c * z).re) :
    ∀ t ∈ Set.Icc a b, 0 < (c * riemannZeta (horizontalAt H t)).re := by
  intro t ht
  exact rotated_re_pos_of_ball (horizontal_ball_of_endpoint_deriv hH hL he hd t ht) hm

theorem partition_covers (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.uIcc (x 0) (x n)) :
    ∃ j < n, t ∈ Set.uIcc (x j) (x (j + 1)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0, by omega, ht⟩
    · have hh : t ∈ Set.uIcc (x 0) (x n) ∪ Set.uIcc (x n) (x (n + 1)) :=
        Set.uIcc_subset_uIcc_union_uIcc ht
      rcases hh with hh | hh
      · obtain ⟨j, hj, htj⟩ := ih (by omega) hh
        exact ⟨j, by omega, htj⟩
      · exact ⟨n, by omega, hh⟩

theorem horizontalPrimitiveSum_integer (H : ℝ) (x : ℕ → ℝ) (c : ℕ → ℂ) (n : ℕ)
    (hr : ∀ j < n,
      0 < (c j * riemannZeta (horizontalAt H (x j))).re ∧
      0 < (c j * riemannZeta (horizontalAt H (x (j + 1)))).re) :
    ∃ k : ℤ, horizontalPrimitiveSum H x c n =
      xiCountingPrimitive (horizontalAt H (x n)) -
        xiCountingPrimitive (horizontalAt H (x 0)) +
          (k : ℂ) * (2 * Real.pi * I) := by
  induction n with
  | zero => exact ⟨0, by simp [horizontalPrimitiveSum]⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih (fun j hj => hr j (by omega))
    have hn := hr n (by omega)
    obtain ⟨l, hl⟩ := localXiPrimitive_increment_integer
      (left_ne_zero_of_mul (ne_zero_of_re_pos hn.1))
      (right_ne_zero_of_mul (ne_zero_of_re_pos hn.1))
      (right_ne_zero_of_mul (ne_zero_of_re_pos hn.2))
    refine ⟨k + l, ?_⟩
    simp only [horizontalPrimitiveSum, Finset.sum_range_succ] at hk ⊢
    rw [hk, hl]
    push_cast
    ring

theorem horizontal_integral_eq_sum {H : ℝ} (hH : 0 < H)
    (x : ℕ → ℝ) (c : ℕ → ℂ) (n : ℕ)
    (hx0 : x 0 = 1 / 2) (hxn : x n = 2)
    (hs : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)), 1 / 2 ≤ t)
    (hr : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)),
      0 < (c j * riemannZeta (horizontalAt H t)).re) :
    HIntegral (logDeriv riemannXi) (1 / 2) 2 H = horizontalPrimitiveSum H x c n := by
  have hz (j : ℕ) (hj : j < n) :
      ∀ t ∈ Set.uIcc (x j) (x (j + 1)),
        riemannXi (horizontalAt H t) ≠ 0 := by
    intro t ht hzero
    have h1 : horizontalAt H t ≠ 1 := by
      intro he
      have hi := congrArg Complex.im he
      simp [horizontalAt] at hi
      linarith
    have he := (LiuWang.Proof.PrincipalPsi.Quantitative.xi_zero_iff_zeta_zero
      (by simpa [horizontalAt] using (show -2 < t by linarith [hs j hj t ht])) h1).mp hzero
    simpa [he] using hr j hj t ht
  have hi (j : ℕ) (hj : j < n) :
      IntervalIntegrable (fun t => logDeriv riemannXi (horizontalAt H t))
        volume (x j) (x (j + 1)) := by
    simpa [horizontalAt, add_comm] using xi_line_integrable
      (a := x j) (b := x (j + 1)) ((H : ℂ) * I) 1
      (by simpa [horizontalAt, add_comm] using hz j hj)
  have he (j : ℕ) (hj : j < n) :
      (∫ t in x j..x (j + 1), logDeriv riemannXi (horizontalAt H t)) =
        localXiPrimitive (c j) (horizontalAt H (x (j + 1))) -
          localXiPrimitive (c j) (horizontalAt H (x j)) := by
    have hp := localXiPrimitive_line_integral
      (a := x j) (b := x (j + 1)) (z := (H : ℂ) * I) (v := 1) (c := c j)
      (by intro t ht; simpa using (show 0 < t by linarith [hs j hj t ht]))
      (by
        intro t _
        apply mem_slitPlane_iff.mpr
        right
        simpa using hH.ne')
      (by simpa [horizontalAt, add_comm] using hr j hj)
    simpa [horizontalAt, add_comm] using hp
  have hadd := intervalIntegral.sum_integral_adjacent_intervals hi
  rw [hx0, hxn] at hadd
  change (∫ t in (1 / 2 : ℝ)..2, logDeriv riemannXi (horizontalAt H t)) = _
  rw [← hadd]
  exact Finset.sum_congr rfl (fun j hj => he j (Finset.mem_range.mp hj))

theorem zeta_height_nonzero_of_rotated_segments {H : ℝ} (hH : 0 < H)
    (x : ℕ → ℝ) (c : ℕ → ℂ) (n : ℕ)
    (hx0 : x 0 = 1 / 2) (hxn : x n = 2)
    (hr : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)),
      0 < (c j * riemannZeta (horizontalAt H t)).re) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = H → riemannZeta s ≠ 0 := by
  have hn : 0 < n := by
    by_contra hh
    have : n = 0 := by omega
    subst n
    linarith
  have hright {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 2)
      (ht : |s.im| = H) : riemannZeta s ≠ 0 := by
    have ht' : s.re ∈ Set.uIcc (x 0) (x n) := by
      rw [hx0, hxn, Set.uIcc_of_le (by norm_num)]
      exact ⟨hs, hs2⟩
    obtain ⟨j, hj, htj⟩ := partition_covers x hn ht'
    have hne := right_ne_zero_of_mul (ne_zero_of_re_pos (hr j hj s.re htj))
    rcases (abs_eq hH.le).mp ht with ht | ht
    · have he : s = horizontalAt H s.re := by
        apply Complex.ext <;> simp [horizontalAt, ht]
      rwa [he]
    · have he : conj s = horizontalAt H s.re := by
        apply Complex.ext <;> simp [horizontalAt, ht]
      rw [← he, riemannZeta_conj] at hne
      exact fun hz => hne (by simp [hz])
  intro s h0 h1 ht
  by_cases hs : 1 / 2 ≤ s.re
  · exact hright hs (by linarith) ht
  · intro hz
    have hs0 : s ≠ 0 := ne_zero_of_re_pos h0
    have hs1 : s ≠ 1 := by intro he; simp [he] at h1
    have hx := (LiuWang.Proof.PrincipalPsi.Quantitative.xi_zero_iff_zeta_zero
      (by linarith : -2 < s.re) hs1).mpr hz
    have hy : riemannXi (1 - s) = 0 := by rwa [riemannXi_one_sub]
    have hy1 : 1 - s ≠ 1 := by intro he; apply hs0; linear_combination -he
    have hyz := (LiuWang.Proof.PrincipalPsi.Quantitative.xi_zero_iff_zeta_zero
      (s := 1 - s) (by simp only [sub_re, one_re]; linarith) hy1).mp hy
    exact hright
      (s := 1 - s) (by simp only [sub_re, one_re]; linarith)
      (by simp only [sub_re, one_re]; linarith) (by simpa using ht) hyz

theorem xi_right_vertical_primitive_all (H : ℝ) :
    VIntegral (logDeriv riemannXi) 2 0 H =
      xiCountingPrimitive (horizontalAt H 2) - xiCountingPrimitive 2 := by
  have hd (t : ℝ) :
      HasDerivAt (fun u : ℝ => xiCountingPrimitive (2 + (u : ℂ) * I))
        (I * logDeriv riemannXi (2 + (t : ℂ) * I)) t := by
    have hz := Remainder.LFunction_re_pos
      (1 : LiuWang.Proof.Interfaces.Character 1)
      (s := 2 + (t : ℂ) * I) (by norm_num)
    rw [DirichletCharacter.LFunction_modOne_eq] at hz
    have h := xiCountingPrimitive_hasDerivAt (s := 2 + (t : ℂ) * I)
      (by norm_num) (mem_slitPlane_iff.mpr (Or.inl (by norm_num))) hz
    simpa only [Argument.linePoint, Function.comp_def, smul_eq_mul] using
      h.scomp t (Argument.line_hasDerivAt 2 I t)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (Remainder.xi_vertical_integrable H)
  rw [intervalIntegral.integral_const_mul] at he
  simpa [VIntegral, horizontalAt, smul_eq_mul] using he

theorem zetaClosedCount_eq_segment_sum {H : ℝ} (hH : 0 < H)
    (x : ℕ → ℝ) (c : ℕ → ℂ) (n : ℕ)
    (hx0 : x 0 = 1 / 2) (hxn : x n = 2)
    (hs : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)), 1 / 2 ≤ t)
    (hr : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)),
      0 < (c j * riemannZeta (horizontalAt H t)).re) :
    (zetaClosedCount H : ℝ) =
      2 * (xiCountingPrimitive (horizontalAt H 2) -
        xiCountingPrimitive 2 - horizontalPrimitiveSum H x c n).im / Real.pi := by
  rw [zetaClosedCount_eq_principal, Argument.principal_count_eq_upper_im 1
    (b := 2) (by norm_num) hH.le
    (by simpa only [DirichletCharacter.LFunction_modOne_eq] using
      zeta_height_nonzero_of_rotated_segments hH x c n hx0 hxn hr)]
  rw [Argument.upperRightIntegral, xi_right_vertical_primitive_all,
    horizontal_integral_eq_sum hH x c n hx0 hxn hs hr]

theorem zetaClosedCount_eq_winding {H : ℝ} (hH : 0 < H)
    (x : ℕ → ℝ) (c : ℕ → ℂ) (n : ℕ)
    (hx0 : x 0 = 1 / 2) (hxn : x n = 2)
    (hs : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)), 1 / 2 ≤ t)
    (hr : ∀ j < n, ∀ t ∈ Set.uIcc (x j) (x (j + 1)),
      0 < (c j * riemannZeta (horizontalAt H t)).re) :
    ∃ k : ℤ,
      horizontalPrimitiveSum H x c n =
        xiCountingPrimitive (horizontalAt H 2) -
          xiCountingPrimitive (horizontalAt H (1 / 2)) +
            (k : ℂ) * (2 * Real.pi * I) ∧
      (zetaClosedCount H : ℝ) =
        2 * (xiCountingPrimitive (horizontalAt H (1 / 2))).im / Real.pi -
          4 * (k : ℝ) := by
  obtain ⟨k, hk⟩ := horizontalPrimitiveSum_integer H x c n
    (fun j hj => ⟨hr j hj _ Set.left_mem_uIcc, hr j hj _ Set.right_mem_uIcc⟩)
  rw [hx0, hxn] at hk
  refine ⟨k, hk, ?_⟩
  rw [zetaClosedCount_eq_segment_sum hH x c n hx0 hxn hs hr, hk]
  simp [sub_im, add_im, xiCountingPrimitive_two_im, mul_im, mul_re]
  field_simp
  ring

#print axioms horizontal_ball_of_endpoint_deriv
#print axioms horizontalPrimitiveSum_integer
#print axioms zeta_height_nonzero_of_rotated_segments
#print axioms zetaClosedCount_eq_segment_sum
#print axioms zetaClosedCount_eq_winding

end LiuWang.Proof.Campaign20260915.ZetaWinding
