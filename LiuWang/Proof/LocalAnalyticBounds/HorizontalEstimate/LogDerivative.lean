import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.GammaBounds
import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.CompensatedSum
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorNearOriginDifferentiability

/-!
# 所选水平线上的真实对数导数生产者

在完整实部区间 `[-1/2, 2]` 上给出有效常数。左半条带非零性由已证
平凡零点结构和函数方程桥导出。归一化与 Hadamard 常数在两点相减
恒等式中精确消去，不作为新假设。
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate

theorem LFunction_ne_zero_on_separated_strip
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {H B : Real} (hB : 0 < B) (hH : H ≠ 0)
    (hsep : ∀ p : CompletedZeroIndex chi, B⁻¹ ≤ |(completedZeroValue p).im - H|)
    {s : Complex} (him : s.im = H) (hlo : -(1 : Real) / 2 ≤ s.re) :
    chi.LFunction s ≠ 0 := by
  apply LFunction_ne_zero_of_completedZero_ordinate_avoidance
    hchi hPrimitive him hlo hH
  intro p hp
  have h := hsep p
  rw [hp, sub_self, abs_zero] at h
  exact (not_le_of_gt (inv_pos.mpr hB)) h

theorem norm_logDeriv_separated_strip_explicit
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {H B d : Real} (hB : 0 < B) (hH : 2 ≤ |H|)
    (hsep : ∀ p : CompletedZeroIndex chi, B⁻¹ ≤ |(completedZeroValue p).im - H|)
    {s : Complex} (him : s.im = H)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 5 / 2)
    (hlo : 2 - d ≤ s.re) (hhi : s.re ≤ 2) :
    ‖logDeriv chi.LFunction s‖ ≤
      24 + 8 * Real.log (|H| + 2) +
        (d + d ^ 2 * B) *
          (Real.log q / 2 + Real.log (|H| + 2) / 2 + 7) := by
  have hH0 : H ≠ 0 := by intro h; norm_num [h] at hH
  have hslo : -(1 : Real) / 2 ≤ s.re := by linarith
  have hn := LFunction_ne_zero_on_separated_strip hchi hPrimitive hB hH0 hsep him hslo
  have hs0 : s ≠ 0 := by
    intro h
    apply hH0
    simpa [h] using him.symm
  have hs : -1 < s.re := by linarith
  have hg0 := DirichletCharacter.gammaFactor_ne_zero_of_neg_one_lt_re_of_ne_zero
    chi hs hs0
  have hgd := DirichletCharacter.differentiableAt_gammaFactor_of_neg_one_lt_re_of_ne_zero
    chi hs hs0
  have he := logDeriv_LFunction_eq_reference_add_zero_difference
    hchi hPrimitive hn hg0 hgd H
  change logDeriv chi.LFunction s =
    logDeriv chi.LFunction (referencePoint H) - logDeriv chi.gammaFactor s +
      logDeriv chi.gammaFactor (referencePoint H) +
        ∑' p : CompletedZeroIndex chi,
          (1 / (s - completedZeroValue p) -
            1 / (referencePoint H - completedZeroValue p)) at he
  have hl : ‖logDeriv chi.LFunction (referencePoint H)‖ ≤ 6 := by
    apply le_trans _ norm_neg_logDeriv_zeta_two_le_six
    have h := norm_neg_logDeriv_LFunction_le_zeta_re chi
      (s := referencePoint H) (by norm_num [referencePoint])
    simpa [logDeriv_apply, referencePoint, norm_div, norm_neg] using h
  have hgs := norm_logDeriv_gammaFactor_horizontal_explicit chi hslo hhi
    (by simpa [him] using hH)
  rw [him] at hgs
  have hgw := norm_logDeriv_gammaFactor_horizontal_explicit chi
    (s := referencePoint H) (by norm_num [referencePoint])
    (by norm_num [referencePoint]) (by simpa [referencePoint] using hH)
  rw [show (referencePoint H).im = H by simp [referencePoint]] at hgw
  have hz := norm_tsum_reciprocal_difference_le hchi hPrimitive hB hsep him hd0 hlo hhi
  rw [he]
  calc
    _ ≤ (‖logDeriv chi.LFunction (referencePoint H)‖ + ‖logDeriv chi.gammaFactor s‖) +
        ‖logDeriv chi.gammaFactor (referencePoint H)‖ +
        ‖∑' p : CompletedZeroIndex chi,
          (1 / (s - completedZeroValue p) -
            1 / (referencePoint H - completedZeroValue p))‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl) |>.trans
          (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl)
    _ ≤ _ := by linarith

theorem source_log_ge_forty {q : Nat} (hq : 3 ≤ q)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    40 ≤ Real.log ((q : Real) * T) := by
  have hpow : (2 : Real) ^ (80 : Nat) ≤ T :=
    (by norm_num : (2 : Real) ^ (80 : Nat) ≤ 2000 ^ (15 : Nat)).trans hT
  have hT0 : 0 < T := (by positivity : (0 : Real) < 2 ^ (80 : Nat)).trans_le hpow
  have hq1 : (1 : Real) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hl := Real.log_le_log (by positivity : (0 : Real) < 2 ^ (80 : Nat)) hpow
  rw [Real.log_pow] at hl
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
  norm_num at hl htwo
  have hm := Real.log_le_log hT0 (le_mul_of_one_le_left hT0.le hq1)
  linarith

theorem source_height_abs_bounds {T H : Real}
    (hT : (2000 : Real) ^ (15 : Nat) ≤ T)
    (hH : |(|H|) - T| ≤ 1) :
    2 ≤ |H| ∧ |H| ≤ T + 1 ∧ T / 2 ≤ |H| := by
  have ht : 4 ≤ T := (by norm_num : (4 : Real) ≤ 2000 ^ (15 : Nat)).trans hT
  rcases abs_le.mp hH with ⟨hl, hu⟩
  exact ⟨by linarith, by linarith, by linarith⟩

theorem norm_logDeriv_source_height_polynomial_le
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T H d : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T)
    (hH : |(|H|) - T| ≤ 1)
    (hsep : ∀ p : CompletedZeroIndex chi,
      (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |(completedZeroValue p).im - H|)
    {s : Complex} (him : s.im = H)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 5 / 2) (hlo : 2 - d ≤ s.re) (hhi : s.re ≤ 2) :
    ‖logDeriv chi.LFunction s‖ ≤
      24 + 8 * (Real.log ((q : Real) * T) + 1) +
        (d + d ^ 2 * (1.7769 * Real.log ((q : Real) * T))) *
          (Real.log ((q : Real) * T) / 2 + 15 / 2) := by
  have hB := source_height_budget_pos hq hT
  have habs := source_height_abs_bounds hT hH
  have h := norm_logDeriv_separated_strip_explicit hchi hPrimitive hB habs.1
    hsep him hd0 hd1 hlo hhi
  have ht : 3 ≤ T := (by norm_num : (3 : Real) ≤ 2000 ^ (15 : Nat)).trans hT
  have ht0 : 0 < T := by linarith
  have hq0 : (0 : Real) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : Real) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hqlog := Real.log_nonneg hq1
  have hshift : Real.log (|H| + 2) ≤ Real.log T + 1 := by
    have hl := Real.log_le_log (by positivity : 0 < |H| + 2)
      (by linarith [habs.2.1] : |H| + 2 ≤ 2 * T)
    rw [Real.log_mul (by norm_num) ht0.ne'] at hl
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith
  have heq := Real.log_mul hq0.ne' ht0.ne'
  have hcoeff : 0 ≤ d + d ^ 2 * (1.7769 * Real.log ((q : Real) * T)) := by positivity
  apply h.trans
  apply add_le_add
  · have hl : Real.log (|H| + 2) ≤ Real.log ((q : Real) * T) + 1 := by linarith
    linarith
  · apply mul_le_mul_of_nonneg_left _ hcoeff
    linarith

theorem norm_logDeriv_source_height_le
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T H : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T)
    (hH : |(|H|) - T| ≤ 1)
    (hsep : ∀ p : CompletedZeroIndex chi,
      (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |(completedZeroValue p).im - H|)
    {s : Complex} (him : s.im = H)
    (hlo : -(1 : Real) / 2 ≤ s.re) (hhi : s.re ≤ 2) :
    ‖logDeriv chi.LFunction s‖ ≤ 10 * (Real.log ((q : Real) * T)) ^ 2 := by
  have h := norm_logDeriv_source_height_polynomial_le hq hchi hPrimitive hT hH hsep
    him (d := 5 / 2) (by norm_num) le_rfl (by linarith) hhi
  have hlog := source_log_ge_forty hq hT
  have hsquare : 40 * Real.log ((q : Real) * T) ≤
      (Real.log ((q : Real) * T)) ^ 2 := by nlinarith
  nlinarith

theorem norm_logDeriv_source_height_right_le
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T H : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T)
    (hH : |(|H|) - T| ≤ 1)
    (hsep : ∀ p : CompletedZeroIndex chi,
      (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |(completedZeroValue p).im - H|)
    {s : Complex} (him : s.im = H)
    (hlo : (3 : Real) / 4 ≤ s.re) (hhi : s.re ≤ 2) :
    ‖logDeriv chi.LFunction s‖ ≤ (5 / 2 : Real) * (Real.log ((q : Real) * T)) ^ 2 := by
  have h := norm_logDeriv_source_height_polynomial_le hq hchi hPrimitive hT hH hsep
    him (d := 5 / 4) (by norm_num) (by norm_num) (by linarith) hhi
  have hlog := source_log_ge_forty hq hT
  have hsquare : 40 * Real.log ((q : Real) * T) ≤
      (Real.log ((q : Real) * T)) ^ 2 := by nlinarith
  nlinarith

end LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate
