import LiuWang.Proof.LocalAnalyticBounds.ReferenceBounds
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeRightHalfPlaneBound

/-! # 实部三半的实际 Dirichlet 级数数值界 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.LocalAnalyticBounds.LeftVertical

theorem norm_neg_logDeriv_zeta_three_halves_le_twenty :
    ‖-deriv riemannZeta ((3 : Complex) / 2) / riemannZeta ((3 : Complex) / 2)‖ ≤ 20 := by
  have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (3 : Complex) / 2) (by norm_num)
  have hid := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (3 : Complex) / 2) (by norm_num)
  have hp : Summable (fun n : Nat => (n : Real) ^ (-(5 / 4 : Real))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hterm : ∀ n : Nat,
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : Complex))
        ((3 : Complex) / 2) n‖ ≤ 4 * (n : Real) ^ (-(5 / 4 : Real)) := by
    intro n
    have heq := BombieriVinogradov.SiegelWalfisz.norm_LSeriesTerm_vonMangoldt_eq
      (c := 3 / 2) n
    norm_num at heq
    rw [heq]
    by_cases hn : n = 0
    · subst n
      norm_num
    have hnpos : (0 : Real) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hlog := Real.log_natCast_le_rpow_div n (by norm_num : (0 : Real) < 1 / 4)
    have hlam : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
      ArithmeticFunction.vonMangoldt_le_log
    calc
      ArithmeticFunction.vonMangoldt n / (n : Real) ^ (3 / 2 : Real) ≤
          ((n : Real) ^ (1 / 4 : Real) / (1 / 4)) / (n : Real) ^ (3 / 2 : Real) :=
        div_le_div_of_nonneg_right (hlam.trans hlog) (by positivity)
      _ = 4 * (n : Real) ^ (-(5 / 4 : Real)) := by
        calc
          _ = 4 * ((n : Real) ^ (1 / 4 : Real) / (n : Real) ^ (3 / 2 : Real)) := by ring
          _ = _ := by rw [← Real.rpow_sub hnpos]; norm_num
  rw [← hid]
  change ‖∑' n, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : Complex))
    ((3 : Complex) / 2) n‖ ≤ 20
  calc
    _ ≤ ∑' n, ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : Complex))
        ((3 : Complex) / 2) n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : Nat, 4 * (n : Real) ^ (-(5 / 4 : Real)) :=
      hs.norm.tsum_le_tsum hterm (hp.mul_left 4)
    _ = 4 * ∑' n : Nat, (n : Real) ^ (-(5 / 4 : Real)) := tsum_mul_left
    _ ≤ 20 := by
      have h := AnalyticNumberTheory.LargeSieve.tsum_nat_rpow_neg_le
        (5 / 4 : Real) (by norm_num)
      norm_num at h
      linarith

theorem norm_logDeriv_LFunction_three_halves_le_twenty
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q) {s : Complex}
    (hs : s.re = (3 : Real) / 2) :
    ‖logDeriv chi.LFunction s‖ ≤ 20 := by
  have h := BombieriVinogradov.SiegelWalfisz.norm_neg_logDeriv_LFunction_le_zeta_re
    chi (show 1 < s.re by linarith)
  rw [hs] at h
  have he : ((3 / 2 : Real) : Complex) = (3 : Complex) / 2 := by norm_num
  rw [he] at h
  simpa [logDeriv_apply] using h.trans norm_neg_logDeriv_zeta_three_halves_le_twenty

end LiuWang.Proof.LocalAnalyticBounds.LeftVertical
