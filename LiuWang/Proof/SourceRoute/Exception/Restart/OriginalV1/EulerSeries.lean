import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.PrincipalIdentity

/-! The literal von Mangoldt series restricted by (n,q)>1 in LWD (2.5). -/

set_option autoImplicit false
noncomputable section

open Complex ArithmeticFunction
open scoped Classical LSeries.notation
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1

def excludedEulerTerm (q : ℕ) (sigma t : ℝ) (n : ℕ) : ℂ :=
  if 1 < Nat.gcd n q then LSeries.term (↗Λ) ((sigma : ℂ) + I * t) n else 0

theorem excludedEulerTerm_eq {q : ℕ} [NeZero q] (sigma t : ℝ) (n : ℕ) :
    excludedEulerTerm q sigma t n =
      LSeries.term (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) ((sigma : ℂ) + I * t) n -
        LSeries.term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) ((sigma : ℂ) + I * t) n := by
  by_cases hn : n = 0
  · simp [excludedEulerTerm, hn]
  have h1 : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply ((ZMod.isUnit_iff_coprime n 1).mpr (Nat.coprime_one_right n))
  by_cases hu : IsUnit (n : ZMod q)
  · have hc := (ZMod.isUnit_iff_coprime n q).mp hu
    simp [excludedEulerTerm, hc.gcd_eq_one, LSeries.term_of_ne_zero hn,
      Pi.mul_apply, h1, MulChar.one_apply hu]
  · have hg : 1 < Nat.gcd n q := by
      have hp := Nat.gcd_pos_of_pos_right n (NeZero.pos q)
      have hc : Nat.gcd n q ≠ 1 := fun he =>
        hu ((ZMod.isUnit_iff_coprime n q).mpr he)
      omega
    simp [excludedEulerTerm, hg, LSeries.term_of_ne_zero hn,
      Pi.mul_apply, h1, MulChar.map_nonunit (1 : DirichletCharacter ℂ q) hu]

theorem complexEuler_hasSum {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    HasSum (LSeries.term (↗chi * ↗Λ) ((sigma : ℂ) + I * t))
      (-logDeriv chi.LFunction ((sigma : ℂ) + I * t)) := by
  have hr : 1 < ((sigma : ℂ) + I * t).re := by simpa [mul_re] using hs
  simpa only [LSeriesHasSum, logDeriv, Pi.div_apply, ← neg_div,
    neg_logDeriv_LFunction_eq_twist_vonMangoldt _ hr] using
      (DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hr).LSeriesHasSum

theorem excludedEulerTerm_hasSum {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (t : ℝ) :
    HasSum (excludedEulerTerm q sigma t)
      (logDeriv (principalLevelCorrection q) ((sigma : ℂ) + I * t)) := by
  have hh := (complexEuler_hasSum (1 : DirichletCharacter ℂ 1) hs t).sub
    (complexEuler_hasSum (1 : DirichletCharacter ℂ q) hs t)
  simp only [DirichletCharacter.LFunction_modOne_eq] at hh
  rw [logDeriv_principal_eq_levelCorrection_add_riemannZeta
    (by simpa [mul_re] using hs)] at hh
  have he : -logDeriv riemannZeta ((sigma : ℂ) + I * t) -
      -(logDeriv (principalLevelCorrection q) ((sigma : ℂ) + I * t) +
        logDeriv riemannZeta ((sigma : ℂ) + I * t)) =
      logDeriv (principalLevelCorrection q) ((sigma : ℂ) + I * t) := by ring
  rw [he] at hh
  simpa only [← excludedEulerTerm_eq] using hh

def excludedDampedTerm (q : ℕ) (sigma t : ℝ) (n : ℕ) : ℂ :=
  excludedEulerTerm q sigma t n -
    (1 / (Real.sqrt 5 : ℂ)) * excludedEulerTerm q (stechkinSigma sigma) t n

theorem excludedDampedTerm_hasSum {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (t : ℝ) :
    HasSum (excludedDampedTerm q sigma t)
      (logDeriv (principalLevelCorrection q) ((sigma : ℂ) + I * t) -
        (1 / (Real.sqrt 5 : ℂ)) *
          logDeriv (principalLevelCorrection q) ((stechkinSigma sigma : ℂ) + I * t)) :=
  (excludedEulerTerm_hasSum hs t).sub
    ((excludedEulerTerm_hasSum (hs.trans_le (stechkinSigma_ge hs)) t).mul_left _)

theorem principalEulerDifference_eq_series {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (t : ℝ) :
    principalEulerDifference q sigma t = (∑' n, excludedDampedTerm q sigma t n).re := by
  rw [(excludedDampedTerm_hasSum hs t).tsum_eq]
  simp only [principalEulerDifference, stechkinK, ofReal_div, ofReal_one]

theorem l24_equation_25 {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (t : ℝ) :
    f (1 : DirichletCharacter ℂ q) sigma t =
      -(logDeriv riemannZeta ((sigma : ℂ) + I * t)).re +
        (1 / Real.sqrt 5) *
          (logDeriv riemannZeta ((stechkinSigma sigma : ℂ) + I * t)).re -
        (∑' n, excludedDampedTerm q sigma t n).re := by
  rw [l24_euler_identity hs, principalEulerDifference_eq_series hs]
  rfl

theorem excludedDampedSeries_norm_le {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (t : ℝ) :
    ‖∑' n, excludedDampedTerm q sigma t n‖ ≤ s q sigma := by
  rw [(excludedDampedTerm_hasSum hs t).tsum_eq, s_eq]
  simpa only [stechkinK, ofReal_div, ofReal_one] using
    LiuWang.Proof.ZeroRegionFamily.Sharp.norm_principal_level_difference_le q hs t

end LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
