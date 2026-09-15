import LiuWang.Proof.LocalAnalyticBounds.ClosedZeroWindow
import LiuWang.Proof.LocalAnalyticBounds.ReferenceBounds

/-!
# The numerical local-count budget in companion (4.3)

For primitive nonprincipal characters, the closed multiplicity-counted
window satisfies both source bounds at every `T >= 2000^15`. Instead of
importing Chen--Wang Lemma 8, we use the stronger kernel coefficient `5/2`
and the elementary reference-line estimates. This transports the coarser
additive budget seven into the exact source constants at its stated height.
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.LocalAnalyticBounds

theorem ncard_closedZeroWindow_le_explicit
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) (T : Real) :
    ((closedZeroWindow chi T).ncard : Real) ≤ (5 / 2 : Real) *
      (Real.log q / 2 + Real.log (|T| + 2) / 2 + 7) := by
  have hc := ncard_closedZeroWindow_le_gamma_zeta hchi hPrimitive T
  have hg := logDeriv_gammaFactor_re_le_on_two chi
    (s := referencePoint T) (by simp [referencePoint])
  have hz := norm_neg_logDeriv_zeta_two_le_six
  have him : (referencePoint T).im = T := by simp [referencePoint]
  rw [him] at hg
  linarith

private theorem forty_le_log_sourceHeight {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    40 ≤ Real.log T := by
  have hpow : (2 : Real) ^ (80 : Nat) ≤ T := (by norm_num : (2 : Real) ^ (80 : Nat) ≤
    (2000 : Real) ^ (15 : Nat)).trans hT
  have hl := Real.log_le_log (by positivity : (0 : Real) < 2 ^ (80 : Nat)) hpow
  rw [Real.log_pow] at hl
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
  norm_num at hl htwo
  linarith

theorem ncard_closedZeroWindow_source_bound
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ((closedZeroWindow chi T).ncard : Real) ≤
        3.5 * (0.5 * Real.log ((q : Real) * (T + 2)) + 0.59773) ∧
      ((closedZeroWindow chi T).ncard : Real) ≤
        1.7769 * Real.log ((q : Real) * T) - 1 := by
  have hqpos : (0 : Real) < q := by exact_mod_cast (by omega : 0 < q)
  have hqone : (1 : Real) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hTtwo : 2 ≤ T := (by norm_num : (2 : Real) ≤ 2000 ^ (15 : Nat)).trans hT
  have hTpos : 0 < T := by linarith
  have hlogq := Real.log_nonneg hqone
  have hlogT := forty_le_log_sourceHeight hT
  have hlogTle : Real.log T ≤ Real.log (T + 2) :=
    Real.log_le_log hTpos (by linarith)
  have hshift : Real.log (T + 2) ≤ Real.log T + 1 := by
    have hm := Real.log_le_log (by linarith : 0 < T + 2)
      (by linarith : T + 2 ≤ 2 * T)
    rw [Real.log_mul (by norm_num) hTpos.ne'] at hm
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith
  have hc := ncard_closedZeroWindow_le_explicit hchi hPrimitive T
  rw [abs_of_pos hTpos] at hc
  rw [Real.log_mul hqpos.ne' (by linarith : T + 2 ≠ 0),
    Real.log_mul hqpos.ne' hTpos.ne']
  constructor <;> linarith

end LiuWang.Proof.LocalAnalyticBounds
