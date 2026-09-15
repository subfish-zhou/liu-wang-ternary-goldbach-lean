import LiuWang.Proof.PerronBudget.StrongConsumer
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ChebyshevCorrection

/-!
# 非主字符的导子源域与真实 psi 诱导误差

始终使用原 N、原实端点 t 和原 T。自然前缀仅用于调用既有 Euler 修正界。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.NonprincipalPsi

theorem conductor_source_domain {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hqUpper : (q : ℝ) ≤ sourceP1 N) :
    3 ≤ chi.conductor ∧ (chi.conductor : ℝ) ≤ sourceP1 N ∧
      chi.primitiveCharacter ≠ 1 ∧ chi.primitiveCharacter.IsPrimitive := by
  refine ⟨BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hchi,
    ?_, BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one
      chi hchi, chi.primitiveCharacter_isPrimitive⟩
  exact (Nat.cast_le.mpr
    (BombieriVinogradov.DirichletCharacter.conductor_le_level chi)).trans hqUpper

theorem norm_psi_sub_primitive_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {t : ℝ} (ht : 1 ≤ t) :
    ‖ExplicitPerron.psi chi t - ExplicitPerron.psi chi.primitiveCharacter t‖ ≤
      Real.log q * Real.log t / Real.log 2 := by
  have hx : 0 < ⌊t⌋₊ := Nat.floor_pos.mpr ht
  have hxR : (0 : ℝ) < (⌊t⌋₊ : ℝ) := by exact_mod_cast hx
  have hqlog : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ q))
  exact (norm_characterChebyshevSum_sub_primitive_le (NeZero.ne q) chi hx).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.log_le_log hxR (Nat.floor_le (by linarith))) hqlog)
      (by linarith [PerronBudget.log_two_bounds.1]))

theorem induction_cost_source_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) {t : ℝ}
    (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    Real.log q * Real.log t / Real.log 2 ≤
      0.000001 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  have hL0 := sourceL_pos hN
  have hT0 := sourceT_pos hN
  have htbig := (PerronBudget.source_cutoff_bounds hN htlo hthi).1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have hqlog0 : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ q))
  have htlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have htlog : Real.log t ≤ sourceL N :=
    Real.log_le_log (by linarith) hthi
  have hqlog : Real.log q ≤ 6 * sourceL N := by
    have hh := Real.log_le_log hq0 hqUpper
    change Real.log q ≤ Real.log (sourceL N ^ (6 : ℕ)) at hh
    rw [Real.log_pow] at hh
    have hlog := Real.log_le_sub_one_of_pos hL0
    norm_num at hh
    linarith
  have hcoarse : Real.log q * Real.log t / Real.log 2 ≤
      12 * sourceL N ^ (2 : ℕ) := by
    apply (div_le_iff₀ (by linarith [PerronBudget.log_two_bounds.1] :
      0 < Real.log 2)).mpr
    have hmul := mul_le_mul hqlog htlog htlog0 (by positivity : 0 ≤ 6 * sourceL N)
    have htwo := mul_le_mul_of_nonneg_left PerronBudget.log_two_bounds.1
      (show 0 ≤ 12 * sourceL N ^ (2 : ℕ) by positivity)
    nlinarith
  have hT12 : 12 ≤ sourceT N :=
    (by norm_num : (12 : ℝ) ≤ 2000 ^ (15 : ℕ)).trans
      (NonSymmetricContour.sourceT_large hN)
  have hpay : 12 ≤ 0.000001 * t / sourceT N := by
    apply (le_div_iff₀ hT0).mpr
    have hh := PerronBudget.million_sourceT_sq_le_endpoint hN htlo
    nlinarith
  exact hcoarse.trans (mul_le_mul_of_nonneg_right hpay (sq_nonneg _))

theorem norm_psi_sub_primitive_source_le {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) {t : ℝ}
    (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖ExplicitPerron.psi chi t - ExplicitPerron.psi chi.primitiveCharacter t‖ ≤
      0.000001 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
  (norm_psi_sub_primitive_le chi
    (by linarith [(PerronBudget.source_cutoff_bounds hN htlo hthi).1])).trans
      (induction_cost_source_le hN hqUpper htlo hthi)

theorem psi_primitive_highZeroSum_source_le {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (hchi : chi ≠ 1)
    [NeZero chi.conductor] {t : ℝ}
    (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖ExplicitPerron.psi chi t +
        FixedHeightZeroSum.highZeroSum chi.primitiveCharacter t (sourceT N)‖ ≤
      1.374172 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  obtain ⟨hc, hcUpper, hcNe, hcPrimitive⟩ := conductor_source_domain chi hchi hqUpper
  have hp := PerronBudget.psi_highZeroSum_source_le_strong
    hN hc hcUpper hcNe hcPrimitive htlo hthi
  have hd := norm_psi_sub_primitive_source_le chi hN hqUpper htlo hthi
  calc
    _ = ‖(ExplicitPerron.psi chi t - ExplicitPerron.psi chi.primitiveCharacter t) +
        (ExplicitPerron.psi chi.primitiveCharacter t +
          FixedHeightZeroSum.highZeroSum chi.primitiveCharacter t (sourceT N))‖ := by
      congr 1
      abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ 0.000001 * t / sourceT N * sourceL N ^ (2 : ℕ) +
        1.374171 * t / sourceT N * sourceL N ^ (2 : ℕ) := add_le_add hd hp
    _ = _ := by ring

end LiuWang.Proof.NonprincipalPsi
