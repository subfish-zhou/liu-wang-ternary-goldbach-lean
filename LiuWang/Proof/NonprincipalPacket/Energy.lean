import LiuWang.Proof.CharacterExpansion.Finite

/-!
# 原 Gauss 系数的全字符能量

复用由 `charOrthSum` 展开双有限和所得的单位 Parseval。
这里不要求 a 与 q 互素，也不要求字符本原。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.NonprincipalPacket

theorem unit_indicator_sum {q : ℕ} [NeZero q] :
    (∑ x : ZMod q, if IsUnit x then (1 : ℝ) else 0) = (q.totient : ℝ) := by
  classical
  have hc : (Finset.univ.filter (fun x : ZMod q => IsUnit x)).card = q.totient := by
    rw [← Fintype.card_subtype]
    refine (Fintype.card_congr ?_).trans (ZMod.card_units_eq_totient q)
    exact
      { toFun := fun x => x.2.unit
        invFun := fun u => ⟨(u : ZMod q), u.isUnit⟩
        left_inv := fun x => Subtype.ext x.2.unit_spec
        right_inv := fun u => Units.ext rfl }
  simpa only [Finset.sum_boole] using congrArg (Nat.cast (R := ℝ)) hc

theorem gauss_energy {q : ℕ} [NeZero q] (a : ℕ) :
    (∑ chi : Character q, ‖G a chi‖ ^ 2) = (q.totient : ℝ) ^ 2 := by
  have hp := charParseval_units (ZMod.stdAddChar.mulShift (a : ZMod q))
  have hn (x : ZMod q) :
      ‖ZMod.stdAddChar.mulShift (a : ZMod q) x‖ = 1 := by
    exact (ZMod.toCircle ((a : ZMod q) * x)).norm_coe
  simpa only [G, gaussSum, MulChar.star_apply', hn, one_pow,
    pow_two, mul_one, unit_indicator_sum] using hp

theorem sum_norm_G_le {q : ℕ} [NeZero q] (a : ℕ) :
    (∑ chi : Character q, ‖G a chi‖) ≤
      Real.sqrt (q.totient : ℝ) * (q.totient : ℝ) := by
  have hc : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, hc, gauss_energy, Real.sqrt_sq (Nat.cast_nonneg _)]
    using Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Character q))
      (fun _ => (1 : ℝ)) (fun chi => ‖G a chi‖)

theorem nonprincipal_gauss_mass_le_totient {q : ℕ} [NeZero q] (a : ℕ) :
    (q.totient : ℝ)⁻¹ *
        (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, ‖G a chi‖) ≤
      Real.sqrt (q.totient : ℝ) := by
  classical
  have hphi : 0 < (q.totient : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hs :
      (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, ‖G a chi‖) ≤
        ∑ chi : Character q, ‖G a chi‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun chi _ _ => norm_nonneg (G a chi))
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * (Real.sqrt (q.totient : ℝ) * (q.totient : ℝ)) :=
      mul_le_mul_of_nonneg_left (hs.trans (sum_norm_G_le a)) (by positivity)
    _ = Real.sqrt (q.totient : ℝ) := by field_simp

theorem nonprincipal_gauss_mass_le {q : ℕ} [NeZero q] (a : ℕ) :
    (q.totient : ℝ)⁻¹ *
        (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, ‖G a chi‖) ≤
      Real.sqrt (q : ℝ) :=
  (nonprincipal_gauss_mass_le_totient a).trans
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le q))

end LiuWang.Proof.NonprincipalPacket
