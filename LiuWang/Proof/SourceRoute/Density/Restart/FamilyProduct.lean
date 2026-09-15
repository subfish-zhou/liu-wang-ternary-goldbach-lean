import LiuWang.Proof.SourceRoute.Density.FamilyLittlewood
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionConjugation
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Chen's whole nonprincipal product and the common-point family square sum. -/

set_option autoImplicit false

noncomputable section

open Complex Finset Set
open scoped ComplexConjugate Classical
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.SourceRoute.Density.Restart

def familyProduct (q : ℕ) [NeZero q] (X : ℝ) (s : ℂ) : ℂ :=
  ∏ chi ∈ nonprincipalCharacters q, H chi X s

def familySquare (q : ℕ) [NeZero q] (X : ℝ) (s : ℂ) : ℝ :=
  ∑ chi ∈ nonprincipalCharacters q, ‖f chi X s‖ ^ 2

theorem familySquare_nonneg (q : ℕ) [NeZero q] (X : ℝ) (s : ℂ) :
    0 ≤ familySquare q X s := sum_nonneg (fun _ _ => sq_nonneg _)

theorem familyProduct_differentiable (q : ℕ) [NeZero q] (X : ℝ) :
    Differentiable ℂ (familyProduct q X) := by
  apply Differentiable.fun_finsetProd
  intro chi hchi
  exact differentiable_H ((mem_nonprincipalCharacters chi).mp hchi) X

theorem familySquare_continuous (q : ℕ) [NeZero q] (X : ℝ) :
    Continuous (familySquare q X) := by
  apply continuous_finsetSum
  intro chi hchi
  exact ((differentiable_f ((mem_nonprincipalCharacters chi).mp hchi) X).continuous.norm).pow 2

theorem Q_inv_conj {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ) (s : ℂ) :
    Q chi⁻¹ X (conj s) = conj (Q chi X s) := by
  unfold Q
  rw [map_sum]
  apply sum_congr rfl
  intro n _
  have hc : chi⁻¹ n = conj (chi n) := by
    rw [← MulChar.star_eq_inv, MulChar.star_apply]
    rfl
  have hpow : (n : ℂ) ^ conj s = conj ((n : ℂ) ^ s) := by
    simpa only [conj_natCast] using
      (Complex.cpow_conj (n : ℂ) s (by simpa using Real.pi_pos.ne))
  simp only [twistedMu, hc, map_div₀, map_mul, hpow, map_intCast]

theorem f_inv_conj {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) (s : ℂ) :
    f chi⁻¹ X (conj s) = conj (f chi X s) := by
  rw [f, DirichletCharacter.LFunction_inv_eq_conj_conj hchi, conj_conj, Q_inv_conj]
  simp only [f, map_sub, map_mul, map_one]

theorem H_inv_conj {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) (s : ℂ) :
    H chi⁻¹ X (conj s) = conj (H chi X s) := by
  simp only [H, f_inv_conj hchi, map_sub, map_one, map_pow]

theorem nonprincipal_inv_perm (q : ℕ) [NeZero q] :
    (nonprincipalCharacters q).image (fun chi => chi⁻¹) = nonprincipalCharacters q := by
  classical
  ext chi
  simp only [Finset.mem_image, mem_nonprincipalCharacters]
  constructor
  · rintro ⟨psi, hp, rfl⟩
    exact inv_ne_one.mpr hp
  · intro hc
    exact ⟨chi⁻¹, inv_ne_one.mpr hc, inv_inv chi⟩

theorem familyProduct_conj (q : ℕ) [NeZero q] (X : ℝ) (s : ℂ) :
    familyProduct q X (conj s) = conj (familyProduct q X s) := by
  classical
  unfold familyProduct
  rw [map_prod]
  calc
    _ = ∏ chi ∈ nonprincipalCharacters q, H chi⁻¹ X (conj s) := by
      have hp := Finset.prod_image (s := nonprincipalCharacters q) (g := fun chi => chi⁻¹)
        (f := fun chi => H chi X (conj s)) (fun a _ b _ h => inv_injective h)
      rwa [nonprincipal_inv_perm] at hp
    _ = _ := prod_congr rfl (fun chi hc => H_inv_conj ((mem_nonprincipalCharacters chi).mp hc) X s)

theorem familySquare_conj (q : ℕ) [NeZero q] (X : ℝ) (s : ℂ) :
    familySquare q X (conj s) = familySquare q X s := by
  classical
  unfold familySquare
  calc
    _ = ∑ chi ∈ nonprincipalCharacters q, ‖f chi⁻¹ X (conj s)‖ ^ 2 := by
      have hp := Finset.sum_image (s := nonprincipalCharacters q) (g := fun chi => chi⁻¹)
        (f := fun chi => ‖f chi X (conj s)‖ ^ 2) (fun a _ b _ h => inv_injective h)
      rwa [nonprincipal_inv_perm] at hp
    _ = _ := sum_congr rfl (fun chi hc => by
      rw [f_inv_conj ((mem_nonprincipalCharacters chi).mp hc), norm_conj])

theorem familyProduct_ne_zero {q : ℕ} [NeZero q] {X : ℝ} {s : ℂ}
    (hs : ∀ chi ∈ nonprincipalCharacters q, H chi X s ≠ 0) :
    familyProduct q X s ≠ 0 := prod_ne_zero_iff.mpr hs

theorem familyProduct_two_ne_zero (q : ℕ) [NeZero q] {X : ℝ} (hX : 3 < X)
    {s : ℂ} (hs : s.re = 2) : familyProduct q X s ≠ 0 :=
  familyProduct_ne_zero (fun chi _ => H_ne_zero_on_two chi hs hX)

theorem familyProduct_order_finite (q : ℕ) [NeZero q] {X : ℝ} (hX : 3 < X) (s : ℂ) :
    analyticOrderAt (familyProduct q X) s ≠ ⊤ :=
  Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero
    (familyProduct_differentiable q X) ⟨2, familyProduct_two_ne_zero q hX (by norm_num)⟩ s

theorem norm_familyProduct_le_exp (q : ℕ) [NeZero q] (X : ℝ) (s : ℂ) :
    ‖familyProduct q X s‖ ≤ Real.exp (familySquare q X s) := by
  rw [familyProduct, norm_prod]
  apply le_trans (b := ∏ chi ∈ nonprincipalCharacters q, (1 + ‖f chi X s‖ ^ 2))
  · apply prod_le_prod (fun _ _ => norm_nonneg _)
    intro chi _
    have hn := norm_sub_le (1 : ℂ) (f chi X s ^ (2 : ℕ))
    rw [norm_one, norm_pow] at hn
    exact hn
  · exact Real.prod_one_add_le_exp_sum _ (fun _ => sq_nonneg _)

theorem norm_familyProduct_sub_one_le (q : ℕ) [NeZero q] (X : ℝ) (s : ℂ) :
    ‖familyProduct q X s - 1‖ ≤ Real.exp (familySquare q X s) - 1 := by
  have h := (nonprincipalCharacters q).norm_prod_one_add_sub_one_le
    (fun chi => -(f chi X s ^ 2))
  simpa only [familyProduct, H, sub_eq_add_neg, norm_neg, norm_pow, familySquare] using h

@[simp] theorem familyProduct_one (X : ℝ) (s : ℂ) : familyProduct 1 X s = 1 := by
  simp [familyProduct]

@[simp] theorem familyProduct_two (X : ℝ) (s : ℂ) : familyProduct 2 X s = 1 := by
  simp [familyProduct]

end LiuWang.Proof.SourceRoute.Density.Restart
