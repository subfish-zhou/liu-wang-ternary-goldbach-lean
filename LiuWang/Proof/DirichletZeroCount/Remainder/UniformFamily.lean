import LiuWang.Proof.DirichletZeroCount.Remainder.UniformXi

/-! # All-character conductor, modulus and normalized sharpened count producers -/

set_option autoImplicit false
noncomputable section
open scoped Classical
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def uniformPrincipalBound (y : ℝ) : ℝ := min (principalBound y) (uniformXiCountBound y)

def uniformNonprincipalBound (q : ℕ) (a y : ℝ) : ℝ :=
  min (nonprincipalBound q y) (uniformCountBound q a y)

def uniformFamilyBound (q : ℕ) [NeZero q] (y : ℝ) : ℝ :=
  uniformPrincipalBound y + ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
    uniformNonprincipalBound chi.conductor (parityShift chi) y

def uniformModulusFamilyBound (q : ℕ) (y : ℝ) : ℝ :=
  uniformPrincipalBound y + (q.totient - 1 : ℕ) *
    max (uniformNonprincipalBound q (1 / 2) y) (uniformNonprincipalBound q (3 / 2) y)

theorem count_principal_le_uniformBound (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (count (1 : Character q) alpha y : ℝ) ≤ uniformPrincipalBound y :=
  le_min (count_principal_le q alpha hy) (principal_count_alpha_le_uniform q ha hy)

theorem count_nonprincipal_le_uniformBound {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {alpha y : ℝ} (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (count chi alpha y : ℝ) ≤ uniformNonprincipalBound chi.conductor (parityShift chi) y :=
  le_min (count_le_conductor hchi alpha hy) (count_nonprincipal_uniform_conductor hchi ha hy)

theorem uniformNonprincipalBound_mono {d q : ℕ} (hd : 0 < d) (hdq : d ≤ q)
    {a y : ℝ} (hy : 0 ≤ y) :
    uniformNonprincipalBound d a y ≤ uniformNonprincipalBound q a y :=
  min_le_min (nonprincipalBound_mono hd hdq hy) (uniformCountBound_mono_modulus hd hdq hy)

theorem familyCount_le_uniformFamilyBound (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (familyCount q alpha y : ℝ) ≤ uniformFamilyBound q y := by
  unfold familyCount uniformFamilyBound
  rw [Nat.cast_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Character q))]
  have hp := count_principal_le_uniformBound q ha hy
  have hn := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)).erase 1)
    (fun chi hc => count_nonprincipal_le_uniformBound (Finset.mem_erase.mp hc).1 ha hy)
  linarith

theorem uniformFamilyBound_le_modulus (q : ℕ) [NeZero q] {y : ℝ} (hy : 0 ≤ y) :
    uniformFamilyBound q y ≤ uniformModulusFamilyBound q y := by
  have hc : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  unfold uniformFamilyBound uniformModulusFamilyBound
  apply add_le_add_right
  calc
    _ ≤ ∑ _chi ∈ (Finset.univ : Finset (Character q)).erase 1,
        max (uniformNonprincipalBound q (1 / 2) y) (uniformNonprincipalBound q (3 / 2) y) := by
      apply Finset.sum_le_sum
      intro chi _
      apply (uniformNonprincipalBound_mono (Nat.pos_of_ne_zero chi.conductor_ne_zero)
        (BombieriVinogradov.DirichletCharacter.conductor_le_level chi) hy).trans
      unfold parityShift
      split_ifs
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = _ := by simp [hc]

theorem uniformFamilyBound_le_previous (q : ℕ) [NeZero q] (y : ℝ) :
    uniformFamilyBound q y ≤ bothPhaseFamilyBound q y := by
  have hp : uniformPrincipalBound y ≤ principalPhaseBound y :=
    min_le_min le_rfl (uniformXiCountBound_le_previous y)
  have hn (chi : Character q) :
      uniformNonprincipalBound chi.conductor (parityShift chi) y ≤
        allHeightPhaseBound chi.conductor (parityShift chi) y := by
    unfold allHeightPhaseBound uniformNonprincipalBound
    split_ifs
    · exact min_le_min le_rfl (uniformCountBound_le_previous _ _ _)
    · exact min_le_left _ _
  exact add_le_add hp (Finset.sum_le_sum (fun chi _ => hn chi))

theorem normalized_familyCount_le_uniform (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (familyCount q alpha y : ℝ) / q.totient ≤ uniformModulusFamilyBound q y / q.totient :=
  div_le_div_of_nonneg_right
    ((familyCount_le_uniformFamilyBound q ha hy).trans (uniformFamilyBound_le_modulus q hy))
    (Nat.cast_nonneg _)

end LiuWang.Proof.DirichletZeroCount.Remainder
