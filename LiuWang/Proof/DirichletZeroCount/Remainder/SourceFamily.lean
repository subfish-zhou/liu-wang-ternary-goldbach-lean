import LiuWang.Proof.DirichletZeroCount.Remainder.SourceFive

/-! # Literal source counts and stronger all-family, complete-S weighted consumers -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open LiuWang.Proof.Interfaces (Character)

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def sourcePrincipalBound (y : ℝ) : ℝ := if y = 0 then 0 else sourceFiveBound y

def sourceFamilyBound (q : ℕ) [NeZero q] (y : ℝ) : ℝ :=
  sourcePrincipalBound y + ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
    sourceSixBound chi.conductor y

def sourceModulusFamilyBound (q : ℕ) (y : ℝ) : ℝ :=
  sourcePrincipalBound y + (q.totient - 1 : ℕ) * sourceSixBound q y

theorem uniformNonprincipalBound_le_sourceSix {q : ℕ} (hq : 3 ≤ q) (chi : Character q)
    {y : ℝ} (hy : 0 ≤ y) :
    uniformNonprincipalBound q (parityShift chi) y ≤ sourceSixBound q y := by
  by_cases hys : y ≤ 10 / 3
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hqlog := log_modulus_ge_one hq
    have hl := log_small_height_upper hy hys
    have hrough {t : ℝ} (ht : y ≤ t) :
        nonprincipalBound q y ≤ (2 * t + 3) * (Real.log q / 2 + 9 / 4) := by
      unfold nonprincipalBound
      apply mul_le_mul (by linarith) (by linarith) _ (by linarith)
      have hh := Real.log_nonneg (by linarith : 1 ≤ y + 3)
      linarith
    have hlog {c : ℝ} (hc : c ≤ Real.log (2 + y)) :
        Real.log q + c ≤ Real.log ((q : ℝ) * (2 + y)) := by
      rw [Real.log_mul hq0.ne' (by positivity)]
      linarith
    apply (min_le_left _ _).trans
    by_cases hy2 : y ≤ 2
    · have hl2 : 2 / 3 ≤ Real.log (2 + y) := by
        have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 + y)
        linarith [Real.log_two_gt_d9]
      have hb := sourceSix_affine_lower hq (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (hlog hl2) (sixMain_small_lower hq hy hy2)
      have hu := hrough hy2
      norm_num at hu
      linarith
    · have hy2' : 2 ≤ y := le_of_lt (lt_of_not_ge hy2)
      have hm := sixMain_middle_lower hq hy2' hys
      by_cases hy3 : y ≤ 3
      · have hl4 : 4 / 3 ≤ Real.log (2 + y) := by
          have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : 4 ≤ 2 + y)
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at hh
          norm_num only [Nat.cast_ofNat] at hh
          linarith [Real.log_two_gt_d9]
        have hb := sourceSix_affine_lower hq (by norm_num : (0 : ℝ) ≤ 4 / 3) (hlog hl4) hm
        have hu := hrough hy3
        norm_num at hu
        linarith
      · have hl5 : 19 / 12 ≤ Real.log (2 + y) := by
          have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 5) (by linarith : 5 ≤ 2 + y)
          have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
          have he : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4) := by
            rw [show (5 : ℝ) = 2 ^ (2 : ℕ) * (5 / 4) by norm_num,
              Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
            norm_num
          rw [he] at hh
          norm_num at ht
          linarith [Real.log_two_gt_d9]
        have hb := sourceSix_affine_lower hq (by norm_num : (0 : ℝ) ≤ 19 / 12) (hlog hl5) hm
        have hu := hrough hys
        norm_num at hu
        linarith
  · exact (min_le_right _ _).trans
      (uniformCountBound_le_sourceSix_high hq chi (le_of_lt (lt_of_not_ge hys)))

theorem uniformPrincipalBound_le_source {y : ℝ} (hy : 0 ≤ y) :
    uniformPrincipalBound y ≤ sourcePrincipalBound y := by
  unfold sourcePrincipalBound
  split_ifs with h
  · subst y
    exact (min_le_left _ _).trans (by norm_num [principalBound])
  · exact (min_le_right _ _).trans (uniformXiCountBound_le_sourceFive (lt_of_le_of_ne hy (Ne.symm h)))

theorem uniformFamilyBound_le_source (q : ℕ) [NeZero q] {y : ℝ} (hy : 0 ≤ y) :
    uniformFamilyBound q y ≤ sourceFamilyBound q y := by
  unfold uniformFamilyBound sourceFamilyBound
  apply add_le_add (uniformPrincipalBound_le_source hy)
  apply Finset.sum_le_sum
  intro chi hc
  have hn := (Finset.mem_erase.mp hc).1
  have hq := BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hn
  have hh := uniformNonprincipalBound_le_sourceSix hq chi.primitiveCharacter hy
  simpa only [parityShift_primitive] using hh

theorem sourceSixBound_mono_modulus {d q : ℕ} (hd : 0 < d) (hdq : d ≤ q)
    {y : ℝ} (hy : 0 ≤ y) : sourceSixBound d y ≤ sourceSixBound q y := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdqR : (d : ℝ) ≤ q := Nat.cast_le.mpr hdq
  have hn : 0 < ‖(3 / 2 : ℂ) + (y : ℂ) * I‖ :=
    lt_of_lt_of_le (by norm_num) (re_le_norm _)
  have hlog := Real.log_le_log (div_pos (mul_pos hdR hn) (by positivity : 0 < 2 * Real.pi))
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hdqR hn.le)
      (by positivity : 0 ≤ 2 * Real.pi))
  have hL := Real.log_le_log (by positivity : 0 < (d : ℝ) * (2 + y))
    (mul_le_mul_of_nonneg_right hdqR (by positivity : 0 ≤ 2 + y))
  have h1 := mul_le_mul_of_nonneg_left hlog (div_nonneg hy Real.pi_pos.le)
  have h2 := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 7 * (1 + 3 / Real.pi))
  unfold sourceSixBound
  linarith

theorem sourceFamilyBound_le_modulus (q : ℕ) [NeZero q] {y : ℝ} (hy : 0 ≤ y) :
    sourceFamilyBound q y ≤ sourceModulusFamilyBound q y := by
  have hc : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  unfold sourceFamilyBound sourceModulusFamilyBound
  apply add_le_add_right
  calc
    _ ≤ ∑ _chi ∈ (Finset.univ : Finset (Character q)).erase 1, sourceSixBound q y :=
      Finset.sum_le_sum (fun chi _ => sourceSixBound_mono_modulus
        (Nat.pos_of_ne_zero chi.conductor_ne_zero)
        (BombieriVinogradov.DirichletCharacter.conductor_le_level chi) hy)
    _ = _ := by simp [hc]

theorem familyCount_le_source (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (familyCount q alpha y : ℝ) ≤ sourceFamilyBound q y :=
  (familyCount_le_uniformFamilyBound q ha hy).trans (uniformFamilyBound_le_source q hy)

theorem normalized_familyCount_le_source (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 0 ≤ alpha) (hy : 0 ≤ y) :
    (familyCount q alpha y : ℝ) / q.totient ≤ sourceModulusFamilyBound q y / q.totient :=
  div_le_div_of_nonneg_right
    ((familyCount_le_source q ha hy).trans (sourceFamilyBound_le_modulus q hy)) (Nat.cast_nonneg _)

theorem normalized_complete_inverse_le_source (q : ℕ) [NeZero q]
    {u y : ℝ} (hu : 0 < u) (hy : 0 ≤ y) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => u ≤ |rho.im|),
        (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) / q.totient ≤
          sourceFamilyBound q y / (u * q.totient) :=
  (normalized_complete_inverse_le_uniform q hu hy).trans
    (div_le_div_of_nonneg_right (uniformFamilyBound_le_source q hy) (by positivity))

theorem normalized_complete_inverse_sqrt_le_source (q : ℕ) [NeZero q]
    {u y : ℝ} (hu : 0 < u) (hy : 0 ≤ y) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi y).filter (fun rho => u ≤ |rho.im|),
        (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) / q.totient ≤
          sourceFamilyBound q y / (Real.sqrt u * q.totient) :=
  (normalized_complete_inverse_sqrt_le_uniform q hu hy).trans
    (div_le_div_of_nonneg_right (uniformFamilyBound_le_source q hy) (by positivity))

end LiuWang.Proof.DirichletZeroCount.Remainder
