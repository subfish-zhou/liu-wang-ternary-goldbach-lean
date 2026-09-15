import LiuWang.Proof.DirichletZeroCount.Consumer
import LiuWang.Proof.ZeroRegionFamily.RealClosure.Principal
import LiuWang.Proof.Parameters.Main

/-!
# Actual weighted ordinary-L zeros on a closed high-height band

The weight is exactly `N^(Re rho - 1) / |Im rho|`, with ordinary analytic
multiplicity and all characters, including the principal character.
The numerical mother bound uses the proved R20 high-nonreal region and
the conductor-sensitive count producers. It is not Lemma 2.2's constant.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedHighZeros

def bandSum (N q : ℕ) [NeZero q] (u y : ℝ) : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ bandValues chi (1 / 2) u y,
    (analyticOrderNatAt chi.LFunction rho : ℝ) *
      ((N : ℝ) ^ (rho.re - 1) / |rho.im|)

def highSum (N q : ℕ) [NeZero q] : ℝ :=
  bandSum N q (omegaCutoff N q) (sourceT N)

def countBudget (q : ℕ) (y : ℝ) : ℝ :=
  min (principalBound y + (q.totient - 1 : ℕ) * nonprincipalBound q y)
    ((q.totient : ℝ) * (y + Real.sqrt y) *
      (Real.log q / 2 + Real.log (y + Real.sqrt y + 2) / 2 + 7 / 3) /
        Real.arctan (Real.sqrt y / 2))

theorem familyCount_le_countBudget (q : ℕ) [NeZero q] (alpha : ℝ)
    {y : ℝ} (hy : 0 < y) :
    (familyCount q alpha y : ℝ) ≤ countBudget q y := by
  refine le_min ((familyCount_le q alpha hy.le).trans (familyBound_le_modulus q hy.le)) ?_
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hc (chi : Character q) :
      (count chi alpha y : ℝ) ≤ (y + Real.sqrt y) *
        (Real.log q / 2 + Real.log (y + Real.sqrt y + 2) / 2 + 7 / 3) /
          Real.arctan (Real.sqrt y / 2) := by
    by_cases hchi : chi = 1
    · subst chi
      exact (count_principal_smoothed q alpha hy.le hs).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
          (Real.arctan_pos.mpr (by positivity)).le)
    · have hld : Real.log chi.conductor ≤ Real.log q :=
        Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero)
          (by exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi)
      exact (count_conductor_smoothed hchi alpha hy.le hs).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
          (Real.arctan_pos.mpr (by positivity)).le)
  have hcard : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => hc chi)
  simpa only [familyCount, Nat.cast_sum, Finset.sum_const, Finset.card_univ,
    hcard, nsmul_eq_mul, mul_div_assoc, mul_assoc] using hsum

def heightScale (q : ℕ) (y : ℝ) : ℝ := max 10 ((q : ℝ) * y)

theorem band_zero_re_le {q : ℕ} [NeZero q] {chi : Character q}
    {u y : ℝ} (hu : 1 ≤ u) {rho : ℂ}
    (hrho : rho ∈ bandValues chi (1 / 2) u y) :
    rho.re ≤ 1 - 1 / (20 * Real.log (heightScale q y)) := by
  obtain ⟨hz, ⟨_, h1, ht⟩, _, hlo⟩ := mem_bandValues.mp hrho
  have hx : 10 ≤ heightScale q y := le_max_left _ _
  have hheight : |rho.im| ≤ heightScale q y / (q : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr (NeZero.pos q))).mpr
    exact (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _)).trans
      (by simpa only [heightScale, mul_comm] using (le_max_right 10 ((q : ℝ) * y)))
  by_contra h
  have hr := lt_of_not_ge h
  by_cases hc : chi = 1
  · subst chi
    exact ZeroRegionFamily.RealClosure.principal_no_zero_twenty hx hr hheight
      (by intro he; simp [he] at h1) hz
  · have hq : (q : ℝ) ≤ heightScale q y := by
      exact (le_mul_of_one_le_right (Nat.cast_nonneg q) ((hu.trans hlo).trans ht)).trans
        (le_max_right _ _)
    exact ZeroRegionFamily.Sharp.nonprincipal_high_no_zero_twenty hx hq chi hc hr
      (by linarith) hheight hz

def decay (N q : ℕ) (y : ℝ) : ℝ :=
  Real.exp (-Real.log N / (20 * Real.log (heightScale q y)))

theorem band_weight_le_decay {N q : ℕ} [NeZero q] (hN : 1 ≤ N)
    {chi : Character q} {u y : ℝ} (hu : 1 ≤ u) {rho : ℂ}
    (hrho : rho ∈ bandValues chi (1 / 2) u y) :
    (N : ℝ) ^ (rho.re - 1) ≤ decay N q y := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ (N : ℝ) ^ (-1 / (20 * Real.log (heightScale q y))) :=
      Real.rpow_le_rpow_of_exponent_le hn (by
        have hb := band_zero_re_le hu hrho
        calc
          rho.re - 1 ≤ -(1 / (20 * Real.log (heightScale q y))) := by linarith
          _ = _ := by ring)
    _ = decay N q y := by
      rw [Real.rpow_def_of_pos (by linarith)]
      congr 1
      ring

def shellBound (N q : ℕ) (u y : ℝ) : ℝ :=
  decay N q y * countBudget q y / u

theorem bandSum_nonneg (N q : ℕ) [NeZero q] (u y : ℝ) :
    0 ≤ bandSum N q u y := by
  apply Finset.sum_nonneg
  intro chi _
  exact Finset.sum_nonneg (fun rho _ => by positivity)

theorem bandSum_le_shellBound {N q : ℕ} [NeZero q] (hN : 1 ≤ N)
    {u y : ℝ} (hu : 1 ≤ u) (hy : 0 < y) :
    bandSum N q u y ≤ shellBound N q u y := by
  have hu0 : 0 < u := by linarith
  have hdec : 0 ≤ decay N q y := (Real.exp_pos _).le
  have hf (chi : Character q) (rho : ℂ) (hrho : rho ∈ bandValues chi (1 / 2) u y) :
      (N : ℝ) ^ (rho.re - 1) / |rho.im| ≤ decay N q y / u :=
    div_le_div₀ hdec (band_weight_le_decay hN hu hrho) hu0
      (mem_bandValues.mp hrho).2.2.2
  have hc (chi : Character q) := band_weighted_sum_le_count chi (1 / 2) u y
    (fun rho => (N : ℝ) ^ (rho.re - 1) / |rho.im|) (div_nonneg hdec hu0.le) (hf chi)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => hc chi)
  have he : bandSum N q u y ≤ (decay N q y / u) * (familyCount q (1 / 2) y : ℝ) := by
    simpa only [bandSum, familyCount, Nat.cast_sum, Finset.mul_sum] using hsum
  exact he.trans ((mul_le_mul_of_nonneg_left (familyCount_le_countBudget q (1 / 2) hy)
    (div_nonneg hdec hu0.le)).trans_eq (by unfold shellBound; ring))

theorem highSum_le_single_shell {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ shellBound N q (omegaCutoff N q) (sourceT N) :=
  bandSum_le_shellBound (Parameters.nat_pos_of_exp_le hN)
    (by linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq])
    (Parameters.sourceT_pos (Parameters.exp_2000_le_of_exp_3100_le hN))

end LiuWang.Proof.WeightedHighZeros
