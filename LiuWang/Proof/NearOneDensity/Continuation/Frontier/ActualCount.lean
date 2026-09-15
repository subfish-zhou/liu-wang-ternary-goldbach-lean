import LiuWang.Proof.NearOneDensity.Continuation.CountInterface
import LiuWang.Proof.NearOneDensity.Continuation.Frontier.Budget

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.NearOneDensity.Continuation.Frontier

theorem strong_row_weight_mass (r : DensityRow) {z : ℝ} (hz : 100000000000 ≤ z) :
    let σ := 1 + rowA r / Real.log z
    (∑' n, dampedWeight σ (stechkinSigma σ) stechkinK n) ≤
      Real.log z * savedMass (rowA r) (719 / 800) (1 / Real.log z) := by
  dsimp only
  rw [damped_mass_eq_zetaDamped (row_sigma_bounds r hz).1]
  have hh := sharp_small_sigma_mass (row_sigma_bounds r hz).1 (row_sigma_bounds r hz).2
  have hL : Real.log z ≠ 0 := by linarith [source_log_lower hz]
  have ha := (row_basic_certificate r).1.ne'
  have he : 1 / (1 + rowA r / Real.log z - 1) - 719 / 800 =
      Real.log z * savedMass (rowA r) (719 / 800) (1 / Real.log z) := by
    unfold savedMass
    field_simp [ha, hL]
    ring
  exact hh.trans_eq he

theorem actual_count_of_weight_bound (r : DensityRow) {q : ℕ} [NeZero q]
    {z lam y M : ℝ} {K : ℕ}
    (hz : 100000000000 ≤ z) (hqy : (q : ℝ) * max 1 y ≤ z)
    (hlam : 0.262132 ≤ lam) (hupper : lam ≤ rowLambda r)
    (hA : 0 ≤ M) (hBA : crossBudget stechkinConductorCoeff (1 / Real.log z) ≤ M)
    (hgap : 0 < zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z) ^ 2 -
      M * crossBudget stechkinConductorCoeff (1 / Real.log z))
    (hratio : (M ^ 2 - M * crossBudget stechkinConductorCoeff (1 / Real.log z)) /
      (zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z) ^ 2 -
        M * crossBudget stechkinConductorCoeff (1 / Real.log z)) < K + 1)
    (hmass : (∑' n, dampedWeight (1 + rowA r / Real.log z)
      (stechkinSigma (1 + rowA r / Real.log z)) stechkinK n) ≤ Real.log z * M) :
    zeroCount q (1 - lam / Real.log z) y ≤ rowMultiplicity r * K := by
  have hlam0 : 0 ≤ lam := by linarith
  have hL : 0 < Real.log z := by linarith [source_log_lower hz]
  have hα := source_alpha_ge_half hz (hupper.trans (row_basic_certificate r).2.1)
  have hD := (row_source_budget r hz hlam hupper).2.2.1
  obtain ⟨s, hsub, hcard, hsep⟩ := actual_paid_cluster_selection r hz hqy hlam0 hupper
  let A := Real.log z * M
  let B := Real.log z * crossBudget stechkinConductorCoeff (1 / Real.log z)
  let D := Real.log z * zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z)
  have hσ := (row_sigma_bounds r hz).1
  have hscaled : 0 < D ^ 2 - A * B := by
    have he : D ^ 2 - A * B = (Real.log z) ^ 2 *
        (zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z) ^ 2 -
          M * crossBudget stechkinConductorCoeff (1 / Real.log z)) := by
      dsimp [A, B, D]
      ring
    rw [he]
    exact mul_pos (sq_pos_of_pos hL) hgap
  have hcount := mixed_count s (fun p : ZeroIndex q => p.1.conductor)
    (fun p => p.1.primitiveCharacter) (fun p => p.2.1.im)
    hσ (hσ.trans_le (stechkinSigma_ge hσ)) (stechkinSigma_ge hσ) stechkinK_mem.2
    (mul_nonneg hL.le hA) (mul_le_mul_of_nonneg_left hBA hL.le)
    (mul_nonneg hL.le hD) hmass
    (fun p hp => by
      have hm := (mem_zeroFamily hα p).mp (hsub hp)
      exact inducing_row_selected_cost r p.1 hz hqy hlam0 hupper hm.1 hm.2.1 hm.2.2.1 hm.2.2.2)
    (fun p hp u hu hpu => by
      have hm := (mem_zeroFamily hα p).mp (hsub hp)
      have hn := (mem_zeroFamily hα u).mp (hsub hu)
      exact inducing_row_cross_cost r p.1 u.1 hz hqy hm.2.2.2 hn.2.2.2
        (fun heq => (hsep p hp u hu hpu heq).le)) hscaled
  have hrat : (A ^ 2 - A * B) / (D ^ 2 - A * B) < K + 1 := by
    dsimp [A, B, D]
    rw [scaled_ratio_eq hL.ne']
    exact hratio
  have hs : s.card < K + 1 := by exact_mod_cast hcount.trans_lt hrat
  exact hcard.trans (Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp hs))

theorem inverse_band_of_family_bound {q : ℕ} [NeZero q] {alpha u y : ℝ} {J : ℕ}
    (hcount : DirichletZeroCount.familyCount q alpha y ≤ J) (hu : 0 < u) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ρ ∈ DirichletZeroCount.bandValues χ alpha u y,
      (analyticOrderNatAt χ.LFunction ρ : ℝ) / |ρ.im|) ≤ (J : ℝ) / u := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
    (fun χ _ => DirichletZeroCount.band_weighted_sum_le_count χ alpha u y
      (fun ρ => 1 / |ρ.im|) (by positivity : (0 : ℝ) ≤ 1 / u) (fun _ hρ =>
        one_div_le_one_div_of_le hu (DirichletZeroCount.mem_bandValues.mp hρ).2.2.2))
  simp only [mul_one_div, one_div_mul_eq_div, ← Finset.sum_div, ← Nat.cast_sum] at hh
  exact hh.trans (div_le_div_of_nonneg_right (by exact_mod_cast hcount) hu.le)

end LiuWang.Proof.NearOneDensity.Continuation.Frontier
