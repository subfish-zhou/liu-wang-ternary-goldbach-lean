import LiuWang.Proof.Campaign20260915.Totient.RSSpectralBounds

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.Campaign20260915.Totient

def rsEpsilon (m : ℕ) (δ : ℝ) : ℝ :=
  δ / 2 * ((((1 + δ) ^ (m + 1) + 1) / 2) ^ m + m)

theorem rsZeroMoment_sum_antitone {m : ℕ} (hm : 1 ≤ m) {L U : ℝ}
    (hL : 0 ≤ L) (hLU : L ≤ U) :
    (∑' p, rsZeroMoment m U p) ≤ ∑' p, rsZeroMoment m L p := by
  apply (rsZeroMoment_summable hm (hL.trans hLU)).tsum_le_tsum _ (rsZeroMoment_summable hm hL)
  intro p
  unfold rsZeroMoment
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hLU (by linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).2])

theorem rsZeroMoment_low_high {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 ≤ L)
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| ≤ rsA → (riemannXiDivisorZeroValue p).re = 1 / 2) :
    (∑' p, rsZeroMoment m L p) ≤
      Real.exp (-L / 2) * (∑' p, rsZeroMoment m 0 p) + ∑' p, rsHighTerm rsA m L p := by
  have hs0 := (rsZeroMoment_summable hm (le_refl (0 : ℝ))).mul_left (Real.exp (-L / 2))
  have hsh := rsHighTerm_summable (le_refl rsA) hL hm
  have hb (p : RiemannXiDivisorZeroIndex) :
      rsZeroMoment m L p ≤ Real.exp (-L / 2) * rsZeroMoment m 0 p + rsHighTerm rsA m L p := by
    by_cases hp : rsA < |(riemannXiDivisorZeroValue p).im|
    · have hn : 0 ≤ Real.exp (-L / 2) * rsZeroMoment m 0 p := by
        unfold rsZeroMoment
        positivity
      simpa only [rsZeroMoment, rsHighTerm, if_pos hp] using
        le_add_of_nonneg_left hn
    · have he := hlow p (le_of_not_gt hp)
      simp only [rsZeroMoment, rsHighTerm, if_neg hp, he, mul_zero, Real.exp_zero, add_zero]
      rw [show ((1 / 2 : ℝ) - 1) * L = -L / 2 by ring]
      exact le_of_eq (by ring)
  exact ((rsZeroMoment_summable hm hL).tsum_le_tsum hb (hs0.add hsh)).trans_eq
    (by rw [hs0.tsum_add hsh, tsum_mul_left])

theorem rsPsi_delta_epsilon_of_actual_moment {m : ℕ} (hm : 1 ≤ m)
    {δ a x : ℝ} (hδ : 0 < δ) (ha : 1 < a)
    (hcut : 1 + (m : ℝ) * δ * a < a) (hax : a ≤ x)
    (hbudget : (∑' p, rsZeroMoment m (Real.log a) p) ≤ (δ / 2) ^ (m + 1)) :
    x * (1 - rsEpsilon m δ) - 1.84 < Chebyshev.psi x ∧
      Chebyshev.psi x < x * (1 + rsEpsilon m δ) - (1 / 2) * Real.log (1 - x⁻¹ ^ 2) := by
  have hx0 : 0 < x := (by linarith : 0 < a).trans_le hax
  have hW := (rsZeroMoment_sum_antitone hm (Real.log_nonneg ha.le)
    (Real.log_le_log (by linarith) hax)).trans hbudget
  let F : ℝ := 1 + (1 + δ) ^ (m + 1)
  have hF : 2 ≤ F := by
    dsimp [F]
    have hp : (1 : ℝ) ≤ (1 + δ) ^ (m + 1) := one_le_pow₀ (by linarith)
    linarith
  have hc : 0 ≤ x * F ^ m / δ ^ m := by positivity
  have hb : x * F ^ m / δ ^ m * (∑' p, rsZeroMoment m (Real.log x) p) ≤
      x * δ / 2 * (F / 2) ^ m := by
    apply (mul_le_mul_of_nonneg_left hW hc).trans_eq
    rw [div_pow, div_pow, pow_succ]
    field_simp
    rw [pow_succ, mul_comm]
  have hlo : x * 2 ^ m / δ ^ m * (∑' p, rsZeroMoment m (Real.log x) p) ≤
      x * F ^ m / δ ^ m * (∑' p, rsZeroMoment m (Real.log x) p) := by
    apply mul_le_mul_of_nonneg_right
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hF m) hx0.le)
        (pow_pos hδ m).le
    · exact tsum_nonneg (fun p => by unfold rsZeroMoment; positivity)
  obtain ⟨hl, hu⟩ := rsPsi_original_moment_bounds hm hδ (by linarith) hcut hax
  have he : x * rsEpsilon m δ = (m : ℝ) * δ * x / 2 + x * δ / 2 * (F / 2) ^ m := by
    unfold rsEpsilon F
    rw [add_comm ((1 + δ) ^ (m + 1)) 1]
    ring
  change x + (m : ℝ) * δ * x / 2 +
    x * F ^ m / δ ^ m * (∑' p, rsZeroMoment m (Real.log x) p) + rsTrivialKernel x >
      Chebyshev.psi x at hu
  unfold rsTrivialKernel at hu
  constructor <;> nlinarith

theorem rsPsi_delta_epsilon_of_low_window_and_high_sum {m : ℕ} (hm : 1 ≤ m)
    {δ a x k B : ℝ} (hδ : 0 < δ) (ha : 1 < a)
    (hcut : 1 + (m : ℝ) * δ * a < a) (hax : a ≤ x)
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| ≤ rsA → (riemannXiDivisorZeroValue p).re = 1 / 2)
    (hk : (∑' p, rsZeroMoment m 0 p) ≤ k)
    (hhigh : (∑' p, rsHighTerm rsA m (Real.log a) p) ≤ B)
    (hbudget : Real.exp (-Real.log a / 2) * k + B ≤ (δ / 2) ^ (m + 1)) :
    x * (1 - rsEpsilon m δ) - 1.84 < Chebyshev.psi x ∧
      Chebyshev.psi x < x * (1 + rsEpsilon m δ) - (1 / 2) * Real.log (1 - x⁻¹ ^ 2) := by
  apply rsPsi_delta_epsilon_of_actual_moment hm hδ ha hcut hax
  exact ((rsZeroMoment_low_high hm (Real.log_nonneg ha.le) hlow).trans
    (add_le_add (mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le) hhigh)).trans hbudget

theorem rs_delta_root_budget (m : ℕ) {T δ : ℝ} (hT : 0 ≤ T)
    (hδ : 2 * T ^ (1 / ((m : ℝ) + 1)) ≤ δ) :
    T ≤ (δ / 2) ^ (m + 1) := by
  have hr : T ^ (((m + 1 : ℕ) : ℝ)⁻¹) ≤ δ / 2 := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using (show
      T ^ (1 / ((m : ℝ) + 1)) ≤ δ / 2 by linarith)
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hT _) hr (m + 1)
  simpa only [Real.rpow_inv_natCast_pow hT (Nat.succ_ne_zero m)] using hp

theorem rs_low_weight_sqrt {a : ℝ} (ha : 0 < a) :
    Real.exp (-Real.log a / 2) = 1 / Real.sqrt a := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha, one_div, ← Real.exp_neg]
  congr 1
  ring

theorem rsPsi_original_root_epsilon {m : ℕ} (hm : 1 ≤ m)
    {δ a x k B : ℝ} (hδ : 0 < δ) (ha : 1 < a)
    (hcut : 1 + (m : ℝ) * δ * a < a) (hax : a ≤ x)
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| ≤ rsA → (riemannXiDivisorZeroValue p).re = 1 / 2)
    (hk : (∑' p, rsZeroMoment m 0 p) ≤ k)
    (hhigh : (∑' p, rsHighTerm rsA m (Real.log a) p) ≤ B)
    (hroot : 2 * (k / Real.sqrt a + B) ^ (1 / ((m : ℝ) + 1)) ≤ δ) :
    x * (1 - rsEpsilon m δ) - 1.84 < Chebyshev.psi x ∧
      Chebyshev.psi x < x * (1 + rsEpsilon m δ) - (1 / 2) * Real.log (1 - x⁻¹ ^ 2) := by
  have hk0 : 0 ≤ k := (tsum_nonneg (fun p => by unfold rsZeroMoment; positivity)).trans hk
  have hB0 : 0 ≤ B := (tsum_nonneg (fun p => by
    unfold rsHighTerm
    split_ifs <;> positivity)).trans hhigh
  apply rsPsi_delta_epsilon_of_low_window_and_high_sum hm hδ ha hcut hax hlow hk hhigh
  rw [rs_low_weight_sqrt (by linarith : 0 < a)]
  simpa only [one_div, inv_mul_eq_div] using
    rs_delta_root_budget m (show 0 ≤ k / Real.sqrt a + B by positivity) hroot

#print axioms rsZeroMoment_sum_antitone
#print axioms rsZeroMoment_low_high
#print axioms rsPsi_delta_epsilon_of_actual_moment
#print axioms rsPsi_delta_epsilon_of_low_window_and_high_sum
#print axioms rs_delta_root_budget
#print axioms rs_low_weight_sqrt
#print axioms rsPsi_original_root_epsilon

end LiuWang.Proof.Campaign20260915.Totient
