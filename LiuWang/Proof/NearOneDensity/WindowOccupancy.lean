import LiuWang.Proof.NearOneDensity.WindowKernel
import LiuWang.Proof.NearOneDensity.SharpMass
import LiuWang.Proof.NearOneDensity.SourceConsumer

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate
open Complex BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.NearOneDensity

theorem primitive_window_mass_budget {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (s : Finset (SymmetricCompletedZeroIndex χ))
    (hr : ∀ p ∈ s, 1 / 2 < (Hadamard.divisorZeroIndex₀_val p).re)
    {a L t : ℝ} (hL : 25 ≤ L) (ha : 0 < a) (haL : a / L ≤ 3 / 20)
    (hheight : Real.log q + Real.log (max 1 |t|) ≤ L + 1 / 10) :
    (∑ p ∈ s, (dampedZeroKernel (1 + a / L) t (Hadamard.divisorZeroIndex₀_val p) +
      dampedZeroKernel (1 + a / L) t (1 - conj (Hadamard.divisorZeroIndex₀_val p)))) ≤
        L * (1 / a + 277 / 1000) := by
  have hL0 : 0 < L := by linarith
  have hσ : 1 < 1 + a / L := by linarith [div_pos ha hL0]
  have hσ₁ : 1 + a / L ≤ 23 / 20 := by linarith
  have hbudget := primitive_finite_reflected_budget hχ hp s hr hσ hσ₁ t
  have hmass := (logKernel_bounds_by_mass χ t hσ
    (hσ.trans_le (stechkinSigma_ge hσ)) (stechkinSigma_ge hσ) stechkinK_mem.2).1
  rw [logKernel_eq_dampedLogDeriv, damped_mass_eq_zetaDamped hσ] at hmass
  have hm := zeta_real_strong hσ hσ₁
  have hid : 1 / (1 + a / L - 1) = L * (1 / a) := by
    field_simp [hL0.ne', ha.ne']
    ring
  rw [hid] at hm
  have hk : 0 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_mem.2]
  have hk' : stechkinConductorCoeff ≤ 277 / 1000 := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_ge_447]
  have hh := mul_le_mul_of_nonneg_left
    (show Real.log q + Real.log (max 1 |t|) - Real.log Real.pi ≤ L by
      linarith [log_pi_ge_one]) hk
  have hh' := mul_le_mul_of_nonneg_right hk' hL0.le
  nlinarith

def rowWindowA : DensityRow → ℝ
  | .r027 | .r028 | .r030 => 1.69
  | .r031 => 1.68 | .r032 => 1.67 | .r033 => 1.66
  | .r036 => 1.62 | .r039 => 1.58 | .r042 => 1.55
  | .r045 | .r046 | .r047 | .r0475 | .r0478 => 3.12

def rowWindowContribution (r : DensityRow) : ℝ :=
  (rowWindowA r + rowLambda r) /
    ((rowWindowA r + rowLambda r) ^ 2 + rowRadius r ^ 2) - 3 / 1250

theorem row_window_certificate (r : DensityRow) :
    0 < rowWindowA r ∧ rowWindowA r ≤ 15 / 4 ∧
      rowRadius r < rowWindowA r ∧ rowRadius r ≤ 2.04 ∧
      0 < rowWindowContribution r ∧
      1 / rowWindowA r + 277 / 1000 <
        ((rowMultiplicity r : ℝ) + 1) * rowWindowContribution r := by
  cases r <;> norm_num [rowWindowA, rowWindowContribution, rowRadius, rowLambda,
    rowMultiplicity]

theorem row_window_count_of_pair_budget (r : DensityRow) {ι : Type*}
    (s : Finset ι) (value : ι → ℂ) {L lam t : ℝ}
    (hL : 25 ≤ L) (hlam : 0 ≤ lam) (hlam₁ : lam ≤ rowLambda r)
    (hre : ∀ p ∈ s, 1 - lam / L ≤ (value p).re)
    (hright : ∀ p ∈ s, (value p).re ≤ 1)
    (ht : ∀ p ∈ s, |t - (value p).im| ≤ rowRadius r / L)
    (hbudget : (∑ p ∈ s, (dampedZeroKernel (1 + rowWindowA r / L) t (value p) +
      dampedZeroKernel (1 + rowWindowA r / L) t (1 - conj (value p)))) ≤
        L * (1 / rowWindowA r + 277 / 1000)) :
    s.card ≤ rowMultiplicity r := by
  have hc := row_window_certificate r
  have hL0 : 0 < L := by linarith
  have hmax : rowLambda r ≤ 1 / 2 := by cases r <;> norm_num [rowLambda]
  have hα : 1 / 2 < 1 - lam / L := by
    have hh : lam / L < 1 / 2 := (div_lt_iff₀ hL0).mpr (by linarith)
    linarith
  have hr (p) (hps : p ∈ s) : 1 / 2 < (value p).re :=
    hα.trans_le (hre p hps)
  have hmono := cauchy_kernel_interval_lower
    (show 0 < rowWindowA r + lam by linarith [hc.1])
    (show rowWindowA r + lam ≤ rowWindowA r + rowLambda r by linarith)
    (rowRadius_nonneg r) (by linarith [hc.2.2.1])
    (show |rowRadius r| ≤ rowRadius r by rw [abs_of_nonneg (rowRadius_nonneg r)])
  have hlower (p) (hps : p ∈ s) :
      L * rowWindowContribution r ≤
        dampedZeroKernel (1 + rowWindowA r / L) t (value p) +
        dampedZeroKernel (1 + rowWindowA r / L) t
          (1 - conj (value p)) := by
    have hh := scaled_window_pair_lower hL hc.1 (rowRadius_nonneg r) hc.2.2.1
      hc.2.2.2.1 rfl ⟨(hr p hps).le, hright p hps⟩ (hre p hps) (ht p hps)
    have hm := mul_le_mul_of_nonneg_left hmono hL0.le
    unfold rowWindowContribution
    nlinarith
  have hsum := Finset.sum_le_sum hlower
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcount : (s.card : ℝ) * rowWindowContribution r ≤ 1 / rowWindowA r + 277 / 1000 := by
    apply (mul_le_mul_iff_left₀ hL0).mp
    nlinarith
  by_contra hn
  have hn' : rowMultiplicity r + 1 ≤ s.card := by omega
  have hnR : (rowMultiplicity r : ℝ) + 1 ≤ (s.card : ℝ) := by exact_mod_cast hn'
  have hh := mul_le_mul_of_nonneg_right hnR hc.2.2.2.2.1.le
  linarith [hc.2.2.2.2.2]

theorem primitive_row_window_count (r : DensityRow) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (s : Finset (SymmetricCompletedZeroIndex χ)) {L lam t : ℝ}
    (hL : 25 ≤ L) (hlam : 0 ≤ lam) (hlam₁ : lam ≤ rowLambda r)
    (hheight : Real.log q + Real.log (max 1 |t|) ≤ L + 1 / 10)
    (hre : ∀ p ∈ s, 1 - lam / L ≤ (Hadamard.divisorZeroIndex₀_val p).re)
    (ht : ∀ p ∈ s, |t - (Hadamard.divisorZeroIndex₀_val p).im| ≤ rowRadius r / L) :
    s.card ≤ rowMultiplicity r := by
  have hc := row_window_certificate r
  have hL0 : 0 < L := by linarith
  have hmax : rowLambda r ≤ 1 / 2 := by cases r <;> norm_num [rowLambda]
  have hr (p) (hps : p ∈ s) : 1 / 2 < (Hadamard.divisorZeroIndex₀_val p).re := by
    have hh : lam / L < 1 / 2 := (div_lt_iff₀ hL0).mpr (by linarith)
    linarith [hre p hps]
  exact row_window_count_of_pair_budget r s Hadamard.divisorZeroIndex₀_val hL hlam hlam₁
    hre (fun p _ => (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hχ hp p).2.le)
    ht (primitive_window_mass_budget hχ hp s hr hL hc.1
      ((div_le_iff₀ hL0).mpr (by linarith [hc.2.1])) hheight)

end LiuWang.Proof.NearOneDensity
