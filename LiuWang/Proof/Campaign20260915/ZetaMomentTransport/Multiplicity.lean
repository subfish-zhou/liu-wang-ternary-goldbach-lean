import LiuWang.Proof.Campaign20260915.ZetaWinding.PositiveCount

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex
open scoped ComplexConjugate
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.ZetaMomentTransport

abbrev ZetaZero := {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}

def xiZetaValue (p : RiemannXiDivisorZeroIndex) : ZetaZero :=
  ⟨riemannXiDivisorZeroValue p, by
    have hr := riemannXiDivisorZeroValue_re_mem_Ioo p
    refine ⟨?_, hr⟩
    exact (xi_zero_iff_zeta_zero (by linarith [hr.1]) (by
      intro he
      have := hr.2
      simp [he] at this)).mp (riemannXiDivisorZeroValue_eq_zero p)⟩

theorem xiZetaValue_surjective : Function.Surjective xiZetaValue := by
  intro z
  obtain ⟨p, hp⟩ := exists_xi_index_of_zeta_zero z.property.2.1 z.property.1
  exact ⟨p, Subtype.ext hp⟩

theorem zetaZero_im_ne_zero (z : ZetaZero) : (z : ℂ).im ≠ 0 := by
  intro he
  exact zeta_ne_zero_closed_height_one z.property.2.1 z.property.2.2
    (by simp [he]) z.property.1

def zetaWeight (f : ℂ → ℝ) (z : ZetaZero) : ℝ :=
  (analyticOrderNatAt riemannZeta (z : ℂ) : ℝ) * f z

def positiveZetaWeight (f : ℂ → ℝ) (z : ZetaZero) : ℝ :=
  if 0 < (z : ℂ).im then zetaWeight f z else 0

theorem xi_fiber_tsum (f : ℂ → ℝ) (z : ZetaZero) :
    (∑' p : xiZetaValue ⁻¹' {z},
      f (riemannXiDivisorZeroValue p)) = zetaWeight f z := by
  classical
  rw [tsum_subtype (xiZetaValue ⁻¹' {z}) (fun p => f (riemannXiDivisorZeroValue p))]
  have he (p : RiemannXiDivisorZeroIndex) :
      xiZetaValue p = z ↔ riemannXiDivisorZeroValue p = (z : ℂ) :=
    Subtype.ext_iff
  simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, he]
  rw [tsum_eq_sum (s := Complex.Hadamard.divisorZeroIndex₀_fiberFinset riemannXi z) (by
    intro p hp
    have hn : riemannXiDivisorZeroValue p ≠ (z : ℂ) := by
      simpa only [Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset] using hp
    simp [hn])]
  have hsum :
      (∑ p ∈ Complex.Hadamard.divisorZeroIndex₀_fiberFinset riemannXi z,
        if riemannXiDivisorZeroValue p = (z : ℂ) then
          f (riemannXiDivisorZeroValue p) else 0) =
      ∑ _p ∈ Complex.Hadamard.divisorZeroIndex₀_fiberFinset riemannXi z, f z := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpv : riemannXiDivisorZeroValue p = (z : ℂ) :=
      (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset _ _ _).mp hp
    simp [hpv]
  rw [hsum, Finset.sum_const, nsmul_eq_mul,
    Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
      differentiable_riemannXi (by
        intro he
        have := z.property.2.1
        simp [he] at this)]
  have ho := analyticOrderNatAt_xi_eq_principal (q := 1) z.property.2.1 (by
    intro he
    have := z.property.2.2
    simp [he] at this)
  simpa only [zetaWeight, DirichletCharacter.LFunction_modOne_eq] using
    congrArg (fun n : ℕ => (n : ℝ) * f z) ho

theorem hasSum_zetaWeight {f : ℂ → ℝ}
    (hf : Summable (fun p => f (riemannXiDivisorZeroValue p))) :
    HasSum (zetaWeight f) (∑' p, f (riemannXiDivisorZeroValue p)) := by
  have h := hf.hasSum.tsum_fiberwise xiZetaValue
  simpa only [xi_fiber_tsum] using h

theorem tsum_xi_eq_zetaWeight {f : ℂ → ℝ}
    (hf : Summable (fun p => f (riemannXiDivisorZeroValue p))) :
    (∑' p, f (riemannXiDivisorZeroValue p)) = ∑' z, zetaWeight f z :=
  (hasSum_zetaWeight hf).tsum_eq.symm

theorem positive_weight_transport {f : ℂ → ℝ}
    (hf : Summable (fun p => f (riemannXiDivisorZeroValue p))) :
    (∑' p : RiemannXiDivisorZeroIndex,
      if 0 < (riemannXiDivisorZeroValue p).im then
        f (riemannXiDivisorZeroValue p) else 0) =
      ∑' z, positiveZetaWeight f z := by
  classical
  have hp := hf.indicator {p | 0 < (riemannXiDivisorZeroValue p).im}
  have ht := tsum_xi_eq_zetaWeight (f := fun z => if 0 < z.im then f z else 0) hp
  simpa only [zetaWeight, positiveZetaWeight, mul_ite, mul_zero] using ht

theorem zetaClosedValues_eq_xiWindowValues (A : ℝ) :
    zetaClosedValues A = xiWindowValues 0 A := by
  classical
  ext z
  rw [mem_zetaClosedValues, mem_xiWindowValues]
  constructor
  · rintro ⟨hz, h0, h1, hA⟩
    exact ⟨(xi_zero_iff_zeta_zero (by linarith) (by
      intro he
      simp [he] at h1)).mpr hz, by simpa using hA⟩
  · intro hz
    obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp (mem_xiWindowValues.mpr hz)
    have hr := (xiZetaValue p).property
    exact ⟨hpv ▸ hr.1, hpv ▸ hr.2.1, hpv ▸ hr.2.2,
      by simpa only [sub_zero] using hz.2⟩

theorem sum_xiWindow_eq_zeta (A : ℝ) (f : ℂ → ℝ) :
    (∑ p ∈ xiWindow 0 A, f (riemannXiDivisorZeroValue p)) =
      ∑ z ∈ zetaClosedValues A, (analyticOrderNatAt riemannZeta z : ℝ) * f z := by
  have hs := congrArg Complex.re (sum_xiWindow_values 0 A (fun z => (f z : ℂ)))
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re,
    Complex.ofReal_re, Complex.natCast_im, Complex.ofReal_im, mul_zero, sub_zero] at hs
  rw [← hs, ← zetaClosedValues_eq_xiWindowValues]
  apply Finset.sum_congr rfl
  intro z hz
  have hr := mem_zetaClosedValues.mp hz
  have ho := analyticOrderNatAt_xi_eq_principal (q := 1) hr.2.1 (by
    intro he
    have := hr.2.2.1
    simp [he] at this)
  simp only [DirichletCharacter.LFunction_modOne_eq] at ho
  rw [ho]

theorem low_window_iff_zetaClosedValues (A : ℝ) :
    (∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| ≤ A →
        (riemannXiDivisorZeroValue p).re = 1 / 2) ↔
    (∀ z ∈ zetaClosedValues A, z.re = 1 / 2) := by
  constructor
  · intro h z hz
    have hr := mem_zetaClosedValues.mp hz
    obtain ⟨p, hp⟩ := exists_xi_index_of_zeta_zero hr.2.1 hr.1
    simpa only [hp] using h p (by simpa only [hp] using hr.2.2.2)
  · intro h p hp
    exact h _ (mem_zetaClosedValues.mpr ⟨(xiZetaValue p).property.1,
      (xiZetaValue p).property.2.1, (xiZetaValue p).property.2.2, hp⟩)

theorem low_window_iff_positiveValues (A : ℝ) :
    (∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| ≤ A →
        (riemannXiDivisorZeroValue p).re = 1 / 2) ↔
    (∀ z ∈ positiveValues A, z.re = 1 / 2) := by
  rw [low_window_iff_zetaClosedValues]
  constructor
  · exact fun h z hz => h z (Finset.mem_filter.mp hz).1
  · intro h z hz
    have hr := mem_zetaClosedValues.mp hz
    by_cases hi : 0 < z.im
    · exact h z (Finset.mem_filter.mpr ⟨hz, hi⟩)
    · have hn : z.im < 0 :=
        lt_of_le_of_ne (not_lt.mp hi) (zetaZero_im_ne_zero ⟨z, hr.1, hr.2.1, hr.2.2.1⟩)
      have hc : conj z ∈ positiveValues A := mem_positiveValues.mpr
        ⟨by rw [riemannZeta_conj, hr.1, map_zero],
          by simpa using hr.2.1, by simpa using hr.2.2.1,
          by simpa using neg_pos.mpr hn, by simpa [abs_of_neg hn] using hr.2.2.2⟩
      simpa using h (conj z) hc

#print axioms xi_fiber_tsum
#print axioms hasSum_zetaWeight
#print axioms sum_xiWindow_eq_zeta
#print axioms low_window_iff_positiveValues

end LiuWang.Proof.Campaign20260915.ZetaMomentTransport
