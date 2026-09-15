import LiuWang.Proof.EffectiveLValue.GaussField
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The parity-independent Abel--Gauss logarithm formula

The limiting value is the original character's `LFunction 1`. Nonprincipality
removes the zero term at the logarithmic singularity; primitivity and real values
are needed only for the Fourier identity. No parity assumption is used.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.EffectiveLValue

open Complex Finset Filter Topology

variable {r : ℕ} [NeZero r]

theorem primitiveCharacter_ne_one (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hr : 1 < r) : χ ≠ 1 := by
  intro h
  have hc := hprimitive
  rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hc
  omega

theorem realCharacter_zero (χ : Interfaces.Character r) (hne : χ ≠ 1) : χ 0 = 0 := by
  simpa using DirichletLConditionalValueSeries.character_nat_zero_of_ne_one χ hne

theorem realCharacter_gauss_fourier (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (n : ℕ) :
    characterGaussSum χ * χ n =
      ∑ a : ZMod r, χ a * ZMod.stdAddChar a ^ n := by
  have h := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hprimitive (n : ZMod r)
  rw [(MulChar.isQuadratic_iff_sq_eq_one.mpr hreal).inv] at h
  simpa [characterGaussSum, gaussSum, AddChar.mulShift_apply,
    ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm] using h.symm

theorem realCharacter_tendsto_abel (χ : Interfaces.Character r) (hne : χ ≠ 1) :
    Tendsto (fun x : ℝ ↦ ∑' n : ℕ, (χ n / n) * (x : ℂ) ^ n)
      (𝓝[<] 1) (𝓝 (χ.LFunction 1)) := by
  have h := DirichletLConditionalValueSeries.tendsto_sum_range_orderedValueSeries
    χ hne 1 (by simp)
  rw [DirichletLConditionalValueSeries.orderedValueSeries_eq_LFunction_of_re_pos] at h
  simp only [DirichletLConditionalValueSeries.cpowWeight_nat_eq, cpow_neg_one,
    inv_mul_eq_div] at h
  exact (tendsto_map'_iff.mp (Complex.tendsto_tsum_powerSeries_nhdsWithin_lt h))

theorem realCharacter_abel_log (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) {x : ℝ} (hx : |x| < 1) :
    characterGaussSum χ * (∑' n : ℕ, (χ n / n) * (x : ℂ) ^ n) =
      ∑ a : ZMod r, χ a * (-Complex.log (1 - x * ZMod.stdAddChar a)) := by
  have hs (a : ZMod r) :
      HasSum (fun n : ℕ ↦ χ a * (((x : ℂ) * ZMod.stdAddChar a) ^ n / n))
        (χ a * (-Complex.log (1 - x * ZMod.stdAddChar a))) :=
    (Complex.hasSum_taylorSeries_neg_log (by
      simpa [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe] using hx)).mul_left _
  have ht := hasSum_sum (s := (univ : Finset (ZMod r))) (fun a _ ↦ hs a)
  have he (n : ℕ) :
      (∑ a : ZMod r, χ a * (((x : ℂ) * ZMod.stdAddChar a) ^ n / n)) =
        characterGaussSum χ * ((χ n / n) * (x : ℂ) ^ n) := by
    calc
      _ = (∑ a : ZMod r, χ a * ZMod.stdAddChar a ^ n) / n * (x : ℂ) ^ n := by
        rw [sum_div, sum_mul]
        apply sum_congr rfl
        intro a _
        rw [mul_pow]
        ring
      _ = _ := by rw [← realCharacter_gauss_fourier χ hprimitive hreal]; ring
  simp_rw [he] at ht
  rw [← ht.tsum_eq, tsum_mul_left]

theorem stdAddChar_sub_one_mem_slitPlane (a : ZMod r) (ha : a ≠ 0) :
    1 - ZMod.stdAddChar a ∈ Complex.slitPlane := by
  have hn : ‖ZMod.stdAddChar a‖ = 1 := (ZMod.toCircle a).norm_coe
  have hne : ZMod.stdAddChar a ≠ 1 := by
    intro h
    apply ha
    exact ZMod.injective_stdAddChar
      (h.trans (ZMod.stdAddChar (N := r)).map_zero_eq_one.symm)
  have hre : (ZMod.stdAddChar a).re < 1 := by
    have hle := Complex.re_le_norm (ZMod.stdAddChar a)
    rw [hn] at hle
    refine lt_of_le_of_ne hle ?_
    intro h
    apply hne
    apply Complex.ext h
    have hh := Complex.sq_norm (ZMod.stdAddChar a)
    rw [hn, Complex.normSq_apply, h] at hh
    simp only [one_im]
    nlinarith [sq_nonneg (ZMod.stdAddChar a).im]
  apply Complex.mem_slitPlane_iff.mpr ∘ Or.inl
  simpa using sub_pos.mpr hre

theorem realCharacter_gauss_mul_LFunction_one_log (χ : Interfaces.Character r)
    (hprimitive : χ.IsPrimitive) (hreal : χ ^ 2 = 1) (hne : χ ≠ 1) :
    characterGaussSum χ * χ.LFunction 1 =
      ∑ a : ZMod r, χ a * (-Complex.log (1 - ZMod.stdAddChar a)) := by
  have hl := (realCharacter_tendsto_abel χ hne).const_mul (characterGaussSum χ)
  have hr : Tendsto
      (fun x : ℝ ↦ ∑ a : ZMod r, χ a * (-Complex.log (1 - x * ZMod.stdAddChar a)))
      (𝓝[<] 1)
      (𝓝 (∑ a : ZMod r, χ a * (-Complex.log (1 - ZMod.stdAddChar a)))) := by
    apply tendsto_finsetSum
    intro a _
    by_cases ha : a = 0
    · subst a
      simp only [realCharacter_zero χ hne, zero_mul]
      exact tendsto_const_nhds
    · have hc : ContinuousAt (fun x : ℝ ↦ Complex.log (1 - x * ZMod.stdAddChar a)) 1 := by
        apply ContinuousAt.clog
        · fun_prop
        · simpa using stdAddChar_sub_one_mem_slitPlane a ha
      simpa using (hc.neg.const_mul (χ a)).tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhds_unique hl
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))]
    with x hx hx'
  exact (realCharacter_abel_log χ hprimitive hreal (abs_lt.mpr ⟨hx', hx⟩)).symm

end LiuWang.Proof.EffectiveLValue
