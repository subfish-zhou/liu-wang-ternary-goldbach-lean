import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.ZeroTransport

/-! Open real part, closed height, and unchanged ordinary-L multiplicities in the original window. -/

set_option autoImplicit false
noncomputable section

open Complex Finset
open scoped Classical
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1

theorem nontrivialZeroIndex_zero {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (p : NontrivialZeroIndex chi) :
    chi.LFunction p.1 = 0 :=
  apply_eq_zero_of_analyticOrderNatAt_ne_zero
    (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le p.2.val) p.2.isLt))

theorem parityShift_eq_complex {q : ℕ} (chi : DirichletCharacter ℂ q) :
    (parityShift chi : ℂ) = (1 - chi (-1)) / 2 := by
  rcases chi.even_or_odd with hc | hc
  · unfold parityShift
    rw [show chi (-1) = 1 from hc]
    norm_num
  · unfold parityShift
    rw [show chi (-1) = -1 from hc]
    norm_num

def windowValues {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (alpha height : ℝ) : Finset ℂ :=
  (zeroValues chi alpha height).filter (fun rho => alpha < rho.re)

theorem mem_windowValues {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {alpha height : ℝ} {rho : ℂ} :
    rho ∈ windowValues chi alpha height ↔
      chi.LFunction rho = 0 ∧ rho.re ∈ Set.Ioo (0 : ℝ) 1 ∧
        alpha < rho.re ∧ |rho.im| ≤ height := by
  rw [windowValues, mem_filter, mem_zeroValues]
  constructor
  · rintro ⟨⟨hz, ⟨h0, h1, ht⟩, _⟩, hr⟩
    exact ⟨hz, ⟨h0, h1⟩, hr, ht⟩
  · rintro ⟨hz, ⟨h0, h1⟩, hr, ht⟩
    exact ⟨⟨hz, ⟨h0, h1, ht⟩, hr.le⟩, hr⟩

theorem windowValues_eq_primitive {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor] (hc : chi ≠ 1)
    (alpha height : ℝ) :
    windowValues chi alpha height = windowValues chi.primitiveCharacter alpha height := by
  unfold windowValues
  rw [zeroValues_eq_primitive chi hc]

theorem window_sum_eq_primitive {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor] (hc : chi ≠ 1)
    (alpha height : ℝ) (w : ℂ → ℝ) :
    (∑ rho ∈ windowValues chi alpha height, (analyticOrderNatAt chi.LFunction rho : ℝ) * w rho) =
      ∑ rho ∈ windowValues chi.primitiveCharacter alpha height,
        (analyticOrderNatAt chi.primitiveCharacter.LFunction rho : ℝ) * w rho := by
  rw [windowValues_eq_primitive chi hc]
  apply sum_congr rfl
  intro rho hr
  rw [analyticOrderNatAt_LFunction_eq_primitive chi hc (mem_windowValues.mp hr).2.1.1]

def windowCount {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (alpha height : ℝ) : ℕ :=
  ∑ rho ∈ windowValues chi alpha height, analyticOrderNatAt chi.LFunction rho

theorem windowCount_eq_primitive {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor] (hc : chi ≠ 1)
    (alpha height : ℝ) :
    windowCount chi alpha height = windowCount chi.primitiveCharacter alpha height := by
  unfold windowCount
  rw [windowValues_eq_primitive chi hc]
  apply sum_congr rfl
  intro rho hr
  exact analyticOrderNatAt_LFunction_eq_primitive chi hc (mem_windowValues.mp hr).2.1.1

theorem windowCount_mono_height {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (alpha : ℝ) {height height1 : ℝ}
    (hh : height ≤ height1) :
    windowCount chi alpha height ≤ windowCount chi alpha height1 := by
  apply sum_le_sum_of_subset
  intro rho hr
  obtain ⟨hz, hstrip, ha, ht⟩ := mem_windowValues.mp hr
  exact mem_windowValues.mpr ⟨hz, hstrip, ha, ht.trans hh⟩

def originalCutoff (x : ℝ) : ℝ := 1 - 1 / (9.645908801 * Real.log x)

theorem original_window_sum_transport {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor] (hc : chi ≠ 1)
    (x : ℝ) (w : ℂ → ℝ) :
    (∑ rho ∈ windowValues chi (originalCutoff x) (x / q),
        (analyticOrderNatAt chi.LFunction rho : ℝ) * w rho) =
      ∑ rho ∈ windowValues chi.primitiveCharacter (originalCutoff x) (x / q),
        (analyticOrderNatAt chi.primitiveCharacter.LFunction rho : ℝ) * w rho :=
  window_sum_eq_primitive chi hc (originalCutoff x) (x / q) w

theorem original_window_count_le_conductor {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor] (hc : chi ≠ 1)
    {x : ℝ} (hx : 10 ≤ x) :
    windowCount chi (originalCutoff x) (x / q) ≤
      windowCount chi.primitiveCharacter (originalCutoff x) (x / chi.conductor) := by
  rw [windowCount_eq_primitive chi hc]
  apply windowCount_mono_height
  apply div_le_div_of_nonneg_left (by linarith)
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero chi.conductor_ne_zero))
  exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi

end LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
