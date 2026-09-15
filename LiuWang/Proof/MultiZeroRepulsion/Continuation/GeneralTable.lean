import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralMother

/-! Exact continuous-parameter certificates for Table 1, on the full ordinary nonprincipal family. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

inductive GeneralTableRow
  | r10367089 | r12 | r13 | r14 | r15 | r16 | r17 | r18 | r19 | r20 | r206 | r2067
  deriving DecidableEq

def generalTableFirst : GeneralTableRow → ℝ
  | .r10367089 => 10367089 / 100000000
  | .r12 => 12 / 100
  | .r13 => 13 / 100
  | .r14 => 14 / 100
  | .r15 => 15 / 100
  | .r16 => 16 / 100
  | .r17 => 17 / 100
  | .r18 => 18 / 100
  | .r19 => 19 / 100
  | .r20 => 20 / 100
  | .r206 => 206 / 1000
  | .r2067 => 2067 / 10000

def generalTableSecond : GeneralTableRow → ℝ
  | .r10367089 => 3534 / 10000
  | .r12 => 3221 / 10000
  | .r13 => 3050 / 10000
  | .r14 => 2891 / 10000
  | .r15 => 2743 / 10000
  | .r16 => 2605 / 10000
  | .r17 => 2477 / 10000
  | .r18 => 2356 / 10000
  | .r19 => 2242 / 10000
  | .r20 => 2135 / 10000
  | .r206 => 2074 / 10000
  | .r2067 => 2067 / 10000

def generalTableA : GeneralTableRow → ℝ
  | .r10367089 => 473 / 1000
  | .r12 => 482 / 1000
  | .r13 => 486 / 1000
  | .r14 => 489 / 1000
  | .r15 => 492 / 1000
  | .r16 => 495 / 1000
  | .r17 => 496 / 1000
  | .r18 => 498 / 1000
  | .r19 | .r20 | .r206 | .r2067 => 499 / 1000

theorem generalTable_certificate (r : GeneralTableRow) :
    0 < generalTableA r ∧ generalTableA r ≤ 1 / 2 ∧
    0 ≤ generalTableFirst r ∧ generalTableFirst r ≤ generalTableSecond r ∧
    generalTableSecond r ≤ generalTableA r ∧
    1 / generalTableA r + 3 * (691 / 2500 : ℝ) <
      1 / (generalTableA r + generalTableFirst r) +
      1 / (generalTableA r + generalTableSecond r) := by
  cases r <;> norm_num [generalTableA, generalTableFirst, generalTableSecond]

theorem generalTable_parameters (r : GeneralTableRow) {x : ℝ} (hx : 8000000000 ≤ x) :
    1 < 1 + generalTableA r / Real.log x ∧
    1 + generalTableA r / Real.log x ≤ 23 / 20 ∧
    1 / 2 ≤ 1 - generalTableSecond r / Real.log x := by
  have h := generalTable_certificate r
  have hL := source_log_lower hx
  have hL0 : 0 < Real.log x := by linarith
  have hpos := div_pos h.1 hL0
  have hsmall : generalTableA r / Real.log x ≤ 3 / 20 := by
    apply (div_le_iff₀ hL0).mpr
    linarith [h.2.1]
  have hsecond : generalTableSecond r / Real.log x ≤ 1 / 2 := by
    apply (div_le_iff₀ hL0).mpr
    linarith [h.2.1, h.2.2.2.2.1]
  exact ⟨by linarith, by linarith, by linarith⟩

theorem generalTable_scalar (r : GeneralTableRow) {x beta gamma : ℝ} (hx : 8000000000 ≤ x)
    (hb : beta < 1) (hg : gamma < 1)
    (hl1 : (1 - beta) * Real.log x ≤ generalTableFirst r)
    (hl2 : (1 - gamma) * Real.log x < generalTableSecond r) :
    let sigma := 1 + generalTableA r / Real.log x
    1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log x <
      1 / (sigma - beta) + 1 / (sigma - gamma) := by
  dsimp only
  have h := generalTable_certificate r
  have hL : 0 < Real.log x := by linarith [source_log_lower hx]
  have hs := (generalTable_parameters r hx).1
  have hp : 0 < generalTableA r + generalTableFirst r := by linarith [h.1, h.2.2.1]
  have hr : 0 < generalTableA r + generalTableSecond r := by
    linarith [h.1, h.2.2.1, h.2.2.2.1]
  have he : (1 + generalTableA r / Real.log x - 1) * Real.log x = generalTableA r := by
    field_simp
    ring
  have he' : 1 / (1 + generalTableA r / Real.log x - 1) = Real.log x / generalTableA r := by
    field_simp
    ring
  have hlp : Real.log x / (generalTableA r + generalTableFirst r) ≤
      1 / (1 + generalTableA r / Real.log x - beta) := by
    apply (div_le_div_iff₀ hp (by linarith)).mpr
    nlinarith
  have hlr : Real.log x / (generalTableA r + generalTableSecond r) <
      1 / (1 + generalTableA r / Real.log x - gamma) := by
    apply (div_lt_div_iff₀ hr (by linarith)).mpr
    nlinarith
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL.le
  have hh := mul_lt_mul_of_pos_right h.2.2.2.2.2 hL
  rw [he']
  simp only [div_eq_mul_inv] at hlp hlr hh ⊢
  nlinarith only [hlp, hlr, hk, hh]

theorem generalTable_nonprincipal (row : GeneralTableRow) {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q (1 / 2) (x / q))
    (hp : p.character ≠ 1) (hr : r.character ≠ 1)
    (hne : p ≠ r) (hnc : p ≠ conjugateSlot r)
    (hl1 : (1 - p.value.re) * Real.log x ≤ generalTableFirst row) :
    generalTableSecond row ≤ (1 - r.value.re) * Real.log x := by
  by_contra hn
  have hl2 := lt_of_not_ge hn
  have hL : 0 < Real.log x := by linarith [source_log_lower hx]
  have hc := generalTable_certificate row
  have hg1 : 1 - p.value.re ≤ (1 + generalTableA row / Real.log x) - 1 := by
    have hh : (1 - p.value.re) * Real.log x ≤ generalTableA row :=
      hl1.trans (hc.2.2.2.1.trans hc.2.2.2.2.1)
    have he := (le_div_iff₀ hL).mpr hh
    linarith
  have hg2 : 1 - r.value.re ≤ (1 + generalTableA row / Real.log x) - 1 := by
    have hh : (1 - r.value.re) * Real.log x ≤ generalTableA row := hl2.le.trans hc.2.2.2.2.1
    have he := (le_div_iff₀ hL).mpr hh
    linarith
  have hs := generalTable_parameters row hx
  have hm := general_nonprincipal_mother hx hq hs.1 hs.2.1 le_rfl p r hne hnc hp hr hg1 hg2
  have hb := generalTable_scalar row hx (mem_strictZeroValues.mp p.zero_mem).2.2.2.1
    (mem_strictZeroValues.mp r.zero_mem).2.2.2.1 hl1 hl2
  exact (not_lt_of_ge hm) hb

end LiuWang.Proof.MultiZeroRepulsion.Continuation
