import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.RationalIntervals

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates

def center16 : RationalInterval := ⟨2.7725887212, 2.7725887232⟩
def center20 : RationalInterval := ⟨2.9957322729, 2.9957322742⟩

def endpointBox (center z root : RationalInterval) : Fin 4 → RationalInterval :=
  ![center, ⟨1 / center.hi, 1 / center.lo⟩, z, root]

def firstLeft : Fin 4 → RationalInterval :=
  endpointBox center16 ⟨-4.487074537, -4.487074533⟩ ⟨6.81292069, 6.81292070⟩
def firstRight : Fin 4 → RationalInterval :=
  endpointBox center16 ⟨2, 2⟩ ⟨20.08553691, 20.08553694⟩
def secondLeft : Fin 4 → RationalInterval :=
  endpointBox center20 ⟨-2, -2⟩ ⟨20.08553691, 20.08553694⟩
def secondRight : Fin 4 → RationalInterval :=
  endpointBox center20 ⟨3.025850926, 3.025850934⟩ ⟨46.41588833, 46.41588834⟩

theorem log_center16 : center16.Contains (Real.log 16) := by
  change (2.7725887212 : ℝ) ≤ Real.log 16 ∧ Real.log 16 ≤ 2.7725887232
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  constructor <;> norm_num <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

theorem log_center20 : center20.Contains (Real.log 20) := by
  change (2.9957322729 : ℝ) ≤ Real.log 20 ∧ Real.log 20 ≤ 2.9957322742
  rw [show (20 : ℝ) = 2 ^ 2 * 5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  constructor <;> norm_num <;>
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9]

theorem sixth_root_box {x l u : ℝ} (hx : 0 ≤ x) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlx : l ^ 6 ≤ x) (hxu : x ≤ u ^ 6) :
    l ≤ x ^ (1 / 6 : ℝ) ∧ x ^ (1 / 6 : ℝ) ≤ u := by
  have he : (x ^ (1 / 6 : ℝ)) ^ 6 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  exact ⟨(pow_le_pow_iff_left₀ hl (Real.rpow_nonneg hx _) (by decide : 6 ≠ 0)).mp
      (by rw [he]; exact hlx),
    (pow_le_pow_iff_left₀ (Real.rpow_nonneg hx _) hu (by decide : 6 ≠ 0)).mp
      (by rw [he]; exact hxu)⟩

theorem root_first :
    (6.81292069 : ℝ) ≤ (100000 : ℝ) ^ (1 / 6 : ℝ) ∧
      (100000 : ℝ) ^ (1 / 6 : ℝ) ≤ 6.81292070 :=
  sixth_root_box (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem root_last :
    (46.41588833 : ℝ) ≤ (10000000000 : ℝ) ^ (1 / 6 : ℝ) ∧
      (10000000000 : ℝ) ^ (1 / 6 : ℝ) ≤ 46.41588834 :=
  sixth_root_box (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem root_middle :
    (20.08553691 : ℝ) ≤ Real.exp 18 ^ (1 / 6 : ℝ) ∧
      Real.exp 18 ^ (1 / 6 : ℝ) ≤ 20.08553694 := by
  have hl := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 3
  have hu := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
  rw [← Real.exp_nat_mul] at hl hu
  rw [← Real.exp_mul]
  norm_num only at hl hu ⊢
  constructor <;> linarith

theorem endpointBox_contains {c z r : RationalInterval} {t x : ℝ}
    (hc : c.Contains (Real.log t)) (hc0 : 0 < c.lo)
    (hz : z.Contains (Real.log x - t)) (hr : r.Contains (x ^ (1 / 6 : ℝ))) :
    ∀ i, (endpointBox c z r i).Contains
      (![Real.log t, 1 / Real.log t, Real.log x - t, x ^ (1 / 6 : ℝ)] i) := by
  intro i
  fin_cases i
  · exact hc
  · change ((1 / c.hi : ℚ) : ℝ) ≤ 1 / Real.log t ∧
      1 / Real.log t ≤ ((1 / c.lo : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_one]
    have hlo : (0 : ℝ) < c.lo := by exact_mod_cast hc0
    exact ⟨one_div_le_one_div_of_le (hlo.trans_le hc.1) hc.2,
      one_div_le_one_div_of_le hlo hc.1⟩
  · exact hz
  · exact hr

theorem firstLeft_contains : ∀ i, (firstLeft i).Contains
    (![Real.log 16, 1 / Real.log 16, Real.log 100000 - 16, (100000 : ℝ) ^ (1 / 6 : ℝ)] i) := by
  apply endpointBox_contains log_center16 (by norm_num [center16])
  · norm_num only [RationalInterval.Contains, Rat.cast_neg, Rat.cast_ofScientific]
    rw [show (100000 : ℝ) = (2 * 5) ^ 5 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    constructor <;> norm_num <;>
      linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9]
  · simpa only [RationalInterval.Contains, Rat.cast_ofScientific] using root_first

theorem firstRight_contains : ∀ i, (firstRight i).Contains
    (![Real.log 16, 1 / Real.log 16, Real.log (Real.exp 18) - 16, Real.exp 18 ^ (1 / 6 : ℝ)] i) := by
  apply endpointBox_contains log_center16 (by norm_num [center16])
  · norm_num [RationalInterval.Contains, Real.log_exp]
  · simpa only [RationalInterval.Contains, Rat.cast_ofScientific] using root_middle

theorem secondLeft_contains : ∀ i, (secondLeft i).Contains
    (![Real.log 20, 1 / Real.log 20, Real.log (Real.exp 18) - 20, Real.exp 18 ^ (1 / 6 : ℝ)] i) := by
  apply endpointBox_contains log_center20 (by norm_num [center20])
  · norm_num [RationalInterval.Contains, Real.log_exp]
  · simpa only [RationalInterval.Contains, Rat.cast_ofScientific] using root_middle

theorem secondRight_contains : ∀ i, (secondRight i).Contains
    (![Real.log 20, 1 / Real.log 20, Real.log 10000000000 - 20, (10000000000 : ℝ) ^ (1 / 6 : ℝ)] i) := by
  apply endpointBox_contains log_center20 (by norm_num [center20])
  · norm_num only [RationalInterval.Contains, Rat.cast_ofScientific]
    rw [show (10000000000 : ℝ) = (2 * 5) ^ 10 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num)]
    constructor <;> norm_num <;>
      linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9]
  · simpa only [RationalInterval.Contains, Rat.cast_ofScientific] using root_last

def highRationalUpper : ℚ :=
  ((cubicEndpointExpression 16).interval firstRight).hi -
    ((cubicEndpointExpression 16).interval firstLeft).lo +
    ((cubicEndpointExpression 20).interval secondRight).hi -
    ((cubicEndpointExpression 20).interval secondLeft).lo

theorem highRationalUpper_le : highRationalUpper ≤ 8794 := by
  decide +kernel

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates
