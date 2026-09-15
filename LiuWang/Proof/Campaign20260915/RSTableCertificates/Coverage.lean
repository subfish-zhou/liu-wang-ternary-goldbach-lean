import LiuWang.Proof.Campaign20260915.RSTableCertificates.UpperRows

set_option autoImplicit false
set_option Elab.async false

namespace LiuWang.Proof.Campaign20260915.RSTableCertificates

open LiuWang.Proof.Campaign20260915.Totient

def Chain (C lo hi : ℚ) : List (Row × ℚ) → Prop
  | [] => hi < lo
  | (r, c) :: rest =>
    r.b ≤ lo ∧ 0 ≤ r.e ∧ r.e * c ≤ C ∧ Chain C c hi rest

instance (C lo hi : ℚ) (s : List (Row × ℚ)) : Decidable (Chain C lo hi s) := by
  induction s generalizing lo with
  | nil => unfold Chain; infer_instance
  | cons p ps ih => unfold Chain; exact instDecidableAnd

def lowerSegments : List (Row × ℚ) :=
  [(row18_4, 18.5), (row18_5, 18.7), (row18_7, 18.8),
   (row18_8, 19.5), (row19_5, 21), (row21, 28), (row28, 72),
   (row72, 225), (row225, 325), (row325, 350), (row350, 376)]

def upperSegments : List (Row × ℚ) :=
  [(row375, 575), (row575, 675), (row675, 750), (row750, 800),
   (row800, 825), (row825, 850), (row850, 875), (row875, 900),
   (row900, 925), (row925, 950), (row950, 975), (row975, 1000),
   (row1000, 1050), (row1050, 1100), (row1100, 1150),
   (row1150, 1200), (row1200, 1300), (row1300, 1500),
   (row1500, 2000), (row2000, 4500), (row4500, 4900), (row4900, 5001)]

theorem lower_chain : Chain 0.307 18.4 375 lowerSegments := by decide +kernel

theorem upper_chain : Chain 0.47 375 5000 upperSegments := by decide +kernel

theorem lower_valid : ∀ s ∈ lowerSegments, s.1.Valid := by
  simp only [lowerSegments, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨row18_4_valid, row18_5_valid, row18_7_valid, row18_8_valid,
    row19_5_valid, row21_valid, row28_valid, row72_valid, row225_valid,
    row325_valid, row350_valid⟩

theorem upper_valid : ∀ s ∈ upperSegments, s.1.Valid := by
  simp only [upperSegments, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨row375_valid, row575_valid, row675_valid, row750_valid,
    row800_valid, row825_valid, row850_valid, row875_valid, row900_valid,
    row925_valid, row950_valid, row975_valid, row1000_valid, row1050_valid,
    row1100_valid, row1150_valid, row1200_valid, row1300_valid, row1500_valid,
    row2000_valid, row4500_valid, row4900_valid⟩

theorem endpoint_nonmonotone : row4900.b < row5000.b ∧ row4900.e < row5000.e := by
  decide +kernel

noncomputable section

theorem chain_sound {C lo hi : ℚ} {segments : List (Row × ℚ)}
    (h : Chain C lo hi segments) {t : ℝ} (hl : (lo : ℝ) ≤ t) (hu : t ≤ (hi : ℝ)) :
    ∃ s ∈ segments, (s.1.b : ℝ) ≤ t ∧ t ≤ (s.2 : ℝ) ∧
      0 ≤ (s.1.e : ℝ) ∧ (s.1.e : ℝ) * s.2 ≤ (C : ℝ) := by
  induction segments generalizing lo with
  | nil =>
    have hh : (hi : ℝ) < lo := Rat.cast_lt.mpr h
    linarith
  | cons s rest ih =>
    obtain ⟨hb, he, hpay, hrest⟩ := h
    by_cases ht : t ≤ (s.2 : ℝ)
    · refine ⟨s, List.mem_cons_self, (Rat.cast_le.mpr hb).trans hl, ht,
        Rat.cast_nonneg.mpr he, ?_⟩
      exact_mod_cast hpay
    · obtain ⟨s', hs', hb', ht', he', hp'⟩ :=
        ih hrest (le_of_lt (lt_of_not_ge ht))
      exact ⟨s', List.mem_cons_of_mem _ hs', hb', ht', he', hp'⟩

theorem certified_cover {C lo hi : ℚ} {segments : List (Row × ℚ)}
    (hc : Chain C lo hi segments) (hv : ∀ s ∈ segments, s.1.Valid)
    (hlo : 0 < lo) {x : ℝ}
    (hx : Real.exp (lo : ℝ) ≤ x) (hx' : x ≤ Real.exp (hi : ℝ)) :
    ∃ s ∈ segments, s.1.Valid ∧ Real.exp (s.1.b : ℝ) ≤ x ∧
      (s.1.e : ℝ) ≤ (C : ℝ) / Real.log x := by
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hl := (Real.le_log_iff_exp_le hx0).mpr hx
  have hu := (Real.log_le_iff_le_exp hx0).mpr hx'
  obtain ⟨s, hs, hb, ht, he, hp⟩ := chain_sound hc hl hu
  refine ⟨s, hs, hv s hs, (Real.le_log_iff_exp_le hx0).mp hb, ?_⟩
  apply (le_div_iff₀ ((Rat.cast_pos.mpr hlo).trans_le hl)).mpr
  exact (mul_le_mul_of_nonneg_left ht he).trans hp

theorem lower_cover {x : ℝ} (hx : Real.exp (18.4 : ℝ) ≤ x)
    (hx' : x ≤ Real.exp (375 : ℝ)) :
    ∃ s ∈ lowerSegments, s.1.Valid ∧ Real.exp (s.1.b : ℝ) ≤ x ∧
      (s.1.e : ℝ) ≤ 0.307 / Real.log x := by
  simpa only [Rat.cast_ofScientific, Rat.cast_ofNat] using
    certified_cover lower_chain lower_valid (by norm_num) hx hx'

theorem upper_cover {x : ℝ} (hx : Real.exp (375 : ℝ) ≤ x)
    (hx' : x ≤ Real.exp (5000 : ℝ)) :
    ∃ s ∈ upperSegments, s.1.Valid ∧ Real.exp (s.1.b : ℝ) ≤ x ∧
      (s.1.e : ℝ) ≤ 0.47 / Real.log x := by
  simpa only [Rat.cast_ofScientific, Rat.cast_ofNat] using
    certified_cover upper_chain upper_valid (by norm_num) hx hx'

theorem budget_eq_original (m : ℕ) (b k : ℝ) :
    budget m b k =
      k / Real.sqrt (Real.exp b) +
        (0.0003647 * (m : ℝ) ^ 2 + 1.298 * m + 0.1592) /
          (((1 - ((m : ℝ) + 0.123) * b / (1748 * (m : ℝ) ^ 2)) * (m : ℝ) ^ 2) *
            (rsA ^ m * (Real.exp b) ^ (1 / 175 : ℝ))) := by
  have hs : Real.sqrt (Real.exp b) = Real.exp (b / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have hp : rsA ^ m * (Real.exp b) ^ (1 / 175 : ℝ) =
      Real.exp (9.99 * (m : ℝ) + b / 175) := by
    rw [rsA, ← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hs, hp]
  unfold budget
  rw [show -b / 2 = -(b / 2) by ring]
  simp only [Real.exp_neg, div_eq_mul_inv, mul_inv_rev]
  ring

theorem row_original_root {r : Row} (h : r.Valid) :
    2 * (r.k / Real.sqrt (Real.exp (r.b : ℝ)) +
      (0.0003647 * (r.m : ℝ) ^ 2 + 1.298 * r.m + 0.1592) /
        (((1 - ((r.m : ℝ) + 0.123) * r.b / (1748 * (r.m : ℝ) ^ 2)) * (r.m : ℝ) ^ 2) *
          (rsA ^ r.m * (Real.exp (r.b : ℝ)) ^ (1 / 175 : ℝ)))) ^
        (1 / ((r.m : ℝ) + 1)) ≤ (r.d : ℝ) := by
  rw [← budget_eq_original]
  exact row_root h

theorem cover_psi_of_moments {C lo hi : ℚ} {segments : List (Row × ℚ)}
    (hc : Chain C lo hi segments) (hv : ∀ s ∈ segments, s.1.Valid)
    (hlo : 0 < lo)
    (hpaid : ∀ s ∈ segments, (∑' p, rsZeroMoment s.1.m (s.1.b : ℝ) p) ≤
      budget s.1.m s.1.b s.1.k)
    {x : ℝ} (hx : Real.exp (lo : ℝ) ≤ x) (hx' : x ≤ Real.exp (hi : ℝ)) :
    x * (1 - (C : ℝ) / Real.log x) < Chebyshev.psi x ∧
      Chebyshev.psi x < x * (1 + (C : ℝ) / Real.log x) := by
  obtain ⟨s, hs, hvalid, hstart, he⟩ := certified_cover hc hv hlo hx hx'
  have hb := row_psi_of_actual_moment hvalid hstart ((hpaid s hs).trans (row_budget hvalid))
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  constructor <;> nlinarith

theorem lower_psi_of_moments
    (hpaid : ∀ s ∈ lowerSegments, (∑' p, rsZeroMoment s.1.m (s.1.b : ℝ) p) ≤
      budget s.1.m s.1.b s.1.k)
    {x : ℝ} (hx : Real.exp (18.4 : ℝ) ≤ x) (hx' : x ≤ Real.exp (375 : ℝ)) :
    x * (1 - 0.307 / Real.log x) < Chebyshev.psi x ∧
      Chebyshev.psi x < x * (1 + 0.307 / Real.log x) := by
  simpa only [Rat.cast_ofScientific, Rat.cast_ofNat] using
    cover_psi_of_moments lower_chain lower_valid (by norm_num) hpaid hx hx'

theorem upper_psi_of_moments
    (hpaid : ∀ s ∈ upperSegments, (∑' p, rsZeroMoment s.1.m (s.1.b : ℝ) p) ≤
      budget s.1.m s.1.b s.1.k)
    {x : ℝ} (hx : Real.exp (375 : ℝ) ≤ x) (hx' : x ≤ Real.exp (5000 : ℝ)) :
    x * (1 - 0.47 / Real.log x) < Chebyshev.psi x ∧
      Chebyshev.psi x < x * (1 + 0.47 / Real.log x) := by
  simpa only [Rat.cast_ofScientific, Rat.cast_ofNat] using
    cover_psi_of_moments upper_chain upper_valid (by norm_num) hpaid hx hx'

#print axioms lower_chain
#print axioms upper_chain
#print axioms lower_cover
#print axioms upper_cover
#print axioms endpoint_nonmonotone
#print axioms row_original_root
#print axioms lower_psi_of_moments
#print axioms upper_psi_of_moments

end
end LiuWang.Proof.Campaign20260915.RSTableCertificates
