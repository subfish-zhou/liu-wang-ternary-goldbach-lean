import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.QuadraticArithmetic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries
open LiuWang.Proof.SourceRoute.MajorOrdinary
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart

namespace LiuWang.Proof.Campaign20260915.MajorArc

theorem third_weight_eq_sixth_mul {q : ℕ} (hq : 0 < q) :
    totientWeight q (1 / 3) = totientWeight q (1 / 6) * (q : ℝ) ^ (1 / 6 : ℝ) := by
  unfold totientWeight
  rw [show (1 / 3 : ℝ) = 1 / 6 + 1 / 6 by norm_num,
    Real.rpow_add (Nat.cast_pos.mpr hq)]
  ring

def thirdNumerator : Block → ℕ
  | .leaf r => r.upper1 * r.root
  | .branch l r => thirdNumerator l + thirdNumerator r

theorem row_third_bound {r : Row} (hr : r.valid = true) :
    totientWeight r.q (1 / 3) ≤ (r.upper1 * r.root : ℕ) / (denominator : ℝ) ^ 2 := by
  obtain ⟨hq, _, hm, h1, _⟩ := r.sound hr
  by_cases hz : r.mu = 0
  · simp only [totientWeight, hm, hz, Int.cast_zero, abs_zero, zero_mul, zero_div]
    positivity
  · have hv := hr
    simp only [Row.valid, Bool.and_eq_true, beq_iff_eq, if_neg hz,
      decide_eq_true_eq] at hv
    have hroot := sixth_root_bound (by norm_num [denominator] : 0 < denominator)
      hv.2.1.1.2
    rw [third_weight_eq_sixth_mul hq]
    have h := mul_le_mul h1 hroot (Real.rpow_nonneg (Nat.cast_nonneg r.q) _)
      (by positivity : 0 ≤ (r.upper1 : ℝ) / denominator)
    convert! h using 1
    push_cast
    ring

theorem block_third_bound {b : Block} (hb : b.valid = true) :
    (∑ q ∈ Finset.Ico b.first b.stop, totientWeight q (1 / 3)) ≤
      (thirdNumerator b : ℝ) / (denominator : ℝ) ^ 2 := by
  induction b with
  | leaf r => simpa [Block.first, Block.stop, thirdNumerator] using row_third_bound hb
  | branch l r hl hr =>
    simp only [Block.valid, Bool.and_eq_true, beq_iff_eq] at hb
    have hleft := hl hb.1.1
    have hright := hr hb.1.2
    have hls := Block.sound hb.1.1
    have hrs := Block.sound hb.1.2
    rw [← hb.2] at hright hrs
    change (∑ q ∈ Finset.Ico l.first r.stop, totientWeight q (1 / 3)) ≤ _
    rw [← Finset.sum_Ico_consecutive _ hls.1 hrs.1]
    simpa only [thirdNumerator, Nat.cast_add, add_div] using add_le_add hleft hright

theorem third_head_through_32 :
    (∑ q ∈ Finset.Ico 1 33, totientWeight q (1 / 3)) ≤ 3.68 := by
  apply (block_third_bound (b := data0000) (by decide +kernel)).trans
  norm_num [thirdNumerator, data0000, denominator]

theorem sixth_root_tangent {q : ℕ} {y : ℝ} (hy : 0 < y) :
    (q : ℝ) ^ (1 / 6 : ℝ) ≤ (5 * y ^ 6 + q) / (6 * y ^ 5) := by
  let x := (q : ℝ) ^ (1 / 6 : ℝ)
  have hx : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hx6 : x ^ 6 = q := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
    norm_num
  have hp : 0 ≤ (x - y) ^ 2 *
      (x ^ 4 + 2 * y * x ^ 3 + 3 * y ^ 2 * x ^ 2 + 4 * y ^ 3 * x + 5 * y ^ 4) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have he : (x - y) ^ 2 *
      (x ^ 4 + 2 * y * x ^ 3 + 3 * y ^ 2 * x ^ 2 + 4 * y ^ 3 * x + 5 * y ^ 4) =
      x ^ 6 - 6 * y ^ 5 * x + 5 * y ^ 6 := by ring
  rw [he, hx6] at hp
  apply (le_div_iff₀ (by positivity : 0 < 6 * y ^ 5)).mpr
  change x * (6 * y ^ 5) ≤ _
  nlinarith only [hp]

theorem third_head_of_sixth_heads {a b A B : ℕ} (ha : 1 ≤ a)
    (h : HeadBound a b A B) {y : ℝ} (hy : 0 < y) :
    (∑ q ∈ Finset.Ico a b, totientWeight q (1 / 3)) ≤
      (5 * y / 6) * ((A : ℝ) / denominator) +
        (1 / (6 * y ^ 5)) * ((B : ℝ) / denominator) := by
  calc
    _ ≤ ∑ q ∈ Finset.Ico a b,
        ((5 * y / 6) * totientWeight q (1 / 6) +
          (1 / (6 * y ^ 5)) * totientWeight q (7 / 6)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : 0 < q := lt_of_lt_of_le (by omega) (Finset.mem_Ico.mp hq).1
      rw [third_weight_eq_sixth_mul hq0, totientWeight_seven_sixths hq0]
      have hb := mul_le_mul_of_nonneg_left (sixth_root_tangent (q := q) hy)
        (totientWeight_nonneg q (1 / 6))
      convert! hb using 1
      field_simp
    _ = (5 * y / 6) * (∑ q ∈ Finset.Ico a b, totientWeight q (1 / 6)) +
        (1 / (6 * y ^ 5)) * (∑ q ∈ Finset.Ico a b, totientWeight q (7 / 6)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left h.2.1 (by positivity))
      (mul_le_mul_of_nonneg_left h.2.2 (by positivity))

theorem certified_remaining_heads :
    HeadBound 1057 100001 6901757962 42256905596807 := by
  have h02 := (((bound0002.join bound0003).join bound0004).join bound0005).join
    (((bound0006.join bound0007).join bound0008).join bound0009)
  have h10 := (((bound0010.join bound0011).join bound0012).join bound0013).join
    (((bound0014.join bound0015).join bound0016).join bound0017)
  have h18 := (((bound0018.join bound0019).join bound0020).join bound0021).join
    (((bound0022.join bound0023).join bound0024).join bound0025)
  have h26 := (((bound0026.join bound0027).join bound0028).join bound0029).join
    (((bound0030.join bound0031).join bound0032).join bound0033)
  have h34 := (((bound0034.join bound0035).join bound0036).join bound0037).join
    (((bound0038.join bound0039).join bound0040).join bound0041)
  have h42 := (((bound0042.join bound0043).join bound0044).join bound0045).join
    (((bound0046.join bound0047).join bound0048).join bound0049)
  have h50 := (((bound0050.join bound0051).join bound0052).join bound0053).join
    (((bound0054.join bound0055).join bound0056).join bound0057)
  have h58 := (((bound0058.join bound0059).join bound0060).join bound0061).join
    (((bound0062.join bound0063).join bound0064).join bound0065)
  have h66 := (((bound0066.join bound0067).join bound0068).join bound0069).join
    (((bound0070.join bound0071).join bound0072).join bound0073)
  have h74 := (((bound0074.join bound0075).join bound0076).join bound0077).join
    (((bound0078.join bound0079).join bound0080).join bound0081)
  have h82 := (((bound0082.join bound0083).join bound0084).join bound0085).join
    (((bound0086.join bound0087).join bound0088).join bound0089)
  have h90 := ((((bound0090.join bound0091).join bound0092).join bound0093).join
    (((bound0094.join bound0095).join bound0096).join bound0097)).join bound0098
  exact (((h02.join h10).join h18).join ((h26.join h34).join h42)).join
    (((h50.join h58).join h66).join ((h74.join h82).join h90))

theorem third_head_33_1056 :
    (∑ q ∈ Finset.Ico 33 1057, totientWeight q (1 / 3)) ≤ 0.284 := by
  apply (third_head_of_sixth_heads (by norm_num) bound0001
    (y := 9 / 4) (by norm_num)).trans
  norm_num [denominator]

theorem third_head_1057_100000 :
    (∑ q ∈ Finset.Ico 1057 100001, totientWeight q (1 / 3)) ≤ 0.03 := by
  apply (third_head_of_sixth_heads (by norm_num) certified_remaining_heads
    (y := 17 / 4) (by norm_num)).trans
  norm_num [denominator]

theorem third_finite_head : totientMoment 100000 (1 / 3) ≤ 4.01 := by
  have he : denominators 100000 = Finset.Ico 1 100001 := by
    unfold denominators
    norm_num only [Nat.floor_natCast]
    rfl
  unfold totientMoment
  rw [he, ← Finset.sum_Ico_consecutive _ (by norm_num : 1 ≤ 33)
    (by norm_num : 33 ≤ 100001),
    ← Finset.sum_Ico_consecutive _ (by norm_num : 33 ≤ 1057)
      (by norm_num : 1057 ≤ 100001)]
  linarith only [third_head_through_32, third_head_33_1056, third_head_1057_100000]

theorem I13_with_third_head_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    ‖I13 N‖ ≤ 0.0016 * (N : ℝ) ^ 2 :=
  I13_of_finite_head hN hlow hhigh third_finite_head

theorem ordinary_major_lower_with_third_head_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N)
    (hlow : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      lowWeightSum N q ≤ 0.0194 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], q ∈ denominators (sourceP N) →
      highWeightSum N q ≤ 0.0126 * (q : ℝ) / sourceL N ^ 4) :
    0.5437 * (N : ℝ) ^ 2 ≤ (LiuWang.Proof.MajorArcApproximation.majorIntegral N).re :=
  ordinary_major_lower_of_finite_head hN hodd hlow hhigh third_finite_head

#print axioms third_finite_head
#print axioms ordinary_major_lower_with_third_head_paid

end LiuWang.Proof.Campaign20260915.MajorArc
