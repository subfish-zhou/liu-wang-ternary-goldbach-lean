import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral.DirectedConstants

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral

theorem cellValue_le_moment_intervals {H u v m M5lo M5hi M6lo M6hi M7hi : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hH : 4 * v < H)
    (h5lo : M5lo ≤ expMoment 5 (phaseSlope H m) (phaseIntercept H m) u v)
    (h5hi : expMoment 5 (phaseSlope H m) (phaseIntercept H m) u v ≤ M5hi)
    (h6lo : M6lo ≤ expMoment 6 (phaseSlope H m) (phaseIntercept H m) u v)
    (h6hi : expMoment 6 (phaseSlope H m) (phaseIntercept H m) u v ≤ M6hi)
    (h7hi : expMoment 7 (phaseSlope H m) (phaseIntercept H m) u v ≤ M7hi) :
    cellValue H u v m ≤
      H / ((H - 4 * u) * (H - 4 * v)) *
        ((H - 4 * v) * (254231 * M5hi + 33643 * M6hi) +
          4 * (254231 * (M6hi - u * M5lo) + 33643 * (M7hi - u * M6lo))) := by
  have hHu : 0 < H - 4 * u := by linarith
  have hHv : 0 < H - 4 * v := by linarith
  have hHp : 0 < H := by linarith
  have hshift5 := sub_le_sub h6hi (mul_le_mul_of_nonneg_left h5lo hu.le)
  have hshift6 := sub_le_sub h7hi (mul_le_mul_of_nonneg_left h6lo hu.le)
  unfold cellValue
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left h5hi (by norm_num))
      (mul_le_mul_of_nonneg_left h6hi (by norm_num))) hHv.le
  · exact mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hshift5 (by norm_num))
      (mul_le_mul_of_nonneg_left hshift6 (by norm_num))) (by norm_num)

theorem cellValue_zero_slope {H u v m : ℝ} (hs : phaseSlope H m = 0) :
    cellValue H u v m =
      H / ((H - 4 * u) * (H - 4 * v)) *
        Real.exp (phaseIntercept H m) *
        ((H - 4 * v) * (254231 * ((v ^ (6 : ℕ) - u ^ (6 : ℕ)) / 6) +
          33643 * ((v ^ (7 : ℕ) - u ^ (7 : ℕ)) / 7)) +
        4 * (254231 * ((v ^ (7 : ℕ) - u ^ (7 : ℕ)) / 7 -
            u * ((v ^ (6 : ℕ) - u ^ (6 : ℕ)) / 6)) +
          33643 * ((v ^ (8 : ℕ) - u ^ (8 : ℕ)) / 8 -
            u * ((v ^ (7 : ℕ) - u ^ (7 : ℕ)) / 7)))) := by
  unfold cellValue
  rw [hs, expMoment_zero, expMoment_zero, expMoment_zero]
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
  ring

theorem original_all_L_partition_bound {L : ℝ} (hL : 3100 ≤ L)
    (n : ℕ) (p m : ℕ → ℝ)
    (hp : MonotoneOn p (Set.Icc 0 n))
    (ha : p 0 = lowerLog 3100) (hb : p n = upperLog 3100)
    (hm : ∀ i < n, m i ∈ Set.Icc (p i) (p (i + 1))) :
    originalDensityScalar L ≤
      (8 * Real.exp (4 * 0.478) * sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100) *
        ∑ i ∈ Finset.range n,
          cellValue ((3100 : ℝ) + Real.log 0.001) (p i) (p (i + 1)) (m i) :=
  (originalDensityScalar_le_base hL).trans (original_fixed_partition_bound n p m hp ha hb hm)

theorem original_all_L_directed_bound {L : ℝ} (hL : 3100 ≤ L)
    (n : ℕ) (p m : ℕ → ℝ) {Hlo Ephase Egamma ellLo ellHi : ℝ}
    (hp : MonotoneOn p (Set.Icc 0 n)) (hp0 : 0 < p 0)
    (ha : p 0 ≤ lowerLog 3100) (hb : upperLog 3100 ≤ p n)
    (hHlo : 4 * p n < Hlo) (hH : Hlo ≤ (3100 : ℝ) + Real.log 0.001)
    (hm : ∀ i < n, m i ∈ Set.Icc (p i) (p (i + 1)))
    (hphase : Real.exp (4 * 0.478) ≤ Ephase)
    (hgamma : Real.exp Real.eulerMascheroniConstant ≤ Egamma)
    (hell : 0 < ellLo)
    (hellLo : ellLo ≤ Real.log (Real.log ((3100 : ℝ) ^ (3 : ℕ))))
    (hellHi : Real.log (Real.log ((3100 : ℝ) ^ (3 : ℕ))) ≤ ellHi) :
    originalDensityScalar L ≤
      (8 * Ephase * (Egamma * ellHi + 2.50637 / ellLo) * 3100) *
        ∑ i ∈ Finset.range n, cellValue Hlo (p i) (p (i + 1)) (m i) :=
  (originalDensityScalar_le_base hL).trans
    (original_fixed_directed_bound n p m hp hp0 ha hb hHlo hH hm hphase hgamma hell hellLo hellHi)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral
