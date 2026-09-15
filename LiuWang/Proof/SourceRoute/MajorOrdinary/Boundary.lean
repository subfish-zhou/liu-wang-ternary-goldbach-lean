import LiuWang.Proof.SourceRoute.MajorOrdinary.Assembly

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.MajorOrdinary

theorem cutoff_uses_low_weight {N q : ℕ} {rho : ℂ}
    (he : |rho.im| = omegaCutoff N q) :
    arcZeroWeight N q rho = WeightedLowZeros.weight N rho.re := by
  simp only [arcZeroWeight, he, le_refl, if_true]

theorem real_zero_uses_low_weight {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q) {rho : ℂ} (hi : rho.im = 0) :
    arcZeroWeight N q rho = WeightedLowZeros.weight N rho.re := by
  simp only [arcZeroWeight, hi, abs_zero, if_pos (omegaCutoff_pos hN hq).le]

theorem packetBound_one (N : ℕ) :
    packetBound N 1 = (N : ℝ) * (lowWeightSum N 1 + 5 * highWeightSum N 1) := by
  simp only [packetBound, Nat.cast_one, Real.sqrt_one, Nat.totient_one,
    div_one, one_mul, zeroEnvelope_split]

theorem zero_radius_Jrho (N : ℕ) (rho : ℂ) :
    cubicMass 0 (Jrho N rho) = 0 := cubicMass_zero _

theorem source425_threshold :
    (0.5437 : ℝ) ≤
      (0.656145 - 0.1108 - 0.0016 - 0.00002) - 3 / (3100 : ℝ) ^ 9 := by
  simpa using source425_margin (N := 1) (L := 3100) le_rfl

end LiuWang.Proof.SourceRoute.MajorOrdinary
