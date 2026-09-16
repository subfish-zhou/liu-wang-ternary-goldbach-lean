import LiuWang.Proof.Campaign20260915.RSMediumRange.CertificateSoundness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

theorem prime_99614737 : Nat.Prime 99614737 := by norm_num

theorem log_99614737 :
    FixedBracket.log 99614737 26 =
      ⟨1841682066669824, 1841682068069846⟩ := by
  have hr : FixedBracket.ratio (99614737 - 2 ^ 26) (99614737 + 2 ^ 26) =
      ⟨19496863554428, 19496863554429⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem log_99614737_bounds :
    (FixedBracket.mk 1841682066669824 1841682068069846).Contains
      (Real.log 99614737) := by
  have h := FixedBracket.log_contains (n := 99614737) (k := 26)
    (by norm_num) (by norm_num)
  rwa [log_99614737] at h

#print axioms prime_99614737
#print axioms log_99614737_bounds

end LiuWang.Proof.Campaign20260915.RSMediumRange
