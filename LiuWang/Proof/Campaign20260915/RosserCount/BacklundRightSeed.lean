import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCertificates

set_option autoImplicit false
set_option maxRecDepth 4000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_right_seed_two :
    (2 : ℝ) ^ (-(12847 / 5000 : ℝ)) ≤ 168487 / 1000000 := by
  have h := backlund_rpow_div_certificate (n := 2) (by norm_num) (by norm_num)
    (a := 12847 / 5000) (q := 17809 / 10000) (d := 1) (u := 168487 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, sum_range_succ])
    (by norm_num [backlundExpLower, sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, div_one] at h
  exact h

#print axioms backlund_right_seed_two

end LiuWang.Proof.Campaign20260915.RosserCount
