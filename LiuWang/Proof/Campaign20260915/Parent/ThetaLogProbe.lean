import LiuWang.Proof.Campaign20260915.Totient.PrefixTable

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace LiuWang.Proof.Campaign20260915.Parent.ThetaLogProbe
open LiuWang.Proof.Campaign20260915.Totient

theorem last_log_row :
    (72506355092 : ℤ) = ⌊logCenter (1409 : ℚ) * 10000000000⌋ := by
  have hs : logScale (1409 : ℚ) = 10 := by decide +kernel
  norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

#print axioms last_log_row
end LiuWang.Proof.Campaign20260915.Parent.ThetaLogProbe
