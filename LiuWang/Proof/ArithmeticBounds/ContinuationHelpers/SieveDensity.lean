import LiuWang.Proof.ArithmeticBounds.ContinuationHelpers.SquarefreeSieve

/-! 固定筛权的有理密度证书，不枚举待估计区间中的整数。 -/

set_option autoImplicit false

namespace LiuWang.Proof.ArithmeticBounds.ContinuationHelpers

theorem sieve_density_le : sieveForm oddDensity ≤ 30517 / 50000 := by
  norm_num [sieveForm, oddDensity, sievePrimes]

end LiuWang.Proof.ArithmeticBounds.ContinuationHelpers
