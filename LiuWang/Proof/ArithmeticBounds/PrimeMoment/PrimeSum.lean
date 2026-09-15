import LiuWang.Proof.ArithmeticBounds.PrimeMoment.Abel
import LiuWang.Proof.ArithmeticBounds.LambdaMoment.SharpPaid

/-! 消费原 W1 的左开右闭实际素数和恒等式。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.PrimeMoment

open Parameters LambdaMoment

theorem W1_le_8 {N : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real))
    (hUX : sourceVaughanU N ≤ X) (hXN : X ≤ N) :
    W1 N X ≤
      (Real.log X ^ 2 - Real.log (sourceVaughanU N) ^ 2) / 2 + 8 * Real.log X := by
  rw [W1_eq_actual_prime_sum hN ((sourceVaughanU_pos hN).le.trans hUX) hXN]
  exact prime_log_sq_interval_le (one_lt_sourceVaughanU hN).le hUX

theorem W1_le_20 {N : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real))
    (hUX : sourceVaughanU N ≤ X) (hXN : X ≤ N) :
    W1 N X ≤
      (Real.log X ^ 2 - Real.log (sourceVaughanU N) ^ 2) / 2 + 20 * Real.log X := by
  have := W1_le_8 hN hUX hXN
  have := Real.log_nonneg ((one_lt_sourceVaughanU hN).le.trans hUX)
  linarith

end LiuWang.Proof.ArithmeticBounds.PrimeMoment
