import LiuWang.Proof.VaughanTypeII.Kernel
import LiuWang.Proof.VaughanTypeI.Geometric

/-! 两个既有核的定义等式，包括共振分支；不提供实际行计数。 -/

set_option autoImplicit false

namespace LiuWang.Proof.VaughanTypeIIBudget

theorem kernel_eq_truncatedKernel (M z : ℝ) :
    VaughanTypeII.kernel M z = VaughanTypeI.truncatedKernel (M + 1 / 2) z := rfl

end LiuWang.Proof.VaughanTypeIIBudget
