import LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.OriginalKernel
import LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.CutoffBudget

/-! Actual original K and arbitrary-cutoff spectral bound.
The scalar boundary payment is not a numerical certificate for the zero sum.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient
namespace LiuWang.Proof.Campaign20260915.Parent.Section8KernelAudit
open LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel

theorem actual_originalK_cutoff {x K : ℝ} (hx : 1 ≤ x) (hK : rsA ≤ K) :
    originalK 1 x ≤
      (∑' p, closedMomentTerm rsA (Real.log x) p) +
        (∑' p, rsHighTerm rsA 1 0 p) / (2 * Real.sqrt x) +
          x ^ (-(1 / (rsR * Real.log K))) / 2 *
            (∑' p, rsHighTerm rsA 1 0 p) +
              (∑' p, rsHighTerm K 1 0 p) / 2 :=
  originalK_variable_cutoff hx hK

#print axioms actual_originalK_cutoff
end LiuWang.Proof.Campaign20260915.Parent.Section8KernelAudit

#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.unweighted_laplace_integral
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.unweighted_phi_integral
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.unweighted_phi_coefficient
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.reflected_tail_pointwise
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.reflected_tail_sum
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.closedMomentTerm_summable
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.actual_moment_split
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.actual_moment_variable_cutoff
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.originalKernelTerm_eq_moment
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.originalK_eq_moment
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.originalKernelTerm_summable
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.originalK_one_inverse_square
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.originalK_variable_cutoff
#print axioms LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.original_boundary_integral_budget
