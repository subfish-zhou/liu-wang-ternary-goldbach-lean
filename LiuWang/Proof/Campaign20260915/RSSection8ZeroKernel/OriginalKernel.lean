import LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.ReflectedTail
import LiuWang.Proof.Campaign20260915.Totient.RSEpsilonTerminal

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel

/-- Rosser 1941, p. 222, (9): the sum is over all nontrivial zeros;
the denominator is |gamma^(m+1)|, not a power of |rho|. -/
def originalKernelTerm (m : ℕ) (x : ℝ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
  x ^ ((riemannXiDivisorZeroValue p).re - 1) /
    |(riemannXiDivisorZeroValue p).im ^ (m + 1)|

def originalK (m : ℕ) (x : ℝ) : ℝ := ∑' p, originalKernelTerm m x p

theorem originalKernelTerm_eq_moment (m : ℕ) {x : ℝ} (hx : 0 < x)
    (p : RiemannXiDivisorZeroIndex) :
    originalKernelTerm m x p = rsZeroMoment m (Real.log x) p := by
  unfold originalKernelTerm rsZeroMoment
  rw [Real.rpow_def_of_pos hx, abs_pow, mul_comm (Real.log x)]

theorem originalK_eq_moment (m : ℕ) {x : ℝ} (hx : 0 < x) :
    originalK m x = ∑' p, rsZeroMoment m (Real.log x) p := by
  exact tsum_congr (originalKernelTerm_eq_moment m hx)

theorem originalKernelTerm_summable {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 1 ≤ x) :
    Summable (originalKernelTerm m x) := by
  have he : originalKernelTerm m x = rsZeroMoment m (Real.log x) :=
    funext (originalKernelTerm_eq_moment m (by linarith))
  rw [he]
  exact rsZeroMoment_summable hm (Real.log_nonneg hx)

theorem originalK_one_inverse_square :
    originalK 1 1 =
      ∑' p : RiemannXiDivisorZeroIndex, 1 / (riemannXiDivisorZeroValue p).im ^ 2 := by
  simp [originalK, originalKernelTerm]

theorem originalK_variable_cutoff {x K : ℝ} (hx : 1 ≤ x) (hK : rsA ≤ K) :
    originalK 1 x ≤
      (∑' p, closedMomentTerm rsA (Real.log x) p) +
        (∑' p, rsHighTerm rsA 1 0 p) / (2 * Real.sqrt x) +
          x ^ (-(1 / (rsR * Real.log K))) / 2 *
            (∑' p, rsHighTerm rsA 1 0 p) +
              (∑' p, rsHighTerm K 1 0 p) / 2 := by
  have hx0 : 0 < x := by linarith
  rw [originalK_eq_moment 1 hx0]
  have h := actual_moment_variable_cutoff hK (Real.log_nonneg hx)
  apply h.trans_eq
  rw [rs_low_weight_sqrt hx0]
  have he : Real.exp (-(Real.log x / (rsR * Real.log K))) =
      x ^ (-(1 / (rsR * Real.log K))) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    ring
  rw [he]
  ring

#print axioms originalK_eq_moment
#print axioms originalK_one_inverse_square
#print axioms originalKernelTerm_summable
#print axioms originalK_variable_cutoff

end LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel
