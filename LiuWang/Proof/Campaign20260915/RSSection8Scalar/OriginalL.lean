import LiuWang.Proof.Campaign20260915.RSSection8Scalar.EndpointL
import LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel.OriginalKernel

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Set BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Campaign20260915.RSSection8ZeroKernel

namespace LiuWang.Proof.Campaign20260915.RSSection8Scalar

theorem originalK_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ originalK m x := by
  apply tsum_nonneg
  intro p
  exact div_nonneg (Real.rpow_nonneg hx _) (abs_nonneg _)

theorem originalK_antitoneOn {m : ℕ} (hm : 1 ≤ m) :
    AntitoneOn (originalK m) (Ici 1) := by
  intro x hx y hy hxy
  apply (originalKernelTerm_summable hm hy).tsum_le_tsum _ (originalKernelTerm_summable hm hx)
  intro p
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  apply Real.rpow_le_rpow_of_nonpos (by linarith [show 1 ≤ x from hx]) hxy
  linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).2]

/-- RS1962 (8.4), consuming K01's source-normalized, multiplicity-preserving kernel. -/
def L (x : ℝ) : ℝ := LValue x (originalK 1 x)

theorem L_antitoneOn : AntitoneOn L (Ioi 1) := by
  intro x hx y hy hxy
  have hx1 : 1 ≤ x := le_of_lt hx
  have hy1 : 1 ≤ y := le_of_lt hy
  exact (LValue_mono_kernel hy
    (originalK_antitoneOn (m := 1) (by norm_num) hx1 hy1 hxy)).trans
    (LValue_antitone_base hx hxy (originalK_nonneg 1 (by linarith [show 1 < x from hx])))

theorem L_endpoint_le {A x : ℝ} (hA : 1 < A) (hx : A ≤ x) : L x ≤ L A :=
  L_antitoneOn hA (hA.trans_le hx) hx

/-- RS1962 Lemma 10, with no unproved assumptions on the actual spectral kernel. -/
theorem lemma10 {A B a x : ℝ} (hA : 1 < A) (ha : a < 1 / 2)
    (hdom : Real.sqrt ((1 / 2) * (1 + 2 * a) / (1 - 2 * a)) ≤ Real.log A)
    (hendpoint : L A < M B a) (hx : x ∈ Icc A B) : L x < M x a :=
  ((L_endpoint_le hA hx.1).trans_lt hendpoint).trans_le (M_endpoint_le hA ha hdom hx)

#print axioms originalK_antitoneOn
#print axioms L_antitoneOn
#print axioms lemma10

end LiuWang.Proof.Campaign20260915.RSSection8Scalar
