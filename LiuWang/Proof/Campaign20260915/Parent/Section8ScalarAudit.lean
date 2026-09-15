import LiuWang.Proof.Campaign20260915.RSSection8Scalar.Section8Tools

/-! Original Section 8 scalar tools with actual spectral kernel L.
Lemma 10 retains its original endpoint comparison; numerical endpoint budgets remain separate.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set
namespace LiuWang.Proof.Campaign20260915.Parent.Section8ScalarAudit
open LiuWang.Proof.Campaign20260915.RSSection8Scalar

theorem actual_L_antitone : AntitoneOn L (Ioi 1) := L_antitoneOn

theorem actual_lemma10 {A B a x : ℝ} (hA : 1 < A) (ha : a < 1 / 2)
    (hdom : Real.sqrt ((1 / 2) * (1 + 2 * a) / (1 - 2 * a)) ≤ Real.log A)
    (hendpoint : L A < M B a) (hx : x ∈ Icc A B) : L x < M x a :=
  lemma10 hA ha hdom hendpoint hx

#print axioms actual_L_antitone
#print axioms actual_lemma10
end LiuWang.Proof.Campaign20260915.Parent.Section8ScalarAudit

#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.logTailKernel_nonneg
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.logTailKernel_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.lemma9
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.primePowerIntegrand_eq
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.primePowerIntegrand_integrable
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.primePower_integral_le
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.M_eq_logM
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.logM_deriv
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.logM_deriv_nonpos
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.logM_antitoneOn
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.M_antitoneOn_of_square
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.M_antitoneOn
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.M_endpoint_le
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.LValue_mono_kernel
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.LValue_antitone_base
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.LValue_antitoneOn
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.lemma10_scalar
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.logM_lower
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.M_047_gt_0028
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.M_031_antitoneOn
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.M_047_antitoneOn
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.originalK_nonneg
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.originalK_antitoneOn
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.L_antitoneOn
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.L_endpoint_le
#print axioms LiuWang.Proof.Campaign20260915.RSSection8Scalar.lemma10
