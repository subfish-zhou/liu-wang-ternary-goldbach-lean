import LiuWang.Proof.ExplicitPerron.SourceKernel
import LiuWang.Proof.ExplicitPerron.ClosedError
import LiuWang.Proof.Parameters.Main

/-!
# Explicit finite Perron API

`source_perron` and `source_perron_of_series` prove the complete printed
half-integer Lemma 4.1, with its literal `2^b` coefficient.

`sourceDomain_right_perron` concerns the actual character, actual inclusive
Chebyshev sum, actual real endpoint, and independently chosen heights. Its
closed effective error is proved, but the scalar comparison with
`1.38022*t*L^2/T` is not asserted. No horizontal edge is estimated here.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ExplicitPerron

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

theorem sourceDomain_right_perron {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hN : Real.exp 2000 ≤ (N : ℝ))
    {t Hminus Hplus : ℝ} (ht : sourceWindowLower N ≤ t)
    (hminus : |Hminus + sourceT N| ≤ 1) (hplus : |Hplus - sourceT N| ≤ 1) :
    ‖vertical (centeredIntegrand chi t (5 / 2)) (1 + 1 / sourceL N) Hminus Hplus -
      psi chi t‖ ≤
      closedRealEndpointError t (1 + 1 / sourceL N) (sourceT N) Hminus Hplus := by
  have hL := sourceL_ge_2000 hN
  have hpow : sourceL N ≤ sourceT N := by
    simpa only [pow_one, sourceT] using
      pow_le_pow_right₀ (one_le_sourceL hN) (show (1 : ℕ) ≤ 15 by norm_num)
  have hT : 1 < sourceT N := by linarith
  have ht1 : 1 ≤ t := by have := sourceT_lt_real_endpoint hN ht; linarith
  have hb : 1 < 1 + 1 / sourceL N := by
    have := one_div_pos.mpr (sourceL_pos hN)
    linarith
  exact norm_realEndpoint_perron_le_closed chi ht1 hb hT hminus hplus

end LiuWang.Proof.ExplicitPerron
