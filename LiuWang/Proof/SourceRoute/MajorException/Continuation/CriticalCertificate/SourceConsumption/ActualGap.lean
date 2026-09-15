import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.Consumer
import LiuWang.Proof.ExceptionalZeroGap.LargeConductor

set_option autoImplicit false
noncomputable section
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroInteraction LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

theorem R24_horizontal_to_source {x : ℝ} {q : ℕ} {rho : ℂ}
    (hx : 10 ≤ x) (hr : RealClosure.region x q rho) :
    ExceptionalZeroGap.nearOneLower x ≤ rho.re := by
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hc : 0 < ExceptionalZeroGap.c1*Real.log x := by
    unfold ExceptionalZeroGap.c1
    positivity
  have hw : 1/(24*Real.log x) ≤ 1/(ExceptionalZeroGap.c1*Real.log x) :=
    one_div_le_one_div_of_le hc (by
      unfold ExceptionalZeroGap.c1
      nlinarith)
  unfold ExceptionalZeroGap.nearOneLower
  linarith [hr.1]

theorem actual_exceptional_gap {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (h987 : 987 ≤ (chi.conductor : ℝ)) :
    Real.pi/(0.4923*Real.sqrt chi.conductor*(Real.log chi.conductor)^2) ≤ 1-rho.re := by
  obtain ⟨d, hd, hdc, _, hdz, _⟩ := exceptionalValues_same_source hN hq hr
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have hi := (exceptionalValues_quadratic_simple hN hq hr).2.2.1
  have he : (rho.re : ℂ) = rho := by
    apply Complex.ext <;> simp [hi]
  have hz : d.character.LFunction (rho.re : ℂ) = 0 := by
    rw [he]
    exact hdz
  have hd987 : 987 ≤ d.modulus := by
    rw [hdc]
    exact_mod_cast h987
  have hb := R24_horizontal_to_source (sourceP_ge_ten hN) (Finset.mem_filter.mp hr).2
  have hg := ExceptionalZeroGap.real_primitive_local_zero_gap d.isPrimitive hd987
    (quadratic_values_real d.character d.square_eq_one) (sourceP_ge_ten hN) hd hb hz
  simpa only [hdc] using hg

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
