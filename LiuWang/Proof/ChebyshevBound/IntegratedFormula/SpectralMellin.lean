import LiuWang.Proof.ChebyshevBound.IntegratedFormula.GammaMellin

/-! # 极点、全零点和及完整 Γ 修正的 Mellin 恒等式。 -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.ChebyshevBound.IntegratedFormula

def spectralMellin (u : ℝ) : ℂ :=
  ((1 - Real.log (2 * Real.pi) : ℝ) : ℂ) * triangle u -
    (∑' p, zeroMellinTerm p u) + poleMellin u + ∑' n, gammaMellinTerm n u

theorem xi_constant_complex :
    -logDeriv riemannXi 0 - (Real.log Real.pi : ℂ) / 2 -
      (Real.eulerMascheroniConstant : ℂ) / 2 =
        ((1 - Real.log (2 * Real.pi) : ℝ) : ℂ) := by
  have h := neg_two_mul_logDeriv_riemannXi_zero_eq
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero,
    Real.log_four_eq] at h
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  push_cast at h ⊢
  linear_combination h / 2

theorem hasMellin_spectralMellin {s : ℂ} (hs : 1 < s.re) :
    HasMellin spectralMellin s
      ((-deriv riemannZeta s / riemannZeta s) / (s * (s + 1))) := by
  have ht := hasMellin_triangle (by linarith : 0 < s.re)
  have hc := hasMellin_const_smul ht.1 (((1 - Real.log (2 * Real.pi) : ℝ) : ℂ))
  have hz := hasMellin_zeroSum hs
  have hp := hasMellin_poleMellin hs
  have hg := hasMellin_gammaSum hs
  have hsub := hasMellin_sub hc.1 hz.1
  have hadd := hasMellin_add hsub.1 hp.1
  have hall := hasMellin_add hadd.1 hg.1
  refine ⟨hall.1, hall.2.trans ?_⟩
  rw [hadd.2, hsub.2, hc.2, ht.2, hz.2, hp.2, hg.2, smul_eq_mul,
    ← xi_constant_complex, Robin1984.neg_riemannZeta_logDeriv_eq_xiDivisor_tsum hs]
  change _ = (-logDeriv riemannXi 0 - (∑' p, xiTerm s p) + 1 / (s - 1) -
    (1 / 2 : ℂ) * Real.log Real.pi + (1 / 2 : ℂ) * digamma (s / 2 + 1)) / (s * (s + 1))
  simp only [div_mul_eq_div_div]
  ring

theorem mellin_mangoldt_eq_spectral {s : ℂ} (hs : 2 < s.re) :
    mellin (fun u => ∑' n, mangoldtTriangle n u) s = mellin spectralMellin s :=
  (hasMellin_mangoldtSum hs).2.trans (hasMellin_spectralMellin (by linarith)).2.symm

end LiuWang.Proof.ChebyshevBound.IntegratedFormula
