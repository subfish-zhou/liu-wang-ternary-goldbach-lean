import LiuWang.Proof.ChebyshevBound.Main
import LiuWang.Proof.ExplicitPerron.ClosedError

/-! The proved pole-plus-eight majorant, on its full valid strip.
Only the logarithmic derivative itself is needed by the Perron transport.
No comparison of derivatives of inequalities is used. -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.PerronRecovery

open ExplicitPerron BombieriVinogradov.SiegelWalfisz

def seriesBound (b : ℝ) : ℝ := 1 / (b - 1) + 8

theorem seriesBound_nonneg {b : ℝ} (hb : 1 < b) : 0 ≤ seriesBound b := by
  unfold seriesBound
  positivity

theorem mangoldt_normSum_le {b : ℝ} (hb : 1 < b) (hb' : b ≤ 5 / 4) :
    vonMangoldtLSeriesNormSum b ≤ seriesBound b := by
  simpa only [vonMangoldtLSeriesNormSum, norm_LSeriesTerm_vonMangoldt_eq, seriesBound]
    using ChebyshevBound.mangoldt_dirichlet_le_inv_add_eight hb hb'

theorem normSum_twisted_le {q : ℕ} (chi : DirichletCharacter ℂ q)
    {b : ℝ} (hb : 1 < b) (hb' : b ≤ 5 / 4) :
    (∑' n, ‖LSeries.term (twistedMangoldtSequence chi) (b : ℂ) n‖) ≤
      seriesBound b := by
  apply le_trans _ (mangoldt_normSum_le hb hb')
  apply (twisted_summable chi (by simpa using hb)).norm.tsum_le_tsum
  · intro n
    apply LSeries.norm_term_le
    simpa only [Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      using norm_twistedMangoldtSequence_le_vonMangoldt chi n
  · exact (ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (b : ℂ)) (by simpa using hb)).norm

theorem norm_logDeriv_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) (hs' : s.re ≤ 5 / 4) :
    ‖-logDeriv chi.LFunction s‖ ≤ seriesBound s.re := by
  have h := norm_neg_logDeriv_LFunction_le_zeta_re chi hs
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (s.re : ℂ)) (by simpa using hs), ← mangoldt_normSum_eq_norm] at h
  simpa only [logDeriv_apply, neg_div] using h.trans (mangoldt_normSum_le hs hs')

theorem source_abscissa_mem {L : ℝ} (hL : 4 ≤ L) :
    1 < 1 + 1 / L ∧ 1 + 1 / L ≤ 5 / 4 := by
  have hL0 : 0 < L := by linarith
  have hpos := one_div_pos.mpr hL0
  have hle : 1 / L ≤ 1 / 4 := (div_le_iff₀ hL0).mpr (by linarith)
  constructor <;> linarith

theorem seriesBound_source (L : ℝ) : seriesBound (1 + 1 / L) = L + 8 := by
  simp [seriesBound]

end LiuWang.Proof.PerronRecovery
