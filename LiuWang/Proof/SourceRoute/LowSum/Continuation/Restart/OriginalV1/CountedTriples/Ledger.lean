import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples.ProductSelection

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples

theorem counted_g_le {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x alpha : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {p r u : ZeroSlots q alpha (x / q)}
    (h : CountedData x q alpha chi psi eta p r u)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG chi psi eta (lwdSourceSigma x) p.value.im r.value.im u.value.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - p.value.re) + 1 / (lwdSourceSigma x - r.value.re) +
          1 / (lwdSourceSigma x - u.value.re)) +
        7 * stechkinConductorCoeff * Real.log x + 2.4998 := by
  have hx : 0 < x := by linarith [h.scale_ge]
  have hs := (lwd_source_parameters h.scale_ge).2.2
  have hp := mem_strictZeroValues.mp p.zero_mem
  have hr := mem_strictZeroValues.mp r.zero_mem
  have hu := mem_strictZeroValues.mp u.zero_mem
  have hmainp (hm : chi = 1) : 1 ≤ |p.value.im| := by
    have hh := principal_slot_RS p (by simpa only [hm, map_one] using h.p_label) h.re_gt_half.1 hRS
    linarith
  have hmainr (hm : psi = 1) : 1 ≤ |r.value.im| := by
    have hh := principal_slot_RS r (by simpa only [hm, map_one] using h.r_label) h.re_gt_half.2.1 hRS
    linarith
  have hmainu (hm : eta = 1) : 1 ≤ |u.value.im| := by
    have hh := principal_slot_RS u (by simpa only [hm, map_one] using h.u_label) h.re_gt_half.2.2 hRS
    linarith
  have hl12 := principal_pair_slot_labels chi psi h.chi_dvd h.psi_dvd p r h.p_label h.r_label
  have hl13 := principal_pair_slot_labels chi eta h.chi_dvd h.eta_dvd p u h.p_label h.u_label
  have hl23 := principal_pair_slot_labels psi eta h.psi_dvd h.eta_dvd r u h.r_label h.u_label
  have h0 := lwd_2_22_on_source_sigma hs.1 hs.2
  have h1 := primitive_slot_debits chi h.chi_primitive h.chi_dvd h.level_le hs.1 hs.2 p r u h.p_label
    h.re_gt_half.1 h.re_gt_half.2.1 h.re_gt_half.2.2 hp.2.2.2.2 hmainp
    h.separation.2.1 h.separation.2.2.2.1 h.separation.2.2.2.2.1 h.gaps.2.1 h.gaps.2.2
    (lwdProduct chi psi = 1) (lwdProduct chi eta = 1) (fun hm => (hl12 hm).1)
    (fun hm => (hl13 hm).1) hgammaHigh
  have h2 := primitive_slot_debits psi h.psi_primitive h.psi_dvd h.level_le hs.1 hs.2 r p u h.r_label
    h.re_gt_half.2.1 h.re_gt_half.1 h.re_gt_half.2.2 hr.2.2.2.2 hmainr
    (slot_conjugate_separation h.separation.2.1) h.separation.2.2.2.2.2 h.separation.2.2.1
    h.gaps.1 h.gaps.2.2 (lwdProduct chi psi = 1) (lwdProduct psi eta = 1)
    (fun hm => (hl12 hm).2) (fun hm => (hl23 hm).1) hgammaHigh
  have h3 := primitive_slot_debits eta h.eta_primitive h.eta_dvd h.level_le hs.1 hs.2 u p r h.u_label
    h.re_gt_half.2.2 h.re_gt_half.1 h.re_gt_half.2.1 hu.2.2.2.2 hmainu
    (slot_conjugate_separation h.separation.2.2.2.1)
    (slot_conjugate_separation h.separation.2.2.2.2.2) h.separation.1
    h.gaps.1 h.gaps.2.1 (lwdProduct chi eta = 1) (lwdProduct psi eta = 1)
    (fun hm => (hl13 hm).2) (fun hm => (hl23 hm).2) hgammaHigh
  rw [add_comm r.value.im p.value.im] at h2
  rw [add_comm u.value.im p.value.im, add_comm u.value.im r.value.im] at h3
  have h6 := pair_cost psi eta h.psi_dvd h.eta_dvd h.level_le hs.1 hs.2 hr.2.2.2.2 hu.2.2.2.2
    hr.2.2.2.1 hu.2.2.2.1 h.gaps.2.1 h.gaps.2.2 hgammaHigh hgammaLow
  by_cases hm : lwdProduct (lwdProduct chi psi) eta = 1
  · have hm' : lwdProduct (lwdProduct chi eta) psi = 1 := by
      apply (triple_principal_iff chi eta psi h.chi_dvd h.eta_dvd h.psi_dvd).mpr
      have hh := (triple_principal_iff chi psi eta h.chi_dvd h.psi_dvd h.eta_dvd).mp hm
      rwa [mul_right_comm] at hh
    have h4 := pair_with_triple_debit chi psi eta h.chi_dvd h.psi_dvd h.eta_dvd h.level_le
      p r u h.u_label h.re_gt_half.2.2 hs.1 hs.2 h.gaps.1 h.gaps.2.1 h.gaps.2.2 hm
      hRS hgammaHigh hgammaLow
    have h5 := pair_with_triple_debit chi eta psi h.chi_dvd h.eta_dvd h.psi_dvd h.level_le
      p u r h.r_label h.re_gt_half.2.1 hs.1 hs.2 h.gaps.1 h.gaps.2.2 h.gaps.2.1 hm'
      hRS hgammaHigh hgammaLow
    rw [add_right_comm p.value.im u.value.im r.value.im] at h5
    have hy123 : |p.value.im + r.value.im + u.value.im| ≤ (3 * x) / q := by
      rw [mul_div_assoc]
      linarith [abs_add_le p.value.im r.value.im, abs_add_le (p.value.im + r.value.im) u.value.im,
        hp.2.2.2.2, hr.2.2.2.2, hu.2.2.2.2]
    have h7 := principal_pair_paid (Nat.lcm_dvd (Nat.lcm_dvd h.chi_dvd h.psi_dvd) h.eta_dvd)
      hs.1 hs.2 (by linarith [h.level_le] : (q : ℝ) ≤ 3 * x) hy123 hu.2.2.2.1 hr.2.2.2.1
      h.gaps.2.2 h.gaps.2.1 hgammaHigh hgammaLow
    rw [← hm] at h7
    unfold nonprincipalCost at h1 h2 h3 h4 h5 h6
    unfold AllPrincipal.principalCost at h7
    rw [Real.log_mul (by norm_num) hx.ne'] at h4 h5 h6 h7
    unfold lwdG
    by_cases h12 : lwdProduct chi psi = 1 <;>
      by_cases h13 : lwdProduct chi eta = 1 <;>
      by_cases h23 : lwdProduct psi eta = 1 <;>
      simp only [h12, h13, h23, if_true, if_false] at h1 h2 h3 h4 h5 h6 h7 ⊢ <;>
      nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, lwd_2_27_constant]
  · have h4 := pair_cost chi psi h.chi_dvd h.psi_dvd h.level_le hs.1 hs.2 hp.2.2.2.2 hr.2.2.2.2
      hp.2.2.2.1 hr.2.2.2.1 h.gaps.1 h.gaps.2.1 hgammaHigh hgammaLow
    have h5 := pair_cost chi eta h.chi_dvd h.eta_dvd h.level_le hs.1 hs.2 hp.2.2.2.2 hu.2.2.2.2
      hp.2.2.2.1 hu.2.2.2.1 h.gaps.1 h.gaps.2.2 hgammaHigh hgammaLow
    have h7 := lwd_2_26 (Nat.lcm_dvd (Nat.lcm_dvd h.chi_dvd h.psi_dvd) h.eta_dvd) h.level_le
      (lwdProduct (lwdProduct chi psi) eta) hm hp.2.2.2.2 hr.2.2.2.2 hu.2.2.2.2
      hs.1 (by linarith [hs.2])
    unfold nonprincipalCost at h1 h2 h3 h4 h5 h6
    rw [Real.log_mul (by norm_num) hx.ne'] at h4 h5 h6
    unfold lwdG
    by_cases h12 : lwdProduct chi psi = 1 <;>
      by_cases h13 : lwdProduct chi eta = 1 <;>
      by_cases h23 : lwdProduct psi eta = 1 <;>
      simp only [h12, h13, h23, if_true, if_false] at h1 h2 h3 h4 h5 h6 h7 ⊢ <;>
      nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, lwd_2_27_constant]

theorem counted_lwd_2_28 {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x alpha : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {p r u : ZeroSlots q alpha (x / q)}
    (h : CountedData x q alpha chi psi eta p r u)
    (hRS : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      |z.im| < 1894438 → z.re = 1 / 2)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    0 ≤ 1 / (lwdSourceSigma x - 1) -
      (1 / (lwdSourceSigma x - p.value.re) + 1 / (lwdSourceSigma x - r.value.re) +
        1 / (lwdSourceSigma x - u.value.re)) +
      7 * stechkinConductorCoeff * Real.log x + 2.4998 := by
  have hb (b c : Bool) := counted_g_le (counted_data_signed h false b c) hRS hgammaHigh hgammaLow
  have h0 := hb false false
  have h1 := hb true false
  have h2 := hb false true
  have h3 := hb true true
  simp only [signedSlot, lwdSignedCharacter, Bool.false_eq_true, if_false, if_true,
    conjugateSlot_value, conj_re, conj_im] at h0 h1 h2 h3
  have hpos := lwd_2_13 chi psi eta (lwd_source_parameters h.scale_ge).2.2.1
    p.value.im r.value.im u.value.im
  linarith only [hpos, h0, h1, h2, h3]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples
