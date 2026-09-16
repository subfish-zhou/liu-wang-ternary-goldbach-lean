import LiuWang.Proof.Campaign20260915.RosserCount.BacklundExplicitCircle
import Mathlib.Analysis.SumIntegralComparisons

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Finset

namespace LiuWang.Proof.Campaign20260915.RosserCount

def backlundDirichletEnvelope (N : ℕ) (σ : ℝ) : ℝ :=
  (∑ n ∈ range N, (n + 1 : ℝ) ^ (-σ)) + (N : ℝ) ^ (1 - σ) / (σ - 1)

theorem backlund_dirichlet_tail {σ : ℝ} (hσ : 1 < σ) {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-σ)) ≤
      (N : ℝ) ^ (1 - σ) / (σ - 1) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Ici (N : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (hNR.trans_le hx) hxy (by linarith)
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) hNR
  have h := hanti.tsum_comp_add_le_integral N hi
    (fun x hx => Real.rpow_nonneg (hNR.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt (by linarith) hNR] at h
  convert h using 1
  rw [show -σ + 1 = -(σ - 1) by ring, neg_div_neg_eq]
  congr 1
  ring

theorem backlund_zeta_dirichlet_envelope {s : ℂ} (hs : 1 < s.re)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s‖ ≤ backlundDirichletEnvelope N s.re := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ s) 1).mpr hsum
  have hz : riemannZeta s = ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ s := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    have h := hsum.sum_add_tsum_nat_add 1
    simpa only [sum_range_one, Nat.cast_zero,
      zero_cpow (Complex.ne_zero_of_one_lt_re hs), div_zero, zero_add] using h.symm
  have hnorm (n : ℕ) : ‖1 / ((n + 1 : ℕ) : ℂ) ^ s‖ = (n + 1 : ℝ) ^ (-s.re) := by
    rw [norm_div, norm_one, norm_natCast_cpow_of_pos (by omega),
      one_div, ← Real.rpow_neg (by positivity)]
    push_cast
    rfl
  have hsplit := hshift.sum_add_tsum_nat_add N
  rw [hz, ← hsplit]
  have htail := norm_tsum_le_tsum_norm
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) N).mpr hshift).norm
  simp only [hnorm] at htail
  have ht : (∑' n : ℕ, (n + N + 1 : ℝ) ^ (-s.re)) ≤
      (N : ℝ) ^ (1 - s.re) / (s.re - 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using backlund_dirichlet_tail hs hN
  have ht' := htail.trans (by simpa only [Nat.cast_add] using ht)
  have hf := norm_sum_le (s := range N) (f := fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s)
  simp only [hnorm] at hf
  have h := norm_add_le (∑ n ∈ range N, 1 / ((n + 1 : ℕ) : ℂ) ^ s)
    (∑' n : ℕ, 1 / ((n + N + 1 : ℕ) : ℂ) ^ s)
  change ‖_‖ ≤ _ at h
  unfold backlundDirichletEnvelope
  linarith

theorem backlundDirichletEnvelope_pos {N : ℕ} (hN : 1 ≤ N) {σ : ℝ} (hσ : 1 < σ) :
    0 < backlundDirichletEnvelope N σ := by
  unfold backlundDirichletEnvelope
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact add_pos_of_nonneg_of_pos
    (sum_nonneg fun n _ => Real.rpow_nonneg (by positivity) _)
    (div_pos (Real.rpow_pos_of_pos hNR _) (by linarith))

theorem backlundDirichletEnvelope_antitone {N : ℕ} (hN : 1 ≤ N) :
    AntitoneOn (backlundDirichletEnvelope N) (Ioi 1) := by
  intro x hx y _ hxy
  have hx1 : 1 < x := hx
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold backlundDirichletEnvelope
  apply add_le_add
  · apply sum_le_sum
    intro n _
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n])
      (by linarith)
  · apply div_le_div₀ (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hNR (by linarith)) (by linarith)
    linarith

theorem backlund_right_dirichlet_log_bound {T : ℝ} {s : ℂ}
    (hs : 0 ≤ s.re) {N : ℕ} (hN : 1 ≤ N) :
    backlundCircleEnvelope T s ≤ Real.log (backlundDirichletEnvelope N (s.re + 5 / 4)) := by
  have hbound (w : ℂ) (hw : w.re = s.re + 5 / 4) :
      Real.log ‖riemannZeta w‖ ≤ Real.log (backlundDirichletEnvelope N (s.re + 5 / 4)) := by
    have hw1 : 1 < w.re := by rw [hw]; linarith
    have h := backlund_zeta_dirichlet_envelope hw1 hN
    rw [hw] at h
    exact Real.log_le_log (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hw1)) h
  exact max_le (hbound _ (by simp)) (hbound _ (by simp))

#print axioms backlund_dirichlet_tail
#print axioms backlund_zeta_dirichlet_envelope
#print axioms backlundDirichletEnvelope_pos
#print axioms backlundDirichletEnvelope_antitone
#print axioms backlund_right_dirichlet_log_bound

end LiuWang.Proof.Campaign20260915.RosserCount
