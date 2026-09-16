import LiuWang.Proof.Campaign20260915.RosserCount.BacklundStripMaximum

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_zeta_middle_growth_positive {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (ht : 1000 ≤ s.im) :
    ‖riemannZeta s‖ < (s.im ^ 2 / (s.im ^ 2 - 4)) *
      (s.im / (2 * Real.pi)) ^ ((1 - s.re) / 2) * Real.log s.im := by
  have hd : 0 < s.im ^ 2 - 4 := by nlinarith
  have hr : 0 < (s.im / (2 * Real.pi)) ^ ((1 - s.re) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hl : 0 < Real.log s.im := Real.log_pos (by linarith)
  have hf := backlundStripPhi_lt_one hs hs' (by linarith)
  have h1 := mul_lt_mul_of_pos_right hf
    (show 0 < s.im ^ 2 / (s.im ^ 2 - 4) by positivity)
  rw [one_mul] at h1
  exact (backlund_zeta_le_original_Phi_bound hs hs' ht).trans_lt
    (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right h1 hr) hl)

theorem backlund_zeta_middle_growth {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (ht : 1000 ≤ |s.im|) :
    ‖riemannZeta s‖ < (|s.im| ^ 2 / (|s.im| ^ 2 - 4)) *
      (|s.im| / (2 * Real.pi)) ^ ((1 - s.re) / 2) * Real.log |s.im| := by
  by_cases hy : 0 ≤ s.im
  · rw [abs_of_nonneg hy] at ht ⊢
    exact backlund_zeta_middle_growth_positive hs hs' ht
  · have hc : 1000 ≤ (conj s).im := by
      simpa only [conj_im, abs_of_neg (lt_of_not_ge hy)] using ht
    have h := backlund_zeta_middle_growth_positive
      (s := conj s) (by simpa using hs) (by simpa using hs') hc
    simpa only [conj_re, conj_im, riemannZeta_conj, norm_conj,
      abs_of_neg (lt_of_not_ge hy)] using h

#print axioms backlund_zeta_middle_growth_positive
#print axioms backlund_zeta_middle_growth

end LiuWang.Proof.Campaign20260915.RosserCount
