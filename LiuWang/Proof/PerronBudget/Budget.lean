import LiuWang.Proof.PerronBudget.ScalarBounds

/-!
# Payment of every term in `closedRealEndpointError`

The two half-integer errors cost at most `1.362`, the independent-height
correction `0.01`, and endpoint transport and `log 2` each `0.001`.
Thus the stronger total `1.374` is available before the printed `1.38022`.
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ExplicitPerron

namespace LiuWang.Proof.PerronBudget

theorem source_series_factor_div_pi {L : ℝ} (hL : 2000 ≤ L) :
    (Real.log 4 + 4) * (1 + 1 / L) / ((1 + 1 / L) - 1) / Real.pi ≤
      2.01 * L := by
  have hL0 : 0 < L := by linarith
  apply (div_le_iff₀ Real.pi_pos).mpr
  have hh := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
    (show 0 ≤ 2.01 * L by positivity)
  nlinarith [(source_series_factor hL).2]

theorem closedHalfError_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {x : ℝ} (hx : 1 ≤ x) (hxN : x ≤ 2 * (N : ℝ)) :
    closedHalfError x (1 + 1 / sourceL N) (sourceT N) ≤
      1.36 * x / sourceT N * sourceL N ^ (2 : ℕ) := by
  let L := sourceL N
  let C := (Real.log 4 + 4) * (1 + 1 / L) / ((1 + 1 / L) - 1)
  have hL : 2000 ≤ L := sourceL_ge_2000 hN
  have hL0 : 0 < L := sourceL_pos hN
  have hT0 := sourceT_pos hN
  have hx0 : 0 < x := by linarith
  have hLL : 2000 * L ≤ L ^ (2 : ℕ) := by
    nlinarith [mul_le_mul_of_nonneg_right hL hL0.le]
  obtain ⟨hC0, hC⟩ := source_series_factor hL
  change 0 ≤ C at hC0
  change C ≤ 6.01 * L at hC
  have hlog2 : 0 < Real.log 2 := by linarith [log_two_bounds.1]
  have hdiv : x ^ (1 + 1 / L) / Real.log 2 ≤ 18 * x := by
    apply (div_le_iff₀ hlog2).mpr
    have hh := mul_le_mul_of_nonneg_left log_two_bounds.1 (show 0 ≤ 18 * x by positivity)
    nlinarith [source_rpow_le_nine_mul hN hx hxN]
  have hspectral : x ^ (1 + 1 / L) / Real.log 2 * C ≤ 0.06 * x * L ^ (2 : ℕ) := by
    have hc : 18 * (6.01 * L) ≤ 0.06 * L ^ (2 : ℕ) := by nlinarith
    calc
      _ ≤ (18 * x) * (6.01 * L) := mul_le_mul hdiv hC hC0 (by positivity)
      _ = x * (18 * (6.01 * L)) := by ring
      _ ≤ x * (0.06 * L ^ (2 : ℕ)) := mul_le_mul_of_nonneg_left hc hx0.le
      _ = _ := by ring
  obtain ⟨hlx0, hlx, hl2x0, hl2x⟩ := source_log_bounds hN hx hxN
  change Real.log x ≤ L + 1 at hlx
  change Real.log (2 * x) ≤ L + 2 at hl2x
  have ha : Real.log x ≤ 1.0005 * L := by linarith
  have ha3 : Real.log x + 3 ≤ 1.002 * L := by linarith
  have hb : Real.log (2 * x) ≤ 1.001 * L := by linarith
  have hb3 : Real.log (2 * x) + 3 ≤ 1.0025 * L := by linarith
  have hpoly :
      2 ^ (1 + 1 / L) * Real.log x * (Real.log x + 3) +
        Real.log (2 * x) * (Real.log (2 * x) + 3) ≤ 4.02 * L ^ (2 : ℕ) := by
    calc
      _ ≤ 3 * (1.0005 * L) * (1.002 * L) + (1.001 * L) * (1.0025 * L) := by
        gcongr
        exact source_two_rpow_le_three hL
      _ ≤ _ := by nlinarith [sq_nonneg L]
  have hnum :
      x ^ (1 + 1 / L) / Real.log 2 * C +
        x * (2 ^ (1 + 1 / L) * Real.log x * (Real.log x + 3) +
          Real.log (2 * x) * (Real.log (2 * x) + 3)) ≤ 4.08 * x * L ^ (2 : ℕ) := by
    nlinarith [mul_le_mul_of_nonneg_left hpoly hx0.le]
  change (_ + _) / (Real.pi * sourceT N) ≤ 1.36 * x / sourceT N * L ^ (2 : ℕ)
  calc
    _ ≤ (4.08 * x * L ^ (2 : ℕ)) / (Real.pi * sourceT N) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (4.08 / Real.pi) * (x / sourceT N * L ^ (2 : ℕ)) := by ring
    _ ≤ 1.36 * (x / sourceT N * L ^ (2 : ℕ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply (div_le_iff₀ Real.pi_pos).mpr
      linarith [Real.pi_gt_three]
    _ = _ := by ring

theorem closedHalfErrors_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    closedHalfError (halfCutoff t) (1 + 1 / sourceL N) (sourceT N) +
        closedHalfError (5 / 2) (1 + 1 / sourceL N) (sourceT N) ≤
      1.362 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  obtain ⟨htbig, hx, hxN, hyN, hxy, _⟩ := source_cutoff_bounds hN htlo hthi
  have ht0 : 0 ≤ t := by linarith
  have hT0 := sourceT_pos hN
  have hsum := add_le_add (closedHalfError_le hN hx hxN)
    (closedHalfError_le hN (by norm_num : (1 : ℝ) ≤ 5 / 2) hyN)
  calc
    _ ≤ 1.36 * halfCutoff t / sourceT N * sourceL N ^ (2 : ℕ) +
        1.36 * (5 / 2) / sourceT N * sourceL N ^ (2 : ℕ) := hsum
    _ = 1.36 * (halfCutoff t + 5 / 2) / sourceT N * sourceL N ^ (2 : ℕ) := by ring
    _ ≤ 1.36 * (1.001 * t) / sourceT N * sourceL N ^ (2 : ℕ) := by gcongr
    _ ≤ _ := by
      have hh : (0 : ℝ) ≤ t / sourceT N * sourceL N ^ (2 : ℕ) := by positivity
      simp only [div_eq_mul_inv] at hh ⊢
      nlinarith

theorem heightCorrection_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    heightCorrection (halfCutoff t) (5 / 2) (1 + 1 / sourceL N) (sourceT N) ≤
      0.01 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  let L := sourceL N
  let T := sourceT N
  let x := halfCutoff t
  let b := 1 + 1 / L
  let C := (Real.log 4 + 4) * b / (b - 1)
  have hL : 2000 ≤ L := sourceL_ge_2000 hN
  have hL0 : 0 < L := sourceL_pos hN
  have hT0 : 0 < T := sourceT_pos hN
  have hTbig : 1001 ≤ T :=
    (by norm_num : (1001 : ℝ) ≤ 2000 ^ (15 : ℕ)).trans
      (pow_le_pow_left₀ (by norm_num) hL 15)
  have hTm0 : 0 < T - 1 := by linarith
  obtain ⟨htbig, hx, hxN, hyN, hxy, _⟩ := source_cutoff_bounds hN htlo hthi
  have ht0 : 0 < t := by linarith
  have hratio : T / (T - 1) ≤ 1.001 := (div_le_iff₀ hTm0).mpr (by linarith)
  have hden : t / (T - 1) ≤ 1.001 * (t / T) := by
    have hh := mul_le_mul_of_nonneg_right hratio (show 0 ≤ t / T by positivity)
    convert hh using 1 <;> first | rfl | field_simp
  have hkernel : (x + 5 / 2) / (T - 1) ≤ 1.001 ^ (2 : ℕ) * (t / T) := by
    calc
      _ ≤ (1.001 * t) / (T - 1) := div_le_div_of_nonneg_right hxy hTm0.le
      _ = 1.001 * (t / (T - 1)) := by ring
      _ ≤ 1.001 * (1.001 * (t / T)) := mul_le_mul_of_nonneg_left hden (by norm_num)
      _ = _ := by ring
  have hp : x ^ b + (5 / 2 : ℝ) ^ b ≤ 9 * (x + 5 / 2) := by
    have hh := source_rpow_le_nine_mul hN hx hxN
    have hh' := source_rpow_le_nine_mul hN (by norm_num : (1 : ℝ) ≤ 5 / 2) hyN
    change x ^ b ≤ 9 * x at hh
    change (5 / 2 : ℝ) ^ b ≤ 9 * (5 / 2) at hh'
    linarith
  have hpk : (x ^ b + (5 / 2 : ℝ) ^ b) / (T - 1) ≤
      9 * 1.001 ^ (2 : ℕ) * (t / T) := by
    calc
      _ ≤ (9 * (x + 5 / 2)) / (T - 1) := div_le_div_of_nonneg_right hp hTm0.le
      _ = 9 * ((x + 5 / 2) / (T - 1)) := by ring
      _ ≤ 9 * (1.001 ^ (2 : ℕ) * (t / T)) :=
        mul_le_mul_of_nonneg_left hkernel (by norm_num)
      _ = _ := by ring
  have hc : 2.01 * 9 * 1.001 ^ (2 : ℕ) * L ≤ 0.01 * L ^ (2 : ℕ) := by
    nlinarith [mul_le_mul_of_nonneg_right hL hL0.le]
  change C * (x ^ b + (5 / 2 : ℝ) ^ b) / (Real.pi * (T - 1)) ≤
    0.01 * t / T * L ^ (2 : ℕ)
  calc
    _ = (C / Real.pi) * ((x ^ b + (5 / 2 : ℝ) ^ b) / (T - 1)) := by
      rw [div_mul_div_comm]
    _ ≤ (2.01 * L) * (9 * 1.001 ^ (2 : ℕ) * (t / T)) :=
      mul_le_mul (source_series_factor_div_pi hL) hpk (by positivity) (by positivity)
    _ = (2.01 * 9 * 1.001 ^ (2 : ℕ) * L) * (t / T) := by ring
    _ ≤ (0.01 * L ^ (2 : ℕ)) * (t / T) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem transportCorrection_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t Hminus Hplus : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ))
    (hminus : |Hminus + sourceT N| ≤ 1) (hplus : |Hplus - sourceT N| ≤ 1) :
    transportCorrection t (1 + 1 / sourceL N) Hminus Hplus ≤
      0.001 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  let L := sourceL N
  let T := sourceT N
  let C := (Real.log 4 + 4) * (1 + 1 / L) / ((1 + 1 / L) - 1)
  have hL : 2000 ≤ L := sourceL_ge_2000 hN
  have hL0 : 0 < L := sourceL_pos hN
  have hT0 : 0 < T := sourceT_pos hN
  have hT1 : 1 ≤ T := one_le_pow₀ (one_le_sourceL hN)
  obtain ⟨htbig, hx, _, _, _, hmax⟩ := source_cutoff_bounds hN htlo hthi
  have ht0 : 0 < t := by linarith
  have hr : (max (halfCutoff t) t) ^ (1 / L) ≤ 9 :=
    source_rpow_small hN (hx.trans (le_max_left _ _)) hmax
  have hgap : |Hplus - Hminus| ≤ 4 * T := by
    obtain ⟨hm1, hm2⟩ := abs_le.mp hminus
    obtain ⟨hp1, hp2⟩ := abs_le.mp hplus
    change -1 ≤ Hminus + T at hm1
    change Hminus + T ≤ 1 at hm2
    change -1 ≤ Hplus - T at hp1
    change Hplus - T ≤ 1 at hp2
    rw [abs_le]
    constructor <;> linarith
  have hcoarse : transportCorrection t (1 + 1 / L) Hminus Hplus ≤ 19 * L * T := by
    calc
      _ = (C / Real.pi) * (max (halfCutoff t) t) ^ (1 / L) *
          (1 / 2) * |Hplus - Hminus| / 2 := by
        unfold transportCorrection C
        rw [show 1 + 1 / L - 1 = 1 / L by ring]
        ring
      _ ≤ (2.01 * L) * 9 * (1 / 2) * (4 * T) / 2 := by
        gcongr
        exact source_series_factor_div_pi hL
      _ ≤ _ := by nlinarith [mul_pos hL0 hT0]
  apply hcoarse.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hT0).mpr
  have htp : T ^ (2 : ℕ) ≤ t / 1000000 := by
    have hh := million_sourceT_sq_le_endpoint hN htlo
    change 1000000 * T ^ (2 : ℕ) ≤ t at hh
    linarith
  have hc : (19 / 1000000 : ℝ) * L ≤ 0.001 * L ^ (2 : ℕ) := by
    nlinarith [mul_le_mul_of_nonneg_right hL hL0.le]
  calc
    _ = (19 * L) * T ^ (2 : ℕ) := by ring
    _ ≤ (19 * L) * (t / 1000000) := mul_le_mul_of_nonneg_left htp (by positivity)
    _ = ((19 / 1000000 : ℝ) * L) * t := by ring
    _ ≤ (0.001 * L ^ (2 : ℕ)) * t := mul_le_mul_of_nonneg_right hc ht0.le
    _ = _ := by ring

theorem log_two_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) :
    Real.log 2 ≤ 0.001 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  have hT0 := sourceT_pos hN
  have hratio : 1000000 ≤ t / sourceT N :=
    (le_div_iff₀ hT0).mpr (LocalAnalyticBounds.LeftVertical.million_sourceT_le_endpoint hN htlo)
  have hsq : 1 ≤ sourceL N ^ (2 : ℕ) := one_le_pow₀ (one_le_sourceL hN)
  have hh := mul_le_mul hratio hsq (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : 0 ≤ t / sourceT N)
  have hlog := log_two_bounds.2
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith

theorem closedRealEndpointError_le_stronger {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) {t Hminus Hplus : ℝ}
    (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ))
    (hminus : |Hminus + sourceT N| ≤ 1) (hplus : |Hplus - sourceT N| ≤ 1) :
    closedRealEndpointError t (1 + 1 / sourceL N) (sourceT N) Hminus Hplus ≤
      1.374 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  have hh := closedHalfErrors_source_le hN htlo hthi
  have hc := heightCorrection_source_le hN htlo hthi
  have ht := transportCorrection_source_le hN htlo hthi hminus hplus
  have hl := log_two_source_le hN htlo
  unfold closedRealEndpointError
  calc
    _ ≤ ((1.362 * t / sourceT N * sourceL N ^ (2 : ℕ) +
        0.001 * t / sourceT N * sourceL N ^ (2 : ℕ)) +
        0.01 * t / sourceT N * sourceL N ^ (2 : ℕ)) +
        0.001 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
      add_le_add (add_le_add (add_le_add hh hl) hc) ht
    _ = _ := by ring

theorem closedRealEndpointError_le_source {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) {t Hminus Hplus : ℝ}
    (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ))
    (hminus : |Hminus + sourceT N| ≤ 1) (hplus : |Hplus - sourceT N| ≤ 1) :
    closedRealEndpointError t (1 + 1 / sourceL N) (sourceT N) Hminus Hplus ≤
      1.38022 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  apply (closedRealEndpointError_le_stronger hN htlo hthi hminus hplus).trans
  have ht0 : 0 < t := (sourceT_pos hN).trans (sourceT_lt_real_endpoint hN htlo)
  have hT0 := sourceT_pos hN
  gcongr
  norm_num

end LiuWang.Proof.PerronBudget
