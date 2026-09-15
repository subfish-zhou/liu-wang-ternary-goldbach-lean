import LiuWang.Proof.PerronRecovery.Scalar

/-! Every term of the recovered source error is paid on the unchanged window.
The mother function remains public; the decimal is only a corollary. -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.PerronRecovery

open ExplicitPerron PerronBudget Interfaces Parameters

theorem halfErrors_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    halfError (halfCutoff t) (1 + 1 / sourceL N) (sourceT N) (sourceL N + 8) +
        halfError (5 / 2) (1 + 1 / sourceL N) (sourceT N) (sourceL N + 8) ≤
      0.96096 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  obtain ⟨htbig, hx, hxN, hyN, hxy, _⟩ := source_cutoff_bounds hN htlo hthi
  have hT0 := sourceT_pos hN
  calc
    _ ≤ 0.96 * halfCutoff t / sourceT N * sourceL N ^ (2 : ℕ) +
        0.96 * (5 / 2) / sourceT N * sourceL N ^ (2 : ℕ) :=
      add_le_add (halfError_source_le hN hx hxN)
        (halfError_source_le hN (by norm_num) hyN)
    _ = 0.96 * (halfCutoff t + 5 / 2) / sourceT N * sourceL N ^ (2 : ℕ) := by ring
    _ ≤ 0.96 * (1.001 * t) / sourceT N * sourceL N ^ (2 : ℕ) := by gcongr
    _ = _ := by ring

theorem heightError_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    heightError (halfCutoff t) (5 / 2) (1 + 1 / sourceL N) (sourceT N) (sourceL N + 8) ≤
      0.000482 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  let L := sourceL N
  let T := sourceT N
  let x := halfCutoff t
  let b := 1 + 1 / L
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
  have hp : x ^ b + (5 / 2 : ℝ) ^ b ≤ 3 * (1.001 * t) := by
    have hh := add_le_add (rpow_source_le hN hx hxN)
      (rpow_source_le hN (by norm_num : (1 : ℝ) ≤ 5 / 2) hyN)
    change x ^ b + (5 / 2 : ℝ) ^ b ≤ 3 * x + 3 * (5 / 2) at hh
    change x + 5 / 2 ≤ 1.001 * t at hxy
    linarith
  have hpk : (x ^ b + (5 / 2 : ℝ) ^ b) / (T - 1) ≤
      3 * 1.001 ^ (2 : ℕ) * (t / T) := by
    calc
      _ ≤ (3 * (1.001 * t)) / (T - 1) := by gcongr
      _ = (3 * 1.001) * (t / (T - 1)) := by ring
      _ ≤ (3 * 1.001) * (1.001 * (t / T)) :=
        mul_le_mul_of_nonneg_left hden (by norm_num)
      _ = _ := by ring
  have hc : 0.32 * 3 * 1.001 ^ (2 : ℕ) * L ≤ 0.000482 * L ^ (2 : ℕ) := by
    nlinarith [mul_le_mul_of_nonneg_right hL hL0.le]
  change (L + 8) * (x ^ b + (5 / 2 : ℝ) ^ b) / (Real.pi * (T - 1)) ≤
    0.000482 * t / T * L ^ (2 : ℕ)
  calc
    _ = ((L + 8) / Real.pi) * ((x ^ b + (5 / 2 : ℝ) ^ b) / (T - 1)) :=
      (div_mul_div_comm _ _ _ _).symm
    _ ≤ (0.32 * L) * (3 * 1.001 ^ (2 : ℕ) * (t / T)) :=
      mul_le_mul (series_factor_source_le hL).2 hpk (by positivity) (by positivity)
    _ = (0.32 * 3 * 1.001 ^ (2 : ℕ) * L) * (t / T) := by ring
    _ ≤ (0.000482 * L ^ (2 : ℕ)) * (t / T) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem endpointFunction_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    (sourceL N + 8) * (max (halfCutoff t) t) ^ (1 / sourceL N) *
        (sourceT N + 1) / (2 * Real.pi) ≤
      0.000001 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  let L := sourceL N
  let T := sourceT N
  have hL : 2000 ≤ L := sourceL_ge_2000 hN
  have hL0 : 0 < L := sourceL_pos hN
  have hT0 : 0 < T := sourceT_pos hN
  have hT1 : 1 ≤ T := one_le_pow₀ (one_le_sourceL hN)
  obtain ⟨htbig, hx, _, _, _, hmax⟩ := source_cutoff_bounds hN htlo hthi
  have ht0 : 0 < t := by linarith
  have hr : (max (halfCutoff t) t) ^ (1 / L) ≤ 3 :=
    rpow_small_source_le hN (hx.trans (le_max_left _ _)) hmax
  have hcoarse :
      (L + 8) * (max (halfCutoff t) t) ^ (1 / L) * (T + 1) / (2 * Real.pi) ≤ L * T := by
    calc
      _ = ((L + 8) / Real.pi) * (max (halfCutoff t) t) ^ (1 / L) * (T + 1) / 2 := by ring
      _ ≤ (0.32 * L) * 3 * (2 * T) / 2 := by
        gcongr
        · exact (series_factor_source_le hL).2
        · linarith
      _ ≤ _ := by nlinarith [mul_pos hL0 hT0]
  apply hcoarse.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hT0).mpr
  have htp : T ^ (2 : ℕ) ≤ t / 1000000 := by
    have hh := million_sourceT_sq_le_endpoint hN htlo
    change 1000000 * T ^ (2 : ℕ) ≤ t at hh
    linarith
  have hc : (1 / 1000000 : ℝ) * L ≤ 0.000001 * L ^ (2 : ℕ) := by nlinarith
  calc
    _ = L * T ^ (2 : ℕ) := by ring
    _ ≤ L * (t / 1000000) := mul_le_mul_of_nonneg_left htp hL0.le
    _ = ((1 / 1000000 : ℝ) * L) * t := by ring
    _ ≤ (0.000001 * L ^ (2 : ℕ)) * t := mul_le_mul_of_nonneg_right hc ht0.le
    _ = _ := by ring

theorem log_two_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) :
    Real.log 2 ≤ 0.000001 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  have hT0 := sourceT_pos hN
  have hratio : 1000000 ≤ t / sourceT N :=
    (le_div_iff₀ hT0).mpr (LocalAnalyticBounds.LeftVertical.million_sourceT_le_endpoint hN htlo)
  have hsq : 1 ≤ sourceL N ^ (2 : ℕ) := one_le_pow₀ (one_le_sourceL hN)
  have hh := mul_le_mul hratio hsq (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : 0 ≤ t / sourceT N)
  have hlog := log_two_bounds.2
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith

theorem sourceError_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    sourceError N t ≤ 0.961444 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  have hh := halfErrors_source_le hN htlo hthi
  have hc := heightError_source_le hN htlo hthi
  have ht := endpointFunction_source_le hN htlo hthi
  have hl := log_two_source_le hN htlo
  unfold sourceError errorFunction
  rw [show 1 + 1 / sourceL N - 1 = 1 / sourceL N by ring]
  calc
    _ ≤ ((0.96096 * t / sourceT N * sourceL N ^ (2 : ℕ) +
        0.000001 * t / sourceT N * sourceL N ^ (2 : ℕ)) +
        0.000482 * t / sourceT N * sourceL N ^ (2 : ℕ)) +
        0.000001 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
      add_le_add (add_le_add (add_le_add hh hl) hc) ht
    _ = _ := by ring

theorem source_right_perron_le {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hN : Real.exp 2000 ≤ (N : ℝ))
    {t lo hi : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ))
    (hlo : |lo + sourceT N| ≤ 1) (hhi : |hi - sourceT N| ≤ 1) :
    ‖vertical (centeredIntegrand chi t (5 / 2)) (1 + 1 / sourceL N) lo hi -
      psi chi t‖ ≤ 0.961444 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
  (source_right_perron_function chi hN htlo hlo hhi).trans (sourceError_le hN htlo hthi)

end LiuWang.Proof.PerronRecovery
