import LiuWang.Proof.SourceRoute.ThirdArc.PrimeBridge
import LiuWang.Proof.MajorArcApproximation.Error
import LiuWang.Proof.ArcGeometry.Main

/-! Restored middle-arc expansion payment, plus the actual prime-power budget. -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion

namespace LiuWang.Proof.SourceRoute.ThirdArc

theorem middle_eta_scale {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq0 : sourceP N < (q : ℝ)) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    (N : ℝ) * |eta| ≤ sourceL N ^ 4 := by
  have hL := sourceL_pos hN
  have hq : (0 : ℝ) < q := (sourceP_pos hN).trans hq0
  have hx : 0 ≤ (N : ℝ) * |eta| := by positivity
  apply le_of_mul_le_mul_left (a := sourceL N ^ 3) ?_ (pow_pos hL 3)
  calc
    sourceL N ^ 3 * ((N : ℝ) * |eta|) ≤ (q : ℝ) * ((N : ℝ) * |eta|) :=
      mul_le_mul_of_nonneg_right hq0.le hx
    _ ≤ sourceL N ^ 7 := by
      have h := (le_div_iff₀ (mul_pos hq (natCast_pos_of_exp_le hN))).mp heta
      nlinarith
    _ = sourceL N ^ 3 * sourceL N ^ 4 := by ring

theorem middle_error_le {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq0 : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    errorBound q N a eta ≤ 11 * (N : ℝ) / sourceL N ^ 6 := by
  have hL := sourceL_pos hN
  have hT := sourceT_pos hN
  have hn := natCast_pos_of_exp_le hN
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hx0 : 0 ≤ (N : ℝ) * |eta| := by positivity
  have hx := middle_eta_scale hN hq0 heta
  have hL3 : 1 ≤ sourceL N ^ 3 := one_le_pow₀ (one_le_sourceL hN)
  have hL4 : 1 ≤ sourceL N ^ 4 := one_le_pow₀ (one_le_sourceL hN)
  have hnp : nonprincipalMass q a ≤ sourceL N ^ 3 := by
    apply (nonprincipalMass_le_modulus q a).trans
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    convert hq1 using 1
    unfold sourceP1
    ring
  have hp : principalMass q ≤ sourceL N ^ 3 :=
    (MajorArcApproximation.principalMass_le_one (NeZero.pos q)).trans hL3
  have hcoef :
      principalMass q * (0.963362 + 3.02347 * (N : ℝ) * |eta|) +
        nonprincipalMass q a * (0.96258 + 3.02102 * (N : ℝ) * |eta|) ≤
      10 * sourceL N ^ 7 := by
    calc
      _ ≤ sourceL N ^ 3 * (5 * sourceL N ^ 4) +
          sourceL N ^ 3 * (5 * sourceL N ^ 4) := by
        apply add_le_add
        · apply mul_le_mul hp _ (by positivity) (by positivity)
          nlinarith
        · apply mul_le_mul hnp _ (by positivity) (by positivity)
          nlinarith
      _ = _ := by ring
  have hlogq : Real.log q ≤ sourceL N ^ 6 :=
    (by linarith [Real.log_le_sub_one_of_pos hq] : Real.log q ≤ (q : ℝ)).trans hq1
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hcorr : Real.log q * sourceL N / Real.log 2 ≤ (N : ℝ) / sourceL N ^ 6 := by
    calc
      _ ≤ 2 * sourceL N ^ 7 := by
        apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
        have hh := mul_le_mul_of_nonneg_right hlogq hL.le
        have he : sourceL N ^ 6 * sourceL N = sourceL N ^ 7 := by ring
        rw [he] at hh
        nlinarith [mul_nonneg (show 0 ≤ sourceL N ^ 7 by positivity)
          (show 0 ≤ Real.log 2 - 1 / 2 by linarith)]
      _ ≤ _ := by
        apply (le_div_iff₀ (pow_pos hL 6)).mpr
        convert (mul_sourceL_pow_lt (c := 2) (k := 13) hN
          (by norm_num) (by norm_num)).le using 1
        ring
  apply (errorBound_le_decimal hN a eta).trans
  calc
    _ ≤ 10 * sourceL N ^ 7 * (N : ℝ) / sourceT N * sourceL N ^ 2 +
        (N : ℝ) / sourceL N ^ 6 := by
      apply add_le_add _ hcorr
      gcongr
    _ = _ := by
      unfold sourceT
      field_simp
      ring

theorem middle_error_paid {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq0 : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    errorBound q N a eta ≤ 0.000000000001 * (N : ℝ) / sourceL N := by
  apply (middle_error_le hN hq0 hq1 heta).trans
  have hL := sourceL_pos hN
  have hp : (11 : ℝ) ≤ 0.000000000001 * sourceL N ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2000) (sourceL_ge_2000 hN) 5
    norm_num at h
    linarith
  apply (div_le_div_iff₀ (pow_pos hL 6) hL).mpr
  have h := mul_le_mul_of_nonneg_right hp (show 0 ≤ (N : ℝ) * sourceL N by positivity)
  convert h using 1 <;> ring

theorem primePower_error_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    Real.sqrt N * sourceL N ≤ 0.000000000001 * (N : ℝ) / sourceL N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hn
  have h8 : (1000000000000000000000000 : ℝ) ≤ sourceL N ^ 8 :=
    (by norm_num : (1000000000000000000000000 : ℝ) ≤ 3100 ^ 8).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 8)
  have h12 : sourceL N ^ 12 ≤ (N : ℝ) := by
    simpa using (mul_sourceL_pow_lt (c := 1) (k := 12) hn
      (by norm_num) (by norm_num)).le
  have hs : 1000000000000 * sourceL N ^ 2 ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    calc
      _ = 1000000000000000000000000 * sourceL N ^ 4 := by ring
      _ ≤ sourceL N ^ 8 * sourceL N ^ 4 :=
        mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = sourceL N ^ 12 := by ring
      _ ≤ _ := h12
  apply (le_div_iff₀ hL).mpr
  have hh := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (N : ℝ))
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
  nlinarith

theorem primeS_M3_fixed {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq0 : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    ‖primeS N (rationalCenter a q + eta)‖ ≤
      principalMass q * (0.999 * (N : ℝ)) + (sigma4 N q + sigma5 N q + sigma6 N q) +
        0.000000000002 * (N : ℝ) / sourceL N := by
  have h := primeS_three_bands hN hi hq1 heta
  have he := middle_error_paid (a := a) (exp_2000_le_of_exp_3100_le hN) hq0 hq1 heta
  have hp := primePower_error_paid hN
  exact (h.trans (add_le_add (add_le_add (add_le_add le_rfl he) le_rfl) hp)).trans_eq
    (by ring)

theorem S_M3_fixed {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq0 : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      principalMass q * (0.999 * (N : ℝ)) + (sigma4 N q + sigma5 N q + sigma6 N q) +
        0.000000000001 * (N : ℝ) / sourceL N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  exact ((S_three_bands hn hi hq1 heta).trans
    (add_le_add (add_le_add le_rfl (middle_error_paid hn hq0 hq1 heta)) le_rfl)).trans_eq
      (by ring)

theorem primeS_M3_same_witness {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M3 N) :
    ∃ (q a : ℕ) (eta : ℝ) (hq : 0 < q),
      let : NeZero q := ⟨hq.ne'⟩
      sourceL N ^ 3 < (q : ℝ) ∧ (q : ℝ) ≤ sourceL N ^ 6 ∧
      sourceIndex a q ∧ alpha = rationalCenter a q + eta ∧
      |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N) ∧
      ‖primeS N alpha‖ ≤
        principalMass q * (0.999 * (N : ℝ)) + (sigma4 N q + sigma5 N q + sigma6 N q) +
          0.000000000002 * (N : ℝ) / sourceL N := by
  obtain ⟨q, a, eta, hq0, hq1, hi, he, heta⟩ := ArcGeometry.M3_eta_range ha
  have hq := ArcGeometry.sourceIndex_den_pos hi
  let : NeZero q := ⟨hq.ne'⟩
  rw [approximationRadius_eq (exp_2000_le_of_exp_3100_le hN) hq] at heta
  refine ⟨q, a, eta, hq, hq0, hq1, hi, he, heta, ?_⟩
  rw [he]
  exact primeS_M3_fixed hN hi hq0 hq1 heta

theorem M3_same_witness {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M3 N) :
    ∃ (q a : ℕ) (eta : ℝ) (hq : 0 < q),
      let : NeZero q := ⟨hq.ne'⟩
      sourceL N ^ 3 < (q : ℝ) ∧ (q : ℝ) ≤ sourceL N ^ 6 ∧
      sourceIndex a q ∧ alpha = rationalCenter a q + eta ∧
      |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N) ∧
      ‖S N alpha‖ ≤
        principalMass q * (0.999 * (N : ℝ)) + (sigma4 N q + sigma5 N q + sigma6 N q) +
          0.000000000001 * (N : ℝ) / sourceL N := by
  obtain ⟨q, a, eta, hq0, hq1, hi, he, heta⟩ := ArcGeometry.M3_eta_range ha
  have hq := ArcGeometry.sourceIndex_den_pos hi
  let : NeZero q := ⟨hq.ne'⟩
  rw [approximationRadius_eq (exp_2000_le_of_exp_3100_le hN) hq] at heta
  refine ⟨q, a, eta, hq, hq0, hq1, hi, he, heta, ?_⟩
  rw [he]
  exact S_M3_fixed hN hi hq0 hq1 heta

end LiuWang.Proof.SourceRoute.ThirdArc
