import LiuWang.Proof.NonSymmetricContour.Kernel
import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Budget

/-! # 水平预算与实际原点留数的数值支付 -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.LocalAnalyticBounds
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.NonSymmetricContour

theorem log_le_div_250 {x : Real} (hx : 2000 ≤ x) :
    Real.log x ≤ x / 250 := by
  have hx0 : 0 < x := by linarith
  have he : (2000 : Real) ≤ Real.exp 8 := by
    calc
      _ ≤ (2.7 : Real) ^ (8 : Nat) := by norm_num
      _ ≤ (Real.exp 1) ^ (8 : Nat) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hbase : Real.log 2000 ≤ 8 := (Real.log_le_iff_le_exp (by norm_num)).mpr he
  have hr := Real.log_le_sub_one_of_pos (div_pos hx0 (by norm_num : (0 : Real) < 2000))
  rw [Real.log_div hx0.ne' (by norm_num)] at hr
  linarith

theorem source_log_qT_bounds {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) :
    0 ≤ Real.log ((q : Real) * sourceT N) ∧
      Real.log ((q : Real) * sourceT N) ≤ (21 / 250 : Real) * sourceL N := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have hT0 := sourceT_pos hN
  have hq0 : (0 : Real) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : Real) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hqlog : Real.log q ≤ 6 * Real.log (sourceL N) := by
    have hh := Real.log_le_log hq0 hqUpper
    change Real.log q ≤ Real.log (sourceL N ^ (6 : Nat)) at hh
    simpa [Real.log_pow] using hh
  rw [Real.log_mul hq0.ne' hT0.ne', log_sourceT]
  constructor
  · have hl0 := Real.log_nonneg (show 1 ≤ sourceL N by linarith)
    linarith [Real.log_nonneg hq1]
  · linarith [log_le_div_250 hL]

theorem horizontal_cost_le_budget {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) {t : Real}
    (htlo : sourceWindowLower N ≤ t) :
    0.0014 * t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2 ≤
      0.0000099 * t / sourceT N * sourceL N ^ (2 : Nat) := by
  obtain ⟨hlo, hhi⟩ := source_log_qT_bounds hN hq hqUpper
  have hL0 := sourceL_pos hN
  have hT0 := sourceT_pos hN
  have ht0 : 0 < t := hT0.trans (sourceT_lt_real_endpoint hN htlo)
  have hs : (Real.log ((q : Real) * sourceT N)) ^ 2 ≤
      ((21 / 250 : Real) * sourceL N) ^ 2 := by
    nlinarith [mul_self_le_mul_self hlo hhi]
  calc
    _ ≤ 0.0014 * t / sourceT N * ((21 / 250 : Real) * sourceL N) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 0.0000098784 * (t / sourceT N * sourceL N ^ (2 : Nat)) := by ring
    _ ≤ 0.0000099 * (t / sourceT N * sourceL N ^ (2 : Nat)) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by ring

theorem norm_origin_le_budget {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    ‖(lFunctionOriginMultiplicity chi : Complex) * (Real.log (t / 2.5) : Complex)‖ ≤
      0.0000001 * t / sourceT N * sourceL N ^ (2 : Nat) := by
  obtain ⟨_, htbig, _, htlog, _⟩ := HorizontalEstimate.source_horizontal_parameters hN htlo hthi
  have ht0 : 0 < t := by linarith
  have hL := sourceL_ge_2000 hN
  have hT0 := sourceT_pos hN
  have hlog0 : 0 ≤ Real.log (t / 2.5) := Real.log_nonneg
    ((le_div_iff₀ (by norm_num : (0 : Real) < 2.5)).mpr (by linarith))
  have hloghi : Real.log (t / 2.5) ≤ sourceL N := by
    rw [Real.log_div ht0.ne' (by norm_num)]
    linarith [Real.log_nonneg (by norm_num : (1 : Real) ≤ 2.5)]
  have hm : (lFunctionOriginMultiplicity chi : Real) ≤ 1 := by
    exact_mod_cast lFunctionOriginMultiplicity_le_one hchi hPrimitive
  have hr : (1 / 10 : Real) ≤ 0.0000001 * t / sourceT N := by
    apply (le_div_iff₀ hT0).mpr
    linarith [LeftVertical.million_sourceT_le_endpoint hN htlo]
  calc
    _ = (lFunctionOriginMultiplicity chi : Real) * Real.log (t / 2.5) := by
      simp [Complex.norm_real, abs_of_nonneg hlog0]
    _ ≤ Real.log (t / 2.5) := by nlinarith
    _ ≤ sourceL N := hloghi
    _ ≤ (1 / 10 : Real) * sourceL N ^ (2 : Nat) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hr (sq_nonneg _)

theorem threeSides_and_origin_cost_le_budget {N q : Nat} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 3 ≤ q)
    (hqUpper : (q : Real) ≤ sourceP1 N) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    (0.0014 * t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2 +
      (1 / 100000 : Real) * t / sourceT N * sourceL N ^ (2 : Nat)) +
      ‖(lFunctionOriginMultiplicity chi : Complex) * (Real.log (t / 2.5) : Complex)‖ ≤
        0.00002 * t / sourceT N * sourceL N ^ (2 : Nat) := by
  have hh := horizontal_cost_le_budget hN hq hqUpper htlo
  have ho := norm_origin_le_budget hN hchi hPrimitive htlo hthi
  calc
    _ ≤ (0.0000099 * t / sourceT N * sourceL N ^ (2 : Nat) +
        (1 / 100000 : Real) * t / sourceT N * sourceL N ^ (2 : Nat)) +
        0.0000001 * t / sourceT N * sourceL N ^ (2 : Nat) :=
      add_le_add (add_le_add hh le_rfl) ho
    _ = _ := by ring

end LiuWang.Proof.NonSymmetricContour
