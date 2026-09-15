import LiuWang.Proof.ChebyshevBound.HighHeight.HeightNumerics

/-!
# 原阈值上的实际零点总贡献

按 e^4,e^8,e^12,e^16,e^20 分层，覆盖全部带重数零点。
证明二次平滑显式公式所需的零点和范数界；本文件不声称该显式公式已建立。
-/

set_option autoImplicit false
noncomputable section

open Complex BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ChebyshevBound.HighHeight

def xiZeroWeight (x : ℝ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
  Real.exp (((riemannXiDivisorZeroValue p).re - 1) * Real.log x) /
    (riemannXiDivisorZeroValue p).im ^ 2

theorem zero_exp_le_one {x : ℝ} (hx : 3100 ≤ Real.log x) (p : RiemannXiDivisorZeroIndex) :
    Real.exp (((riemannXiDivisorZeroValue p).re - 1) * Real.log x) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (by linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).2]) (by linarith)

theorem zero_exp_height_le {x u : ℝ} (hx : 3100 ≤ Real.log x) (hu : 4 ≤ u)
    (p : RiemannXiDivisorZeroIndex) (hp : |(riemannXiDivisorZeroValue p).im| ≤ Real.exp u) :
    Real.exp (((riemannXiDivisorZeroValue p).re - 1) * Real.log x) ≤
      Real.exp (-(3100 / (20 * (u + 21 / 10)))) := by
  have hlog : 0 ≤ Real.log (|(riemannXiDivisorZeroValue p).im| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg (riemannXiDivisorZeroValue p).im])
  have hheight : Real.log (|(riemannXiDivisorZeroValue p).im| + 2) ≤ u + 1 / 10 :=
    (Real.log_le_log (by positivity) (add_le_add_left hp 2)).trans (log_exp_height_le hu)
  have hi : 1 / (20 * (u + 21 / 10)) ≤
      1 / (20 * (Real.log (|(riemannXiDivisorZeroValue p).im| + 2) + 2)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hgap := hi.trans (xi_zero_gap_twenty p).le
  have hc : 0 ≤ 1 / (20 * (u + 21 / 10)) := by
    apply div_nonneg zero_le_one
    linarith
  have hm := mul_le_mul_of_nonneg_right hgap (by linarith : 0 ≤ Real.log x)
  have hxmul := mul_le_mul_of_nonneg_left hx hc
  apply Real.exp_le_exp.mpr
  simp only [div_eq_mul_inv] at hm hxmul ⊢
  nlinarith only [hm, hxmul]

def xiLayerMajorant (p : RiemannXiDivisorZeroIndex) : ℝ :=
  (1 / 10000000000) * (1 / (riemannXiDivisorZeroValue p).im ^ 2) +
  (1 / 4000000) * xiHeightTail (Real.exp 4) p +
  (1 / 50000) * xiHeightTail (Real.exp 8) p +
  (1 / 5000) * xiHeightTail (Real.exp 12) p +
  (1 / 1000) * xiHeightTail (Real.exp 16) p +
  xiHeightTail (Real.exp 20) p

theorem xiZeroWeight_le_layer {x : ℝ} (hx : 3100 ≤ Real.log x)
    (p : RiemannXiDivisorZeroIndex) : xiZeroWeight x p ≤ xiLayerMajorant p := by
  have h4 := xiHeightTail_nonneg (Real.exp 4) p
  have h8 := xiHeightTail_nonneg (Real.exp 8) p
  have h12 := xiHeightTail_nonneg (Real.exp 12) p
  have h16 := xiHeightTail_nonneg (Real.exp 16) p
  have h20 := xiHeightTail_nonneg (Real.exp 20) p
  have hi : 0 ≤ 1 / (riemannXiDivisorZeroValue p).im ^ 2 := by positivity
  have hbound (u C : ℝ) (hu : 4 ≤ u) (hp : |(riemannXiDivisorZeroValue p).im| ≤ Real.exp u)
      (hC : Real.exp (-(3100 / (20 * (u + 21 / 10)))) ≤ C) :
      xiZeroWeight x p ≤ C * (1 / (riemannXiDivisorZeroValue p).im ^ 2) := by
    have h := mul_le_mul_of_nonneg_right ((zero_exp_height_le hx hu p hp).trans hC) hi
    simpa only [xiZeroWeight, div_eq_mul_inv, mul_one, one_mul] using h
  unfold xiLayerMajorant
  by_cases hp4 : |(riemannXiDivisorZeroValue p).im| ≤ Real.exp 4
  · have h := hbound 4 _ (by norm_num) hp4 zero_exp_budget_four
    linarith
  have he4 : xiHeightTail (Real.exp 4) p = 1 / (riemannXiDivisorZeroValue p).im ^ 2 :=
    if_pos (lt_of_not_ge hp4)
  by_cases hp8 : |(riemannXiDivisorZeroValue p).im| ≤ Real.exp 8
  · have h := hbound 8 _ (by norm_num) hp8 zero_exp_budget_eight
    rw [← he4] at h
    linarith
  have he8 : xiHeightTail (Real.exp 8) p = 1 / (riemannXiDivisorZeroValue p).im ^ 2 :=
    if_pos (lt_of_not_ge hp8)
  by_cases hp12 : |(riemannXiDivisorZeroValue p).im| ≤ Real.exp 12
  · have h := hbound 12 _ (by norm_num) hp12 zero_exp_budget_twelve
    rw [← he8] at h
    linarith
  have he12 : xiHeightTail (Real.exp 12) p = 1 / (riemannXiDivisorZeroValue p).im ^ 2 :=
    if_pos (lt_of_not_ge hp12)
  by_cases hp16 : |(riemannXiDivisorZeroValue p).im| ≤ Real.exp 16
  · have h := hbound 16 _ (by norm_num) hp16 zero_exp_budget_sixteen
    rw [← he12] at h
    linarith
  have he16 : xiHeightTail (Real.exp 16) p = 1 / (riemannXiDivisorZeroValue p).im ^ 2 :=
    if_pos (lt_of_not_ge hp16)
  by_cases hp20 : |(riemannXiDivisorZeroValue p).im| ≤ Real.exp 20
  · have h := hbound 20 _ (by norm_num) hp20 zero_exp_budget_twenty
    rw [← he16] at h
    linarith
  have he20 : xiHeightTail (Real.exp 20) p = 1 / (riemannXiDivisorZeroValue p).im ^ 2 :=
    if_pos (lt_of_not_ge hp20)
  have h := mul_le_mul_of_nonneg_right (zero_exp_le_one hx p) hi
  have hw : xiZeroWeight x p ≤ xiHeightTail (Real.exp 20) p := by
    rw [he20]
    simpa only [xiZeroWeight, div_eq_mul_inv, mul_one, one_mul] using h
  linarith

theorem xiLayerMajorant_summable : Summable xiLayerMajorant := by
  have hT (u : ℝ) (hu : 4 ≤ u) : Summable (xiHeightTail (Real.exp u)) := by
    have h := exp_four_ge_fifty_four.trans (Real.exp_le_exp.mpr hu)
    exact xiHeightTail_summable (by linarith)
  exact (((((xi_height_inverse_square_summable.mul_left (1 / 10000000000)).add
    ((hT 4 (by norm_num)).mul_left (1 / 4000000))).add
    ((hT 8 (by norm_num)).mul_left (1 / 50000))).add
    ((hT 12 (by norm_num)).mul_left (1 / 5000))).add
    ((hT 16 (by norm_num)).mul_left (1 / 1000))).add (hT 20 (by norm_num))

theorem xiLayerMajorant_sum_le : (∑' p, xiLayerMajorant p) ≤ 3 / 10000000 := by
  have hT (u : ℝ) (hu : 4 ≤ u) : Summable (xiHeightTail (Real.exp u)) := by
    have h := exp_four_ge_fifty_four.trans (Real.exp_le_exp.mpr hu)
    exact xiHeightTail_summable (by linarith)
  have hsum := (((((xi_height_inverse_square_summable.hasSum.mul_left (1 / 10000000000)).add
    ((hT 4 (by norm_num)).hasSum.mul_left (1 / 4000000))).add
    ((hT 8 (by norm_num)).hasSum.mul_left (1 / 50000))).add
    ((hT 12 (by norm_num)).hasSum.mul_left (1 / 5000))).add
    ((hT 16 (by norm_num)).hasSum.mul_left (1 / 1000))).add
    (hT 20 (by norm_num)).hasSum
  rw [show (∑' p, xiLayerMajorant p) = _ from hsum.tsum_eq]
  have h4 := xiHeightTail_exp_sum_le 1 (by norm_num)
  have h8 := xiHeightTail_exp_sum_le 2 (by norm_num)
  have h12 := xiHeightTail_exp_sum_le 3 (by norm_num)
  have h16 := xiHeightTail_exp_sum_le 4 (by norm_num)
  have h20 := xiHeightTail_exp_sum_le 5 (by norm_num)
  norm_num at h4 h8 h12 h16 h20
  linarith [xi_height_inverse_square_sum_le]

theorem xiZeroWeight_summable {x : ℝ} (hx : 3100 ≤ Real.log x) :
    Summable (xiZeroWeight x) :=
  Summable.of_nonneg_of_le (fun _ => by unfold xiZeroWeight; positivity)
    (xiZeroWeight_le_layer hx) xiLayerMajorant_summable

theorem xiZeroWeight_sum_le {x : ℝ} (hx : 3100 ≤ Real.log x) :
    (∑' p, xiZeroWeight x p) ≤ 3 / 10000000 :=
  ((xiZeroWeight_summable hx).tsum_le_tsum (xiZeroWeight_le_layer hx)
    xiLayerMajorant_summable).trans xiLayerMajorant_sum_le

end LiuWang.Proof.ChebyshevBound.HighHeight
