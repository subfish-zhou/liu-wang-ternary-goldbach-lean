import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.HeightPayments

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

def sourceCutoff (q : ℕ) (d y : ℝ) : ℝ :=
  1 - d / Real.log ((q : ℝ) * y)

theorem sourceCutoff_order {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {y d e : ℝ} (hy : lowHeight ≤ y) (hd : 0 ≤ d) (hde : d ≤ e)
    (he : e ≤ 0.478) :
    59 / 60 ≤ sourceCutoff q e y ∧
      sourceCutoff q e y ≤ sourceCutoff q d y ∧ sourceCutoff q d y ≤ 1 := by
  have hl : 0 < Real.log ((q : ℝ) * y) := by
    linarith [M3_log_product_ge_thirty hN hq hy]
  have hsplit := M3_rowCutoff_ge_source_split .r0478 hN hq hy
  change 59 / 60 ≤ 1 - 0.478 / Real.log ((q : ℝ) * y) at hsplit
  dsimp only [sourceCutoff]
  refine ⟨hsplit.trans ?_, ?_, ?_⟩
  · exact sub_le_sub_left (div_le_div_of_nonneg_right he hl.le) 1
  · exact sub_le_sub_left (div_le_div_of_nonneg_right hde hl.le) 1
  · exact sub_le_self _ (div_nonneg hd hl.le)

theorem moving_countIntegral_monotone {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X u v d : ℝ} (hX : 1 ≤ X) (hu : lowHeight ≤ u) (huv : u ≤ v)
    (hd : 0 ≤ d) (hd1 : d ≤ 0.478) :
    MonotoneOn (fun y => countIntegral q X y (59 / 60) (sourceCutoff q d y))
      (Set.uIcc u v) := by
  rw [Set.uIcc_of_le huv]
  intro y hy z _hz hyz
  have hlow := hu.trans hy.1
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hlogy : 0 < Real.log ((q : ℝ) * y) := by
    linarith [M3_log_product_ge_thirty hN hq hlow]
  have hlog := Real.log_le_log (mul_pos hqpos (lowHeight_pos.trans_le hlow))
    (mul_le_mul_of_nonneg_left hyz hqpos.le)
  have hcut : sourceCutoff q d y ≤ sourceCutoff q d z :=
    sub_le_sub_left (div_le_div_of_nonneg_left hd hlogy hlog) 1
  have hstart := (sourceCutoff_order hN hq hlow hd le_rfl hd1).1
  exact (countIntegral_mono_height q hX (by norm_num) hstart hyz).trans
    (countIntegral_mono_upper q hX (by norm_num) hstart hcut)

theorem moving_strip_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X u v d e p : ℝ} (hX : 1 ≤ X) (hu : lowHeight ≤ u) (huv : u ≤ v)
    (hd : 0 ≤ d) (hde : d ≤ e) (he : e ≤ 0.478) :
    IntervalIntegrable (fun y => heightKernel p y *
      countIntegral q X y (sourceCutoff q e y) (sourceCutoff q d y)) volume u v := by
  have hpos := lowHeight_pos.trans_le hu
  have hleft := heightKernel_mul_integrable hpos huv p
    (moving_countIntegral_monotone hN hq hX hu huv hd (hde.trans he)).intervalIntegrable
  have hright := heightKernel_mul_integrable hpos huv p
    (moving_countIntegral_monotone hN hq hX hu huv (hd.trans hde) he).intervalIntegrable
  apply (hleft.sub hright).congr_ae
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro y hy
  rw [Set.uIoc_of_le huv] at hy
  have ho := sourceCutoff_order hN hq (hu.trans hy.1.le) hd hde he
  have hs := countIntegral_split q y (lt_of_lt_of_le zero_lt_one hX)
    (by norm_num : (1 / 2 : ℝ) ≤ 59 / 60) ho.1 ho.2.1
  dsimp only
  rw [hs]
  ring

theorem moving_countIntegral_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X u v d p : ℝ} (hX : 1 ≤ X) (hu : lowHeight ≤ u) (huv : u ≤ v)
    (hd : 0 ≤ d) (hd1 : d ≤ 0.478) :
    (∫ y in u..v, heightKernel p y * countIntegral q X y (59 / 60) 1) =
      (∫ y in u..v, heightKernel p y *
        countIntegral q X y (59 / 60) (sourceCutoff q 0.478 y)) +
      (∫ y in u..v, heightKernel p y *
        countIntegral q X y (sourceCutoff q 0.478 y) (sourceCutoff q d y)) +
      ∫ y in u..v, heightKernel p y *
        countIntegral q X y (sourceCutoff q d y) 1 := by
  have hbulk := heightKernel_mul_integrable (lowHeight_pos.trans_le hu) huv p
    (moving_countIntegral_monotone hN hq hX hu huv
      (by norm_num : (0 : ℝ) ≤ 0.478) le_rfl).intervalIntegrable
  have hstrip := moving_strip_integrable hN hq hX hu huv hd hd1 le_rfl (p := p)
  have htail := moving_strip_integrable hN hq hX hu huv
    (by norm_num : (0 : ℝ) ≤ 0) hd hd1 (p := p)
  simp only [sourceCutoff, zero_div, sub_zero] at htail
  change IntervalIntegrable (fun y => heightKernel p y *
    countIntegral q X y (sourceCutoff q d y) 1) volume u v at htail
  rw [← intervalIntegral.integral_add hbulk hstrip,
    ← intervalIntegral.integral_add (hbulk.add hstrip) htail]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le huv] at hy
  have ho := sourceCutoff_order hN hq (hu.trans hy.1) hd hd1 le_rfl
  dsimp only
  rw [countIntegral_split q y (lt_of_lt_of_le zero_lt_one hX)
      (by norm_num : (1 / 2 : ℝ) ≤ 59 / 60) (ho.1.trans ho.2.1) ho.2.2,
    countIntegral_split q y (lt_of_lt_of_le zero_lt_one hX)
      (by norm_num : (1 / 2 : ℝ) ≤ 59 / 60) ho.1 ho.2.1]
  ring

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
