import LiuWang.Proof.Campaign20260915.RSMediumRange.Chunk0000

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

theorem medium_start_log :
    (968034399783744 : ℝ) / fixedScale ≤ Real.log 16000 := by
  have h := FixedBracket.log_contains (n := 16000) (k := 13)
    (by norm_num) (by norm_num)
  have he : (FixedBracket.log 16000 13).lo = 968034399783744 := by decide +kernel
  simpa only [he] using h.1

theorem medium_start_actual
    (hl : (158867924626313 : ℝ) / 10000000000 ≤ Chebyshev.theta 16000)
    (hu : Chebyshev.theta 16000 ≤ (158867924837558 : ℝ) / 10000000000)
    (hp : (Totient.prefixEuler 16000 : ℝ) ≤ (172591171463 : ℝ) / 10000000000) :
    Chunk0000Start.Actual := by
  refine ⟨?_, ?_, ?_, medium_start_log⟩
  · norm_num [Chunk0000Start, fixedScale] at hl ⊢
    exact hl
  · norm_num [Chunk0000Start, fixedScale] at hu ⊢
    exact hu
  · norm_num [Chunk0000Start, fixedScale] at hp ⊢
    exact hp

theorem theta_3_14_from_medium {x : ℝ} (hx : 16000 ≤ x)
    (ht : x - 2 * Real.sqrt x < Chebyshev.theta x) :
    x * (1 - 1 / (2 * Real.log x)) < Chebyshev.theta x := by
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hroot := Real.sq_sqrt (show 0 ≤ x by linarith)
  have hm := mul_le_mul_of_nonneg_right (four_log_le_sqrt hx) (Real.sqrt_nonneg x)
  have hbound : 2 * Real.sqrt x ≤ x / (2 * Real.log x) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log x)).mpr
    nlinarith
  have hid : x * (1 - 1 / (2 * Real.log x)) = x - x / (2 * Real.log x) := by ring
  rw [hid]
  linarith

theorem product_envelope_source_form {x : ℝ} (hx : 16000 ≤ x) :
    Totient.productEnvelope x =
      Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * Real.log x ^ 2)) := by
  have hl : Real.log x ≠ 0 := (Real.log_pos (by linarith : 1 < x)).ne'
  unfold Totient.productEnvelope
  field_simp [hl]
  ring

#print axioms medium_start_log
#print axioms theta_3_14_from_medium
#print axioms product_envelope_source_form

end LiuWang.Proof.Campaign20260915.RSMediumRange
