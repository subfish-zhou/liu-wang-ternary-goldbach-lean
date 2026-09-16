import LiuWang.Proof.Campaign20260915.RSMediumRange.ChunkChain

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

theorem log_from_left_endpoint {b x : ℝ} (hb : 0 < b) (hbx : b ≤ x) :
    Real.log b + 2 * (x - b) / (x + b) ≤ Real.log x ∧
      Real.log x ≤ Real.log b + (x - b) / b := by
  have hx : 0 < x := hb.trans_le hbx
  have ht : 0 ≤ (x - b) / b := div_nonneg (sub_nonneg.mpr hbx) hb.le
  have hl := Real.le_log_one_add_of_nonneg ht
  have he : 1 + (x - b) / b = x / b := by field_simp; ring
  rw [he, Real.log_div hx.ne' hb.ne'] at hl
  have hf : 2 * ((x - b) / b) / ((x - b) / b + 2) =
      2 * (x - b) / (x + b) := by
    rw [show (x - b) / b + 2 = (x + b) / b by field_simp; ring,
      ← mul_div_assoc, div_div_div_cancel_right₀ hb.ne']
  rw [hf] at hl
  have hu := Real.log_le_sub_one_of_pos (div_pos hx hb)
  rw [Real.log_div hx.ne' hb.ne'] at hu
  constructor
  · linarith
  · have h : x / b - 1 = (x - b) / b := by field_simp
    rw [h] at hu
    linarith

def gridLogLo (n e m tableLo : ℕ) : ℕ :=
  tableLo + e * 6931471803 * 10000 +
    (2 * (n - m * 2 ^ e) * fixedScale) / (n + m * 2 ^ e)

def gridLogHi (n e m tableHi : ℕ) : ℕ :=
  tableHi + e * 6931471808 * 10000 +
    divUp ((n - m * 2 ^ e) * fixedScale) (m * 2 ^ e)

noncomputable section

theorem gridLog_bounds {n e m tableLo tableHi : ℕ}
    (hm : 0 < m) (hb : m * 2 ^ e ≤ n)
    (ht : (FixedBracket.mk tableLo tableHi).Contains (Real.log m)) :
    (FixedBracket.mk (gridLogLo n e m tableLo) (gridLogHi n e m tableHi)).Contains
      (Real.log n) := by
  let b : ℕ := m * 2 ^ e
  have hb0 : 0 < b := Nat.mul_pos hm (by positivity)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
  have hxR : (b : ℝ) ≤ n := by exact_mod_cast hb
  have hreal := log_from_left_endpoint hbR hxR
  have hlo := FixedBracket.ratio_contains (2 * (n - b)) (n + b) (by omega)
  have hhi := FixedBracket.ratio_contains (n - b) b hb0
  have hcast : ((n - b : ℕ) : ℝ) = (n : ℝ) - b := Nat.cast_sub hb
  have hid : Real.log (b : ℝ) = Real.log m + e * Real.log 2 := by
    simp only [b, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  rw [hid] at hreal
  have hlow := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg e)
  have hhigh := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg e)
  dsimp only [FixedBracket.Contains] at ht hlo hhi ⊢
  simp only [FixedBracket.ratio, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, hcast] at hlo hhi
  dsimp only [gridLogLo, gridLogHi]
  push_cast
  have hlo' := hlo.1
  have hhi' := hhi.2
  simp only [b] at hlo' hhi'
  simp only [b, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hreal
  norm_num [fixedScale] at ht hlo' hhi' ⊢
  constructor <;> linarith [ht.1, ht.2, hreal.1, hreal.2]

#print axioms gridLog_bounds

end
end LiuWang.Proof.Campaign20260915.RSMediumRange
