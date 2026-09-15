import LiuWang.Proof.VaughanTypeI.Scalar

/-!
# 原大 N 应用域内的实际 Lemma 6.5 与 Lemma 6.6

独立变截断核界已证，不把它作为输入；所有截点、相位及分母均保持同一见证。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeI

open Interfaces Parameters Finset

theorem weighted_kernel_le {N a q : ℕ} {α θ X W : ℝ}
    (hq : 2 ≤ q) (hcop : Nat.Coprime a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hX : 1 ≤ X) (hW : 0 ≤ W) :
    W * (∑ n ∈ Icc 1 ⌊X⌋₊, truncatedKernel ((N : ℝ) / n) ((n : ℝ) * α)) ≤
      (X * (1 + Real.log q) + (q : ℝ) * (5 + 2 * Real.log q) +
        6 * (N : ℝ) / q * (1 + Real.log X)) * W := by
  have hfloor : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hX)
  have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hlog : Real.log (⌊X⌋₊ : ℝ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast hfloor) hfl
  have hk := variable_kernel_le (Y := (N : ℝ)) hq hfloor (Nat.cast_nonneg N) hcop hθ hα
  simp only [mul_comm α] at hk
  have hbound :
      (∑ n ∈ Icc 1 ⌊X⌋₊, truncatedKernel ((N : ℝ) / n) ((n : ℝ) * α)) ≤
        X * (1 + Real.log q) + (q : ℝ) * (5 + 2 * Real.log q) +
          6 * (N : ℝ) / q * (1 + Real.log X) := by
    apply hk.trans
    apply add_le_add
    · apply add_le_add_left
      exact mul_le_mul_of_nonneg_right hfl (by linarith [Real.log_natCast_nonneg q])
    · exact mul_le_mul_of_nonneg_left (add_le_add_right hlog _) (by positivity)
  simpa only [mul_comm W] using mul_le_mul_of_nonneg_right hbound hW

theorem sourceS2_bound {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ‖sourceS2 N α‖ ≤
      0.0282 * (N : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * sourceL N ^ 2 +
      0.0001 * (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) +
      0.0006 * (N : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
        sourceL N ^ (5 / 2 : ℝ) := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hL := (sourceL_pos h2000).le
  have hV := (sourceVaughanV_pos h2000).le
  have hq2 : 2 ≤ q := by
    have hq := source_q_million hN hqL
    exact_mod_cast (show (2 : ℝ) ≤ q by linarith)
  have hV1 : 1 ≤ sourceVaughanV N :=
    (one_lt_sourceVaughanU h2000).le.trans (sourceVaughanU_le_V h2000)
  have hk := (norm_sourceS2_le_kernel h2000 α).trans
    (weighted_kernel_le (N := N) hq2 hi.2.2 hθ hα hV1 hL)
  have hXterm :
      (sourceVaughanV N * (1 + Real.log q)) * sourceL N ≤
        0.0001 * (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) := by
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (one_add_log_q_le_L hN hqL hqU) hV) hL).trans
    simpa only [mul_assoc, ← pow_two] using sourceVaughanV_mul_L_sq_le hN
  have hqterm := kernel_q_term_le hN hqL hqU hL (le_refl (sourceL N))
  have hNterm := kernel_N_term_le hN hqL (sourceVaughan_log_bounds hN).1 hL
    (le_refl (sourceL N))
  have hA : 0 ≤ (N : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * sourceL N ^ (2 : ℕ) := by positivity
  have hC : 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
      sourceL N ^ (5 / 2 : ℝ) := by positivity
  nlinarith

theorem sourceS3_bound {N a q : ℕ} {α θ : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hi : sourceIndex a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) :
    ‖sourceS3 N α‖ ≤
      0.0131 * (N : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * sourceL N ^ 2 +
      0.8 * (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) +
      0.0005 * (N : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
        sourceL N ^ (5 / 2 : ℝ) := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hL := (sourceL_pos h2000).le
  have hUV := mul_pos (sourceVaughanU_pos h2000) (sourceVaughanV_pos h2000)
  have hUV1 : 1 ≤ sourceVaughanU N * sourceVaughanV N := by
    have hu := (one_lt_sourceVaughanU h2000).le
    have hv := hu.trans (sourceVaughanU_le_V h2000)
    nlinarith
  have hW := Real.log_nonneg hUV1
  have hlogbounds := (sourceVaughan_log_bounds hN).2
  have hWL : Real.log (sourceVaughanU N * sourceVaughanV N) ≤ sourceL N := by linarith [hlogbounds.1]
  have hq2 : 2 ≤ q := by
    have hq := source_q_million hN hqL
    exact_mod_cast (show (2 : ℝ) ≤ q by linarith)
  have hk := (norm_sourceS3_le_kernel h2000 α).trans
    (weighted_kernel_le (N := N) hq2 hi.2.2 hθ hα hUV1 hW)
  have hXterm :
      ((sourceVaughanU N * sourceVaughanV N) * (1 + Real.log q)) *
        Real.log (sourceVaughanU N * sourceVaughanV N) ≤
          0.8 * (N : ℝ) ^ (4 / 5 : ℝ) * sourceL N ^ (7 / 5 : ℝ) := by
    calc
      _ ≤ ((sourceVaughanU N * sourceVaughanV N) * sourceL N) *
          ((4 / 5 : ℝ) * sourceL N) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (one_add_log_q_le_L hN hqL hqU) hUV.le)
          hlogbounds.2 hW (mul_nonneg hUV.le hL)
      _ = (4 / 5 : ℝ) * (sourceVaughanU N * sourceVaughanV N * sourceL N ^ (2 : ℕ)) := by ring
      _ = _ := by rw [sourceVaughanUV_mul_L_sq hN]; ring
  have hqterm := kernel_q_term_le hN hqL hqU hW hWL
  have hNterm := kernel_N_term_le hN hqL hlogbounds.1 hW hWL
  nlinarith

end LiuWang.Proof.VaughanTypeI
