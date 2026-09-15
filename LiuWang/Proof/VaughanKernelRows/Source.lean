import LiuWang.Proof.VaughanKernelRows.Intervals
import LiuWang.Proof.VaughanTypeI.Scalar

/-!
# 原大 N 域的实际核行与取整余项支付

复用源参数的 `N < U²V`、`U ≤ V`，在 `V ≤ M` 下推出 `N ≤ U*M²`。
这与 `U ≥ 4` 支付末块及截断 `M + 1/2` 的余项；不涉及 S4 能量估计。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanKernelRows

open Finset VaughanTypeI Interfaces Parameters

theorem four_le_sourceVaughanU {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    4 ≤ sourceVaughanU N := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  apply (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 4)
    (sourceVaughanU_pos h2000)).mp
  rw [log_sourceVaughanU h2000]
  have hlog := nat_mul_log_lt (k := 4) (sourceL_ge_2000 h2000) (by norm_num)
  have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  norm_num at hlog h4
  linarith [sourceL_ge_3100 hN]

theorem source_natCast_le_U_mul_M_sq {N : ℕ} {M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hVM : sourceVaughanV N ≤ M) :
    (N : ℝ) ≤ sourceVaughanU N * M ^ 2 := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hU := (sourceVaughanU_pos h2000).le
  have hV := (sourceVaughanV_pos h2000).le
  have hM := hV.trans hVM
  have hUM := (sourceVaughanU_le_V h2000).trans hVM
  calc
    _ ≤ sourceVaughanU N ^ 2 * sourceVaughanV N :=
      (natCast_lt_sourceVaughanU_sq_mul_V h2000).le
    _ = sourceVaughanU N * (sourceVaughanU N * sourceVaughanV N) := by ring
    _ ≤ sourceVaughanU N * (M * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hUM hVM hV hM) hU
    _ = _ := by ring

theorem source_U_le_quotient {N : ℕ} {M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hVM : sourceVaughanV N ≤ M)
    (hMU : M ≤ (N : ℝ) / sourceVaughanU N) :
    sourceVaughanU N ≤ (N : ℝ) / M := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hM := (sourceVaughanV_pos h2000).trans_le hVM
  apply (le_div_iff₀ hM).mpr
  have h := (le_div_iff₀ (sourceVaughanU_pos h2000)).mp hMU
  linarith

theorem row_bound_scalar_le {N M U q H : ℝ}
    (hM : 0 < M) (hq : 0 < q) (hU : 4 ≤ U) (hH : 1 ≤ H)
    (hNM : N ≤ U * M ^ 2) :
    (((N / M - U + 1) / q + 1) * (3 * (M + 1 / 2) + q * H)) ≤
      3 * N / q + 3 * M + (N / M) * H + q * H := by
  have hX : N / M ≤ U * M := by
    apply (div_le_iff₀ hM).mpr
    nlinarith
  have hMX : M * (N / M) = N := mul_div_cancel₀ N hM.ne'
  have hfirst : 3 * (M + 1 / 2) * (N / M - U + 1) ≤ 3 * N := by
    nlinarith [mul_nonneg hM.le (show 0 ≤ U - 2 by linarith)]
  have hrest : 3 * (M + 1 / 2) + (N / M - U + 1) * H ≤
      3 * M + (N / M) * H := by
    nlinarith [mul_nonneg (show 0 ≤ U - 1 by linarith)
      (show 0 ≤ H - 1 by linarith)]
  calc
    _ = (3 * (M + 1 / 2) * (N / M - U + 1)) / q +
        (3 * (M + 1 / 2) + (N / M - U + 1) * H) + q * H := by
      field_simp
      ring
    _ ≤ 3 * N / q + (3 * M + (N / M) * H) + q * H :=
      add_le_add (add_le_add (div_le_div_of_nonneg_right hfirst hq.le) hrest) le_rfl
    _ = _ := by ring

theorem source_row_bound {N a q : ℕ} {α θ M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hcop : Nat.Coprime a q)
    (hθ : |θ| ≤ 1) (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hVM : sourceVaughanV N ≤ M) (hMU : M ≤ (N : ℝ) / sourceVaughanU N)
    (m : ℕ) :
    (∑ m' ∈ Ioc ⌊sourceVaughanU N⌋₊ ⌊(N : ℝ) / M⌋₊,
      truncatedKernel (M + 1 / 2) (α * ((m : ℝ) - (m' : ℝ)))) ≤
      (((N : ℝ) / M - sourceVaughanU N + 1) / q + 1) *
        (3 * (M + 1 / 2) + (q : ℝ) * (1 + Real.log q)) := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hq : 0 < q := by
    have := source_q_million hN hqL
    exact_mod_cast (by linarith : (0 : ℝ) < q)
  have hM := (sourceVaughanV_pos h2000).trans_le hVM
  exact rational_row_le hq hcop hθ hα (by positivity)
    (sourceVaughanU_pos h2000).le (source_U_le_quotient hN hVM hMU) m

theorem source_row_le {N a q : ℕ} {α θ M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hcop : Nat.Coprime a q)
    (hθ : |θ| ≤ 1) (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hVM : sourceVaughanV N ≤ M) (hMU : M ≤ (N : ℝ) / sourceVaughanU N)
    (m : ℕ) :
    (∑ m' ∈ Ioc ⌊sourceVaughanU N⌋₊ ⌊(N : ℝ) / M⌋₊,
      truncatedKernel (M + 1 / 2) (α * ((m : ℝ) - (m' : ℝ)))) ≤
      3 * (N : ℝ) / q + 3 * M + ((N : ℝ) / M) * (1 + Real.log q) +
        (q : ℝ) * (1 + Real.log q) := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  apply (source_row_bound hN hqL hcop hθ hα hVM hMU m).trans
  exact row_bound_scalar_le ((sourceVaughanV_pos h2000).trans_le hVM)
    (by linarith [source_q_million hN hqL]) (four_le_sourceVaughanU hN)
    (by linarith [Real.log_natCast_nonneg q]) (source_natCast_le_U_mul_M_sq hN hVM)

theorem source_row_le_logN {N a q : ℕ} {α θ M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hqL : sourceP1 N ≤ (q : ℝ)) (hqU : (q : ℝ) ≤ sourceQ N)
    (hcop : Nat.Coprime a q)
    (hθ : |θ| ≤ 1) (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hVM : sourceVaughanV N ≤ M) (hMU : M ≤ (N : ℝ) / sourceVaughanU N)
    (m : ℕ) :
    (∑ m' ∈ Ioc ⌊sourceVaughanU N⌋₊ ⌊(N : ℝ) / M⌋₊,
      truncatedKernel (M + 1 / 2) (α * ((m : ℝ) - (m' : ℝ)))) ≤
      3 * (N : ℝ) / q + 3 * M + ((N : ℝ) / M) * sourceL N +
        (q : ℝ) * sourceL N := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  have hM := (sourceVaughanV_pos h2000).trans_le hVM
  have hlog := one_add_log_q_le_L hN hqL hqU
  apply (source_row_le hN hqL hcop hθ hα hVM hMU m).trans
  exact add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hlog (by positivity)))
    (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg q))

end LiuWang.Proof.VaughanKernelRows
