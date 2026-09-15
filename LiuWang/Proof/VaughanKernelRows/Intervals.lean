import LiuWang.Proof.VaughanKernelRows.Phase

/-!
# 连续有限区间上的实际核行

只补齐一次末块。偶性把整行改写为同一任意相位，不拆分实数差的正负部分。
自然数减法仅用于区间长度；核的参数始终是实数差。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanKernelRows

open Finset AnalyticNumberTheory.LargeSieve VaughanTypeI

@[simp] theorem truncatedKernel_neg (T x : ℝ) :
    truncatedKernel T (-x) = truncatedKernel T x := by
  simp only [truncatedKernel, distToInt_neg]

theorem rational_phase_blocks_le {a q : ℕ} {α β θ T : ℝ}
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) (hT : 0 ≤ T) (J : ℕ) :
    (∑ k ∈ range (J * q), truncatedKernel T (α * k + β)) ≤
      (J : ℝ) * (3 * T + (q : ℝ) * (1 + Real.log q)) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Nat.succ_mul, sum_range_add]
      have htail :
          (∑ k ∈ range q, truncatedKernel T (α * (J * q + k : ℕ) + β)) =
            ∑ k ∈ range q, truncatedKernel T (α * k + (α * (J * q : ℕ) + β)) := by
        apply sum_congr rfl
        intro k _
        congr 1
        push_cast
        ring
      rw [htail]
      have hb := rational_phase_kernel_le (β := α * (J * q : ℕ) + β) hq hcop hθ hα hT
      calc
        _ ≤ (J : ℝ) * (3 * T + (q : ℝ) * (1 + Real.log q)) +
            (3 * T + (q : ℝ) * (1 + Real.log q)) := add_le_add ih hb
        _ = _ := by push_cast; ring

theorem rational_phase_range_le {a q : ℕ} {α β θ T : ℝ}
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) (hT : 0 ≤ T) (n : ℕ) :
    (∑ k ∈ range n, truncatedKernel T (α * k + β)) ≤
      ((n : ℝ) / q + 1) * (3 * T + (q : ℝ) * (1 + Real.log q)) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hcover : n ≤ (n / q + 1) * q :=
    ((Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self (n / q))).le
  have hJ : ((n / q + 1 : ℕ) : ℝ) ≤ (n : ℝ) / q + 1 := by
    have hd : ((n / q : ℕ) : ℝ) * q ≤ n := by exact_mod_cast Nat.div_mul_le_self n q
    have := (le_div_iff₀ hqp).mpr hd
    push_cast
    linarith
  have hB : 0 ≤ 3 * T + (q : ℝ) * (1 + Real.log q) := by
    positivity [Real.log_natCast_nonneg q]
  calc
    _ ≤ ∑ k ∈ range ((n / q + 1) * q), truncatedKernel T (α * k + β) :=
      sum_le_sum_of_subset_of_nonneg (range_mono hcover)
        (fun k _ _ => truncatedKernel_nonneg hT _)
    _ ≤ ((n / q + 1 : ℕ) : ℝ) * (3 * T + (q : ℝ) * (1 + Real.log q)) :=
      rational_phase_blocks_le hq hcop hθ hα hT _
    _ ≤ _ := mul_le_mul_of_nonneg_right hJ hB

theorem rational_row_nat_le {a q : ℕ} {α θ T : ℝ}
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2) (hT : 0 ≤ T)
    (A B m : ℕ) :
    (∑ m' ∈ Ioc A B, truncatedKernel T (α * ((m : ℝ) - (m' : ℝ)))) ≤
      (((B - A : ℕ) : ℝ) / q + 1) *
        (3 * T + (q : ℝ) * (1 + Real.log q)) := by
  have hi : Ioc A B = Ico (A + 1) (B + 1) := by
    ext k
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hi, sum_Ico_eq_sum_range]
  have hlen : B + 1 - (A + 1) = B - A := by omega
  rw [hlen]
  have he :
      (∑ k ∈ range (B - A),
        truncatedKernel T (α * ((m : ℝ) - (A + 1 + k : ℕ)))) =
      ∑ k ∈ range (B - A),
        truncatedKernel T (α * k + α * ((A + 1 : ℕ) - (m : ℝ))) := by
    apply sum_congr rfl
    intro k _
    rw [← truncatedKernel_neg T (α * ((m : ℝ) - (A + 1 + k : ℕ)))]
    congr 1
    push_cast
    ring
  rw [he]
  exact rational_phase_range_le hq hcop hθ hα hT _

theorem rational_row_le {a q : ℕ} {α θ T U X : ℝ}
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hθ : |θ| ≤ 1)
    (hα : α = (a : ℝ) / q + θ / (q : ℝ) ^ 2)
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hUX : U ≤ X) (m : ℕ) :
    (∑ m' ∈ Ioc ⌊U⌋₊ ⌊X⌋₊,
      truncatedKernel T (α * ((m : ℝ) - (m' : ℝ)))) ≤
      ((X - U + 1) / q + 1) * (3 * T + (q : ℝ) * (1 + Real.log q)) := by
  have hlen : ((⌊X⌋₊ - ⌊U⌋₊ : ℕ) : ℝ) ≤ X - U + 1 := by
    rw [Nat.cast_sub (Nat.floor_mono hUX)]
    have hx := Nat.floor_le (hU.trans hUX)
    have hu := Nat.lt_floor_add_one U
    linarith
  apply (rational_row_nat_le hq hcop hθ hα hT ⌊U⌋₊ ⌊X⌋₊ m).trans
  apply mul_le_mul_of_nonneg_right
    (add_le_add (div_le_div_of_nonneg_right hlen (Nat.cast_nonneg q)) le_rfl)
  positivity [Real.log_natCast_nonneg q]

end LiuWang.Proof.VaughanKernelRows
