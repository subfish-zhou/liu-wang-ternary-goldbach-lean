import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticPolyaVinogradov
import AnalyticNumberTheory.LargeSieve.GeomSum
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# 保留零频权重的尖锐区间字符和界

在同一个 Fourier 和内处理平移区间，不将两个前缀的范数相加。
对称频率配对给出 `sqrt r * harmonic (r / 2)`；六项调和和的已证
上界将它吸收到 `sqrt r * log r` 中。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ExceptionalZeroGap

open Complex Finset ZMod AnalyticNumberTheory.LargeSieve

variable {r : ℕ} [NeZero r]

theorem sum_range_add_fourier_completion {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (a : ZMod r) (N : ℕ) :
    (∑ n ∈ range N, χ (a + n)) =
      (r : ℂ)⁻¹ * gaussSum χ stdAddChar *
        ∑ j : ZMod r, χ⁻¹ (-j) * stdAddChar (j * a) *
          ∑ n ∈ range N, stdAddChar (j * (n : ZMod r)) := by
  have hinv (z : ZMod r) :
      χ z = (r : ℂ)⁻¹ * ∑ j : ZMod r,
        stdAddChar (j * z) * (χ⁻¹ (-j) * gaussSum χ stdAddChar) := by
    have hi := congrArg (fun f : ZMod r → ℂ => f z)
      (ZMod.dft.symm_apply_apply (χ : ZMod r → ℂ))
    rw [ZMod.invDFT_apply] at hi
    simp only [hχ.fourierTransform_eq_inv_mul_gaussSum, smul_eq_mul] at hi
    exact hi.symm
  simp_rw [hinv, mul_add, AddChar.map_add_eq_mul]
  rw [← mul_sum, sum_comm, mul_assoc]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro n _
  ring

theorem stdAddChar_natCast_eq_charReal (n : ℕ) :
    stdAddChar (n : ZMod r) = charReal ((n : ℝ) / r) := by
  rw [show stdAddChar (n : ZMod r) =
      Complex.exp (2 * Real.pi * I * ((n : ℤ) : ℂ) / (r : ℂ)) by
    simpa using (ZMod.stdAddChar_coe (N := r) (n : ℤ))]
  unfold charReal
  push_cast
  congr 1
  ring

theorem norm_geometric_kernel_le {j : ℕ} (hj : 1 ≤ j) (hjr : j < r) (N : ℕ) :
    ‖∑ n ∈ range N, stdAddChar ((j : ZMod r) * (n : ZMod r))‖ ≤
      (r : ℝ) / (2 * (min j (r - j) : ℕ)) := by
  have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hjr' : (j : ℝ) < r := by exact_mod_cast hjr
  have hx0 : 0 < (j : ℝ) / r := div_pos hj0 hr
  have hx1 : (j : ℝ) / r < 1 := (div_lt_one hr).2 hjr'
  have hfract : Int.fract ((j : ℝ) / r) = (j : ℝ) / r :=
    Int.fract_eq_self.2 ⟨hx0.le, hx1⟩
  have hnot : ¬ ∃ k : ℤ, (k : ℝ) = (j : ℝ) / r := by
    exact Int.fract_ne_zero_iff.mp (by rw [hfract]; exact hx0.ne')
  have hsum :
      (∑ n ∈ range N, stdAddChar ((j : ZMod r) * (n : ZMod r))) =
        ∑ n ∈ range N, charReal ((n : ℝ) * ((j : ℝ) / r)) := by
    apply sum_congr rfl
    intro n _
    rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow,
      stdAddChar_natCast_eq_charReal, charReal_nat_mul]
  rw [hsum]
  refine (geomSum_exp_bound_far N hnot).trans_eq ?_
  have hmin : distToInt ((j : ℝ) / r) = (min j (r - j) : ℕ) / (r : ℝ) := by
    rw [distToInt, hfract, Nat.cast_min, Nat.cast_sub hjr.le,
      ← min_div_div_right hr.le]
    congr 1
    field_simp
  rw [hmin]
  field_simp

omit [NeZero r] in
theorem sum_reciprocal_min_le_harmonic (hr : 2 ≤ r) :
    (∑ j ∈ Ico 1 r, ((min j (r - j) : ℕ) : ℝ)⁻¹) ≤
      2 * (harmonic (r / 2) : ℝ) := by
  have hhalf : 1 ≤ r / 2 := by omega
  rw [← sum_Ico_consecutive (f := fun j : ℕ =>
    ((min j (r - j) : ℕ) : ℝ)⁻¹) (by omega : 1 ≤ r / 2 + 1)
      (by omega : r / 2 + 1 ≤ r)]
  have hleft :
      (∑ j ∈ Ico 1 (r / 2 + 1), ((min j (r - j) : ℕ) : ℝ)⁻¹) =
        (harmonic (r / 2) : ℝ) := by
    calc
      _ = ∑ j ∈ Ico 1 (r / 2 + 1), (j : ℝ)⁻¹ := by
        apply sum_congr rfl
        intro j hj
        rw [Nat.min_eq_left (by have := mem_Ico.mp hj; omega)]
      _ = _ := by
        rw [Ico_add_one_right_eq_Icc, harmonic_eq_sum_Icc]
        push_cast
        rfl
  rw [hleft]
  have hright :
      (∑ j ∈ Ico (r / 2 + 1) r, ((min j (r - j) : ℕ) : ℝ)⁻¹) ≤
        (harmonic (r / 2) : ℝ) := by
    calc
      _ = ∑ j ∈ Ico (r / 2 + 1) r, ((r - j : ℕ) : ℝ)⁻¹ := by
        apply sum_congr rfl
        intro j hj
        rw [Nat.min_eq_right (by have := mem_Ico.mp hj; omega)]
      _ = ∑ j ∈ Ico 1 (r - r / 2), (j : ℝ)⁻¹ := by
        rw [sum_Ico_reflect (fun j : ℕ => (j : ℝ)⁻¹) (r / 2 + 1)
          (m := r) (n := r) (by omega)]
        simp
      _ ≤ ∑ j ∈ Ico 1 (r / 2 + 1), (j : ℝ)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · exact Ico_subset_Ico_right (by omega)
        · intro j _ _
          positivity
      _ = _ := by
        rw [Ico_add_one_right_eq_Icc, harmonic_eq_sum_Icc]
        push_cast
        rfl
  linarith

omit [NeZero r] in
theorem harmonic_half_le_log (hr : 12 ≤ r) :
    (harmonic (r / 2) : ℝ) ≤ Real.log r := by
  have hn : 6 ≤ r / 2 := by omega
  have hn0 : r / 2 ≠ 0 := by omega
  have hseq := (Real.strictAnti_eulerMascheroniSeq'.antitone hn).trans_lt
    Real.eulerMascheroniSeq'_six_lt_two_thirds
  simp only [Real.eulerMascheroniSeq', hn0, ↓reduceIte] at hseq
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 * (r / 2 : ℕ))
    (show (2 : ℝ) * (r / 2 : ℕ) ≤ r by exact_mod_cast Nat.mul_div_le r 2)
  rw [Real.log_mul (by norm_num) (by positivity)] at hlog
  linarith [Real.log_two_gt_d9]

private theorem sum_univ_eq_sum_range (f : ZMod r → ℝ) :
    (∑ j : ZMod r, f j) = ∑ n ∈ range r, f (n : ZMod r) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne r)
  calc
    _ = ∑ i : Fin q.succ, f ((i : ℕ) : ZMod q.succ) := by
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv q.succ).toEquiv
      intro i
      congr 1
      exact ZMod.natCast_zmod_val (ZMod.finEquiv q.succ i)
    _ = _ := Fin.sum_univ_eq_sum_range (fun n : ℕ => f (n : ZMod q.succ)) q.succ

theorem weighted_fourier_kernel_le {χ : DirichletCharacter ℂ r}
    (hr : 12 ≤ r) (a : ZMod r) (N : ℕ) :
    (∑ j : ZMod r, ‖χ⁻¹ (-j) * stdAddChar (j * a) *
      ∑ n ∈ range N, stdAddChar (j * (n : ZMod r))‖) ≤
        (r : ℝ) * Real.log r := by
  let F : ZMod r → ℝ := fun j => ‖χ⁻¹ (-j) * stdAddChar (j * a) *
    ∑ n ∈ range N, stdAddChar (j * (n : ZMod r))‖
  have hzero : F 0 = 0 := by
    let : Fact (1 < r) := ⟨by omega⟩
    have hz : χ⁻¹ (0 : ZMod r) = 0 :=
      MulChar.map_nonunit χ⁻¹ not_isUnit_zero
    simp [F, hz]
  have hbound (j : ℕ) (hj : j ∈ Ico 1 r) :
      F (j : ZMod r) ≤ (r : ℝ) / 2 * ((min j (r - j) : ℕ) : ℝ)⁻¹ := by
    have hnorm : ‖stdAddChar ((j : ZMod r) * a)‖ = 1 :=
      Circle.norm_coe (ZMod.toCircle _)
    calc
      _ ≤ ‖∑ n ∈ range N, stdAddChar ((j : ZMod r) * (n : ZMod r))‖ := by
        dsimp [F]
        rw [norm_mul, norm_mul, hnorm, mul_one]
        exact mul_le_of_le_one_left (norm_nonneg _) (χ⁻¹.norm_le_one _)
      _ ≤ (r : ℝ) / (2 * (min j (r - j) : ℕ)) :=
        norm_geometric_kernel_le (mem_Ico.mp hj).1 (mem_Ico.mp hj).2 N
      _ = _ := by simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  change (∑ j : ZMod r, F j) ≤ _
  rw [sum_univ_eq_sum_range, ← sum_range_add_sum_Ico _ (by omega : 1 ≤ r)]
  simp only [sum_range_one, Nat.cast_zero, hzero, zero_add]
  calc
    _ ≤ ∑ j ∈ Ico 1 r, (r : ℝ) / 2 * ((min j (r - j) : ℕ) : ℝ)⁻¹ :=
      sum_le_sum hbound
    _ = (r : ℝ) / 2 * ∑ j ∈ Ico 1 r, ((min j (r - j) : ℕ) : ℝ)⁻¹ :=
      (mul_sum _ _ _).symm
    _ ≤ (r : ℝ) / 2 * (2 * (harmonic (r / 2) : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_min_le_harmonic (by omega)) (by positivity)
    _ ≤ (r : ℝ) * Real.log r := by
      have := mul_le_mul_of_nonneg_left (harmonic_half_le_log hr) (Nat.cast_nonneg r)
      nlinarith

/-- 任意平移区间；不需要实性，也没有两个前缀引起的额外因子。 -/
theorem norm_sum_range_add_le_sqrt_mul_log {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hr : 987 ≤ r) (a : ZMod r) (N : ℕ) :
    ‖∑ n ∈ range N, χ (a + n)‖ ≤ Real.sqrt r * Real.log r := by
  rw [sum_range_add_fourier_completion hχ a N, norm_mul, norm_mul,
    norm_inv, Complex.norm_natCast, hχ.norm_gaussSum_stdAddChar (by omega)]
  calc
    _ ≤ (r : ℝ)⁻¹ * Real.sqrt r *
        ∑ j : ZMod r, ‖χ⁻¹ (-j) * stdAddChar (j * a) *
          ∑ n ∈ range N, stdAddChar (j * (n : ZMod r))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (r : ℝ)⁻¹ * Real.sqrt r * ((r : ℝ) * Real.log r) :=
      mul_le_mul_of_nonneg_left (weighted_fourier_kernel_le (by omega) a N) (by positivity)
    _ = _ := by
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne r
      field_simp

theorem norm_sum_Ico_le_sqrt_mul_log {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hr : 987 ≤ r) (m n : ℕ) :
    ‖∑ k ∈ Ico m n, χ k‖ ≤ Real.sqrt r * Real.log r := by
  rw [sum_Ico_eq_sum_range]
  simpa only [Nat.cast_add] using
    norm_sum_range_add_le_sqrt_mul_log hχ hr (m : ZMod r) (n - m)

theorem norm_sum_int_Ico_le_sqrt_mul_log {χ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hr : 987 ≤ r) (m n : ℤ) :
    ‖∑ k ∈ Ico m n, χ k‖ ≤ Real.sqrt r * Real.log r := by
  have hsum : (∑ k ∈ range (n - m).toNat, χ ((m : ZMod r) + k)) =
      ∑ k ∈ Ico m n, χ k := by
    apply sum_bij (i := fun (k : ℕ) _ => m + (k : ℤ))
    · intro k hk
      have := mem_range.mp hk
      simp only [mem_Ico]
      omega
    · intro k _ l _ h
      omega
    · intro k hk
      have := mem_Ico.mp hk
      refine ⟨(k - m).toNat, mem_range.mpr (by omega), ?_⟩
      omega
    · intro k _
      simp
  rw [← hsum]
  exact norm_sum_range_add_le_sqrt_mul_log hχ hr (m : ZMod r) (n - m).toNat

end LiuWang.Proof.ExceptionalZeroGap
