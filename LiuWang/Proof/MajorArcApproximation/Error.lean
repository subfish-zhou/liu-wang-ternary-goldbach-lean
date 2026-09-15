import LiuWang.Proof.MajorArcApproximation.Geometry

/-! # 原核心弧上的强展开误差：保留母函数并支付统一小界 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion

namespace LiuWang.Proof.MajorArcApproximation

def epsilon (N a q : ℕ) (eta : ℝ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    errorBound q N a eta

theorem epsilon_eq {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    epsilon N a q eta = errorBound q N a eta := by
  simp only [epsilon, dif_neg (NeZero.ne q)]

theorem continuous_epsilon (N a q : ℕ) : Continuous (epsilon N a q) := by
  by_cases hq : q = 0
  · subst q
    change Continuous (fun _ : ℝ => (0 : ℝ))
    exact continuous_const
  · let : NeZero q := ⟨hq⟩
    simp only [funext (epsilon_eq N a)]
    unfold errorBound PrincipalExpansion.errorFunction PrincipalExpansion.abelError
      PerronRecovery.oscillatoryError
    fun_prop

theorem epsilon_nonneg {N a q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hi : sourceIndex a q) (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    0 ≤ epsilon N a q eta := by
  let : NeZero q := ⟨Nat.ne_of_gt (ArcGeometry.sourceIndex_den_pos hi)⟩
  rw [epsilon_eq]
  exact (norm_nonneg _).trans (norm_S_sub_model hN hi hq eta)

theorem principalMass_le_one {q : ℕ} (hq : 0 < q) : principalMass q ≤ 1 := by
  have hp : 1 ≤ q.totient := Nat.totient_pos.mpr hq
  have hm : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  unfold principalMass
  apply (div_le_one (Nat.cast_pos.mpr hp)).mpr
  exact hm.trans (by exact_mod_cast hp)

theorem nonprincipalMass_le_q {q : ℕ} [NeZero q] (a : ℕ) :
    nonprincipalMass q a ≤ (q : ℝ) := by
  apply (nonprincipalMass_le_modulus q a).trans
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity, by nlinarith⟩

theorem epsilon_le_core {N a q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hi : sourceIndex a q) (hq : (q : ℝ) ≤ sourceP N) {eta : ℝ}
    (heta : |eta| ≤ deltaRadius N q) :
    epsilon N a q eta ≤ 20 * (N : ℝ) / sourceL N^10 := by
  have hq0 := ArcGeometry.sourceIndex_den_pos hi
  let : NeZero q := ⟨Nat.ne_of_gt hq0⟩
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hn := natCast_pos_of_exp_le hN
  have hL := sourceL_pos hN
  have hP := sourceP_pos hN
  have hP1 := one_le_sourceP hN
  have hT := sourceT_pos hN
  have hx0 : 0 ≤ (N : ℝ) * |eta| := by positivity
  have hqx : (q : ℝ) * ((N : ℝ) * |eta|) ≤ sourceP N := by
    have hh := (le_div_iff₀ (mul_pos hqr hn)).mp (heta.trans (delta_le hN hq0))
    nlinarith
  have hx : (N : ℝ) * |eta| ≤ sourceP N := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hx0]
  have hcoef :
      principalMass q * (0.963362 + 3.02347 * (N : ℝ) * |eta|) +
        nonprincipalMass q a * (0.96258 + 3.02102 * (N : ℝ) * |eta|) ≤ 10 * sourceP N := by
    calc
      _ ≤ 1 * (1 + 4 * ((N : ℝ) * |eta|)) +
          (q : ℝ) * (1 + 4 * ((N : ℝ) * |eta|)) := by
        apply add_le_add
        · apply mul_le_mul (principalMass_le_one hq0) _ (by positivity) (by norm_num)
          nlinarith
        · apply mul_le_mul (nonprincipalMass_le_q a) _ (by positivity) (by positivity)
          nlinarith
      _ ≤ _ := by nlinarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogq : Real.log q ≤ sourceP N := by
    linarith [Real.log_le_sub_one_of_pos hqr]
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hcorr : Real.log q * sourceL N / Real.log 2 ≤ (N : ℝ) / sourceL N^10 := by
    calc
      _ ≤ 2 * sourceL N^4 := by
        apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
        have hh := mul_le_mul_of_nonneg_right hlogq hL.le
        change Real.log q * sourceL N ≤ sourceL N^3 * sourceL N at hh
        nlinarith [mul_nonneg (show 0 ≤ sourceL N^4 by positivity)
          (show 0 ≤ Real.log 2 - 1/2 by linarith)]
      _ ≤ _ := by
        apply (le_div_iff₀ (pow_pos hL 10)).mpr
        have hh := (mul_sourceL_pow_lt (c := 2) (k := 14) hN (by norm_num) (by norm_num)).le
        convert hh using 1; ring
  rw [epsilon_eq]
  apply (errorBound_le_decimal hN a eta).trans
  calc
    _ ≤ 10 * sourceP N * (N : ℝ) / sourceT N * sourceL N^2 +
        (N : ℝ) / sourceL N^10 := by
      apply add_le_add _ hcorr
      gcongr
    _ = 11 * (N : ℝ) / sourceL N^10 := by
      unfold sourceP sourceT
      field_simp
      ring
    _ ≤ _ := by gcongr; norm_num

def uniformError (N : ℕ) : ℝ := 20 * (N : ℝ) / sourceL N^10

theorem uniformError_nonneg (N : ℕ) : 0 ≤ uniformError N := by
  unfold uniformError
  positivity

theorem uniformError_le_N {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    uniformError N ≤ (N : ℝ) := by
  have hL := sourceL_pos hN
  have hpow : (20 : ℝ) ≤ sourceL N^10 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2000) (sourceL_ge_2000 hN) 10
    norm_num at h ⊢
    linarith
  unfold uniformError
  apply (div_le_iff₀ (pow_pos hL 10)).mpr
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (sub_nonneg.mpr hpow)]

end LiuWang.Proof.MajorArcApproximation
