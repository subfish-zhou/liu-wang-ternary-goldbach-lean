import LiuWang.Proof.PrincipalPsi.CenteredZeros
import LiuWang.Proof.PrincipalPsi.ZetaIntegrand
import LiuWang.Proof.PerronBudget.StrongConsumer

/-!
# 真实 ζ 分支的已付 Perron 项及尚未数值闭合的分账

本文件不是 1.3804 显式公式。右积分误差为已验 1.374，极点中心常数
2.5 另付 0.000001；真实轮廓差和真实低/高零点基数仍在右端显式保留。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.PrincipalPsi

theorem psi_mod_one_eq_chebyshev (t : ℝ) :
    ExplicitPerron.psi (1 : DirichletCharacter ℂ 1) t = (Chebyshev.psi t : ℂ) := by
  rw [ExplicitPerron.psi_eq_sum, ExplicitPerron.psi_eq_sum_one, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [MulChar.one_apply (isUnit_of_subsingleton _), mul_one]

def zetaRightIntegral (t b Hminus Hplus : ℝ) : ℂ :=
  ExplicitPerron.vertical
    (fun s => -logDeriv riemannZeta s * ((t : ℂ) ^ s - (2.5 : ℂ) ^ s) / s)
    b Hminus Hplus

theorem zetaRightIntegral_eq_principal (t b Hminus Hplus : ℝ) :
    zetaRightIntegral t b Hminus Hplus =
      ExplicitPerron.vertical
        (ExplicitPerron.centeredIntegrand (1 : DirichletCharacter ℂ 1) t (5 / 2))
        b Hminus Hplus := by
  unfold zetaRightIntegral ExplicitPerron.centeredIntegrand
  simp only [DirichletCharacter.LFunction_modOne_eq, Complex.ofReal_div, Complex.ofReal_ofNat]
  norm_num

theorem zeta_right_perron_strong {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) {t Hminus Hplus : ℝ}
    (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ))
    (hminus : |Hminus + sourceT N| ≤ 1) (hplus : |Hplus - sourceT N| ≤ 1) :
    ‖zetaRightIntegral t (1 + 1 / sourceL N) Hminus Hplus - (Chebyshev.psi t : ℂ)‖ ≤
      1.374 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  rw [zetaRightIntegral_eq_principal, ← psi_mod_one_eq_chebyshev]
  exact PerronBudget.sourceDomain_right_perron_strong 1 hN htlo hthi hminus hplus

theorem pole_center_cost_le_source {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) {t : ℝ} (htlo : sourceWindowLower N ≤ t) :
    (2.5 : ℝ) ≤ 0.000001 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  have hL := sourceL_ge_2000 hN
  have hT := sourceT_pos hN
  have ht := sourceT_lt_real_endpoint hN htlo
  have hratio : 1 ≤ t / sourceT N := (le_div_iff₀ hT).mpr (by linarith)
  have hLsq : (2000 : ℝ) ^ 2 ≤ sourceL N ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hL 2
  calc
    (2.5 : ℝ) ≤ 0.000001 * 1 * (2000 : ℝ) ^ 2 := by norm_num
    _ ≤ 0.000001 * (t / sourceT N) * sourceL N ^ 2 := by gcongr
    _ = _ := by ring

theorem zeta_psi_remainder_ledger {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) {t Hminus Hplus : ℝ}
    (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ))
    (hminus : |Hminus + sourceT N| ≤ 1) (hplus : |Hplus - sourceT N| ≤ 1) :
    ‖(Chebyshev.psi t : ℂ) - (t : ℂ) + highZeroSum 1 t (sourceT N)‖ ≤
      ‖zetaRightIntegral t (1 + 1 / sourceL N) Hminus Hplus -
          ((t : ℂ) - 2.5) + closedCenteredZeroSum 1 t (sourceT N)‖ +
        2 * Real.sqrt t * (lowZeroIndices 1 (sourceT N)).card +
        5 * (highZeroIndices 1 (sourceT N)).card +
        1.374001 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  have hTbig : 2.5 ≤ sourceT N :=
    (by norm_num : (2.5 : ℝ) ≤ 2000 ^ (15 : ℕ)).trans (NonSymmetricContour.sourceT_large hN)
  have ht : 2.5 ≤ t := hTbig.trans (sourceT_lt_real_endpoint hN htlo).le
  have hP := zeta_right_perron_strong hN htlo hthi hminus hplus
  have hK := norm_closedCentered_sub_high_le_card 1 ht (sourceT N)
  have hC := pole_center_cost_le_source hN htlo
  have hCnorm : ‖(2.5 : ℂ)‖ ≤
      0.000001 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
    rw [show ‖(2.5 : ℂ)‖ = (2.5 : ℝ) by norm_num [Complex.norm_def]]
    exact hC
  let R := zetaRightIntegral t (1 + 1 / sourceL N) Hminus Hplus
  let Z := closedCenteredZeroSum 1 t (sourceT N)
  let H := highZeroSum 1 t (sourceT N)
  calc
    _ = ‖(R - ((t : ℂ) - 2.5) + Z) -
        (R - (Chebyshev.psi t : ℂ)) - (Z - H) - (2.5 : ℂ)‖ := by
      congr 1
      dsimp [R, Z, H]
      ring
    _ ≤ ‖R - ((t : ℂ) - 2.5) + Z‖ + ‖R - (Chebyshev.psi t : ℂ)‖ +
        ‖Z - H‖ + ‖(2.5 : ℂ)‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ ‖R - ((t : ℂ) - 2.5) + Z‖ +
        1.374 * t / sourceT N * sourceL N ^ (2 : ℕ) +
        (2 * Real.sqrt t * (lowZeroIndices 1 (sourceT N)).card +
          5 * (highZeroIndices 1 (sourceT N)).card) +
        0.000001 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
      add_le_add (add_le_add (add_le_add le_rfl hP) hK) hCnorm
    _ = _ := by dsimp [R, Z]; ring

end LiuWang.Proof.PrincipalPsi
