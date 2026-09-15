import LiuWang.Proof.MultiZeroRepulsion.FullWindow
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticTatuzawaMultiplicativeValueTransfer

/-! Genuine same-weight Euler positivity across distinct conductor levels. -/

set_option autoImplicit false
noncomputable section
open Complex
open ArithmeticFunction hiding log
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem phase_norm_le_one {q n : ℕ} (chi : DirichletCharacter ℂ q)
    (hn : n ≠ 0) (t : ℝ) : ‖phase chi t n‖ ≤ 1 := by
  by_cases hu : IsUnit (n : ZMod q)
  · exact (phase_norm chi hn hu t).le
  · simp [phase, MulChar.map_nonunit chi hu]

theorem phase_pairCharacter {q r n : ℕ}
    (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    (hn : n ≠ 0) (t u : ℝ) :
    phase (pairCharacter chi psi) (t + u) n = phase chi t n * phase psi u n := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [phase, pairCharacter_apply, ofReal_add]
  rw [show -(I * ((t : ℂ) + u)) = -(I * (t : ℂ)) + -(I * (u : ℂ)) by ring,
    cpow_add _ _ hnc]
  ring

def heteroWeight {q r : ℕ} (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    (sigma t u : ℝ) (n : ℕ) : ℝ :=
  2 * eulerTerm (1 : DirichletCharacter ℂ 1) sigma 0 n +
    2 * eulerTerm chi sigma t n + 2 * eulerTerm psi sigma u n +
    eulerTerm (pairCharacter chi psi) sigma (t + u) n +
    eulerTerm (pairCharacter chi psi⁻¹) sigma (t - u) n

theorem heteroWeight_eq {q r n : ℕ} (chi : DirichletCharacter ℂ q)
    (psi : DirichletCharacter ℂ r) (hn : n ≠ 0) (sigma t u : ℝ) :
    heteroWeight chi psi sigma t u n =
      2 * Λ n * (n : ℝ) ^ (-sigma) * (1 + (phase chi t n).re) *
        (1 + (phase psi u n).re) := by
  have hu : IsUnit (n : ZMod 1) := by
    rw [Subsingleton.elim (n : ZMod 1) 1]
    exact isUnit_one
  simp only [heteroWeight, eulerTerm_phase _ hn]
  rw [phase_one hu, phase_pairCharacter chi psi hn, sub_eq_add_neg,
    phase_pairCharacter chi psi⁻¹ hn, phase_inv]
  simp only [one_re, mul_re, conj_re, conj_im]
  ring

theorem heteroWeight_nonneg {q r : ℕ} (chi : DirichletCharacter ℂ q)
    (psi : DirichletCharacter ℂ r) (sigma t u : ℝ) (n : ℕ) :
    0 ≤ heteroWeight chi psi sigma t u n := by
  by_cases hn : n = 0
  · simp [heteroWeight, eulerTerm, hn]
  rw [heteroWeight_eq chi psi hn]
  have hc := (neg_le_abs (phase chi t n).re).trans
    ((abs_re_le_norm _).trans (phase_norm_le_one chi hn t))
  have hp := (neg_le_abs (phase psi u n).re).trans
    ((abs_re_le_norm _).trans (phase_norm_le_one psi hn u))
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) vonMangoldt_nonneg)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by linarith)) (by linarith)

theorem heteroWeight_antitone {q r : ℕ} (chi : DirichletCharacter ℂ q)
    (psi : DirichletCharacter ℂ r) {sigma sigma1 : ℝ} (hs : sigma ≤ sigma1) (t u : ℝ) (n : ℕ) :
    heteroWeight chi psi sigma1 t u n ≤ heteroWeight chi psi sigma t u n := by
  by_cases hn : n = 0
  · simp [heteroWeight, eulerTerm, hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have he : heteroWeight chi psi sigma1 t u n =
      (n : ℝ) ^ (sigma - sigma1) * heteroWeight chi psi sigma t u n := by
    rw [heteroWeight_eq chi psi hn, heteroWeight_eq chi psi hn]
    have hr : (n : ℝ) ^ (sigma - sigma1) * (n : ℝ) ^ (-sigma) = (n : ℝ) ^ (-sigma1) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    calc
      _ = 2 * Λ n * ((n : ℝ) ^ (sigma - sigma1) * (n : ℝ) ^ (-sigma)) *
          (1 + (phase chi t n).re) * (1 + (phase psi u n).re) := by rw [hr]
      _ = _ := by ring
  rw [he]
  have hf := Real.rpow_le_one_of_one_le_of_nonpos hn1 (show sigma - sigma1 ≤ 0 by linarith)
  simpa using mul_le_mul_of_nonneg_right hf (heteroWeight_nonneg chi psi sigma t u n)

theorem heterolevel_pair_euler_nonneg {q r : ℕ} [NeZero q] [NeZero r] [NeZero (q * r)]
    (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    {sigma : ℝ} (hs : 1 < sigma) (t u : ℝ) :
    0 ≤ 2 * zetaDamped sigma 0 +
      2 * dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t +
      2 * dampedLogDeriv psi sigma (stechkinSigma sigma) stechkinK u +
      dampedLogDeriv (pairCharacter chi psi) sigma (stechkinSigma sigma) stechkinK (t + u) +
      dampedLogDeriv (pairCharacter chi psi⁻¹) sigma (stechkinSigma sigma) stechkinK (t - u) := by
  have hsum {a : ℝ} (ha : 1 < a) := ((((eulerTerm_hasSum (1 : DirichletCharacter ℂ 1) ha 0).mul_left 2).add
    ((eulerTerm_hasSum chi ha t).mul_left 2)).add ((eulerTerm_hasSum psi ha u).mul_left 2)).add
    (eulerTerm_hasSum (pairCharacter chi psi) ha (t + u)) |>.add
    (eulerTerm_hasSum (pairCharacter chi psi⁻¹) ha (t - u))
  have hh := (hsum hs).sub ((hsum (hs.trans_le (stechkinSigma_ge hs))).mul_left stechkinK)
  have hn : 0 ≤ ∑' n, (heteroWeight chi psi sigma t u n -
      stechkinK * heteroWeight chi psi (stechkinSigma sigma) t u n) := by
    apply tsum_nonneg
    intro n
    have ha := heteroWeight_antitone chi psi (stechkinSigma_ge hs) t u n
    have hb := mul_le_mul_of_nonneg_right stechkinK_mem.2
      (heteroWeight_nonneg chi psi (stechkinSigma sigma) t u n)
    linarith
  change HasSum (fun n => heteroWeight chi psi sigma t u n -
    stechkinK * heteroWeight chi psi (stechkinSigma sigma) t u n) _ at hh
  rw [hh.tsum_eq] at hn
  simp only [DirichletCharacter.LFunction_modOne_eq, ofReal_zero, mul_zero, add_zero] at hn
  convert hn using 1
  dsimp [dampedLogDeriv, zetaDamped]
  simp only [mul_zero, add_zero]
  ring

theorem heterolevel_selected_bound {q r : ℕ} [NeZero q] [NeZero r] [NeZero (q * r)]
    (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (t u : ℝ)
    (v w a b : Finset ℂ)
    (hv : ∀ z ∈ v, 1 / 2 < z.re ∧ z.re < 1)
    (hw : ∀ z ∈ w, 1 / 2 < z.re ∧ z.re < 1)
    (ha : ∀ z ∈ a, 1 / 2 < z.re ∧ z.re < 1)
    (hb : ∀ z ∈ b, 1 / 2 < z.re ∧ z.re < 1) :
    2 * ordinaryMass chi sigma t v + 2 * ordinaryMass psi sigma u w +
      ordinaryMass (pairCharacter chi psi) sigma (t + u) a +
      ordinaryMass (pairCharacter chi psi⁻¹) sigma (t - u) b ≤
      2 / (sigma - 1) - 3 / 2 + 2 * ordinaryCost chi sigma t + 2 * ordinaryCost psi sigma u +
        ordinaryCost (pairCharacter chi psi) sigma (t + u) +
        ordinaryCost (pairCharacter chi psi⁻¹) sigma (t - u) := by
  have he := heterolevel_pair_euler_nonneg chi psi hs t u
  have h0 := zeta_real_strong hs hs1
  have h1 := ordinary_selected_bound chi hs hs1 t v hv
  have h2 := ordinary_selected_bound psi hs hs1 u w hw
  have h3 := ordinary_selected_bound (pairCharacter chi psi) hs hs1 (t + u) a ha
  have h4 := ordinary_selected_bound (pairCharacter chi psi⁻¹) hs hs1 (t - u) b hb
  simp only [div_eq_mul_inv] at h0 ⊢
  linarith only [he, h0, h1, h2, h3, h4]

theorem heterolevel_full_window_bound {q r : ℕ} [NeZero q] [NeZero r] [NeZero (q * r)]
    (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    {sigma alpha : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha) (y t u : ℝ) :
    2 * ordinaryMass chi sigma t (strictZeroValues chi alpha y) +
      2 * ordinaryMass psi sigma u (strictZeroValues psi alpha y) +
      ordinaryMass (pairCharacter chi psi) sigma (t + u)
        (strictZeroValues (pairCharacter chi psi) alpha y) +
      ordinaryMass (pairCharacter chi psi⁻¹) sigma (t - u)
        (strictZeroValues (pairCharacter chi psi⁻¹) alpha y) ≤
      2 / (sigma - 1) - 3 / 2 + 2 * ordinaryCost chi sigma t + 2 * ordinaryCost psi sigma u +
        ordinaryCost (pairCharacter chi psi) sigma (t + u) +
        ordinaryCost (pairCharacter chi psi⁻¹) sigma (t - u) := by
  apply heterolevel_selected_bound chi psi hs hs1 t u
  all_goals
    intro z hz
    have hh := mem_strictZeroValues.mp hz
    exact ⟨ha.trans_lt hh.2.2.1, hh.2.2.2.1⟩

end LiuWang.Proof.MultiZeroRepulsion.Continuation
