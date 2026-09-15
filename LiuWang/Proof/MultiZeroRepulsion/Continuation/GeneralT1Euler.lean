import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralOutputs

/-! The four genuine three-character Euler products, at their own lcm levels. -/

set_option autoImplicit false
noncomputable section
open Complex
open ArithmeticFunction hiding log
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.NearOneDensity.Continuation

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

def t1Product {d e : ℕ} (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) :
    DirichletCharacter ℂ (Nat.lcm d e) := mixedQuotient chi psi⁻¹

theorem t1Product_apply {d e : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (n : ℕ) :
    t1Product chi psi n = chi n * psi n := by
  rw [t1Product, mixedQuotient_nat_apply,
    BombieriVinogradov.DirichletCharacter.conj_apply_eq_inv_apply, inv_inv]

theorem t1Product_changeLevel {d e q : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (hd : d ∣ q) (he : e ∣ q) :
    (t1Product chi psi).changeLevel (Nat.lcm_dvd hd he) =
      chi.changeLevel hd * psi.changeLevel he := by
  rw [t1Product, mixed_quotient_changeLevel, map_inv]
  change _ * star _ = _
  rw [MulChar.star_eq_inv, inv_inv]

theorem t1Product_phase {d e n : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (hn : n ≠ 0) (t u : ℝ) :
    phase (t1Product chi psi) (t + u) n = phase chi t n * phase psi u n := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [phase, t1Product_apply, ofReal_add]
  rw [show -(I * ((t : ℂ) + u)) = -(I * (t : ℂ)) + -(I * (u : ℂ)) by ring,
    cpow_add _ _ hnc]
  ring

def t1GTerm {d e f : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f)
    (sigma t u v : ℝ) (n : ℕ) : ℝ :=
  eulerTerm (1 : DirichletCharacter ℂ 1) sigma 0 n +
    eulerTerm chi sigma t n + eulerTerm psi sigma u n + eulerTerm eta sigma v n +
    eulerTerm (t1Product chi psi) sigma (t + u) n +
    eulerTerm (t1Product chi eta) sigma (t + v) n +
    eulerTerm (t1Product psi eta) sigma (u + v) n +
    eulerTerm (t1Product (t1Product chi psi) eta) sigma (t + u + v) n

def t1G {d e f : ℕ} [NeZero d] [NeZero e] [NeZero f]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) (sigma t u v : ℝ) : ℝ :=
  zetaDamped sigma 0 +
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t +
    dampedLogDeriv psi sigma (stechkinSigma sigma) stechkinK u +
    dampedLogDeriv eta sigma (stechkinSigma sigma) stechkinK v +
    dampedLogDeriv (t1Product chi psi) sigma (stechkinSigma sigma) stechkinK (t + u) +
    dampedLogDeriv (t1Product chi eta) sigma (stechkinSigma sigma) stechkinK (t + v) +
    dampedLogDeriv (t1Product psi eta) sigma (stechkinSigma sigma) stechkinK (u + v) +
    dampedLogDeriv (t1Product (t1Product chi psi) eta)
      sigma (stechkinSigma sigma) stechkinK (t + u + v)

theorem t1G_hasSum {d e f : ℕ} [NeZero d] [NeZero e] [NeZero f]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) {sigma : ℝ} (hs : 1 < sigma) (t u v : ℝ) :
    HasSum (fun n => t1GTerm chi psi eta sigma t u v n -
      stechkinK * t1GTerm chi psi eta (stechkinSigma sigma) t u v n)
      (t1G chi psi eta sigma t u v) := by
  have hh {a : ℝ} (ha : 1 < a) :=
    (((((((eulerTerm_hasSum (1 : DirichletCharacter ℂ 1) ha 0).add
      (eulerTerm_hasSum chi ha t)).add (eulerTerm_hasSum psi ha u)).add
      (eulerTerm_hasSum eta ha v)).add (eulerTerm_hasSum (t1Product chi psi) ha (t + u))).add
      (eulerTerm_hasSum (t1Product chi eta) ha (t + v))).add
      (eulerTerm_hasSum (t1Product psi eta) ha (u + v))).add
      (eulerTerm_hasSum (t1Product (t1Product chi psi) eta) ha (t + u + v))
  have h := (hh hs).sub ((hh (hs.trans_le (stechkinSigma_ge hs))).mul_left stechkinK)
  convert h using 1 <;> try rfl
  unfold t1G dampedLogDeriv zetaDamped
  simp only [DirichletCharacter.LFunction_modOne_eq, ofReal_zero, mul_zero, add_zero]
  ring

theorem t1_four_terms {d e f n : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f)
    (hn : n ≠ 0) (sigma t u v : ℝ) :
    t1GTerm chi psi eta sigma t u v n +
      t1GTerm chi psi⁻¹ eta sigma t (-u) v n +
      t1GTerm chi psi eta⁻¹ sigma t u (-v) n +
      t1GTerm chi psi⁻¹ eta⁻¹ sigma t (-u) (-v) n =
      4 * Λ n * (n : ℝ) ^ (-sigma) *
        (1 + (phase chi t n).re) * (1 + (phase psi u n).re) * (1 + (phase eta v n).re) := by
  have hu : IsUnit (n : ZMod 1) := by
    rw [Subsingleton.elim (n : ZMod 1) 1]
    exact isUnit_one
  simp only [t1GTerm, eulerTerm_phase _ hn, phase_one hu,
    t1Product_phase _ _ hn, phase_inv, one_re, mul_re, mul_im, conj_re, conj_im]
  ring

theorem t1_euler_nonneg {d e f : ℕ} [NeZero d] [NeZero e] [NeZero f]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) {sigma : ℝ} (hs : 1 < sigma) (t u v : ℝ) :
    0 ≤ t1G chi psi eta sigma t u v + t1G chi psi⁻¹ eta sigma t (-u) v +
      t1G chi psi eta⁻¹ sigma t u (-v) + t1G chi psi⁻¹ eta⁻¹ sigma t (-u) (-v) := by
  have hh := (((t1G_hasSum chi psi eta hs t u v).add
    (t1G_hasSum chi psi⁻¹ eta hs t (-u) v)).add
    (t1G_hasSum chi psi eta⁻¹ hs t u (-v))).add
    (t1G_hasSum chi psi⁻¹ eta⁻¹ hs t (-u) (-v))
  rw [← hh.tsum_eq]
  apply tsum_nonneg
  intro n
  by_cases hn : n = 0
  · simp [t1GTerm, eulerTerm, hn]
  have hpoly (a : ℝ) := t1_four_terms chi psi eta hn a t u v
  have hc := (neg_le_abs (phase chi t n).re).trans
    ((abs_re_le_norm _).trans (phase_norm_le_one chi hn t))
  have hp := (neg_le_abs (phase psi u n).re).trans
    ((abs_re_le_norm _).trans (phase_norm_le_one psi hn u))
  have he := (neg_le_abs (phase eta v n).re).trans
    ((abs_re_le_norm _).trans (phase_norm_le_one eta hn v))
  have hprod : 0 ≤ 4 * Λ n * (1 + (phase chi t n).re) *
      (1 + (phase psi u n).re) * (1 + (phase eta v n).re) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) vonMangoldt_nonneg)
      (by linarith)) (by linarith)) (by linarith)
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ n by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    (neg_le_neg (stechkinSigma_ge hs))
  have hk := mul_le_mul_of_nonneg_right stechkinK_mem.2
    (Real.rpow_nonneg (Nat.cast_nonneg n) (-stechkinSigma sigma))
  have hbound := mul_nonneg hprod
    (show 0 ≤ (n : ℝ) ^ (-sigma) - stechkinK * (n : ℝ) ^ (-stechkinSigma sigma) by linarith)
  have hrewrite :
      t1GTerm chi psi eta sigma t u v n - stechkinK * t1GTerm chi psi eta (stechkinSigma sigma) t u v n +
      (t1GTerm chi psi⁻¹ eta sigma t (-u) v n - stechkinK * t1GTerm chi psi⁻¹ eta (stechkinSigma sigma) t (-u) v n) +
      (t1GTerm chi psi eta⁻¹ sigma t u (-v) n - stechkinK * t1GTerm chi psi eta⁻¹ (stechkinSigma sigma) t u (-v) n) +
      (t1GTerm chi psi⁻¹ eta⁻¹ sigma t (-u) (-v) n - stechkinK * t1GTerm chi psi⁻¹ eta⁻¹ (stechkinSigma sigma) t (-u) (-v) n) =
      (t1GTerm chi psi eta sigma t u v n + t1GTerm chi psi⁻¹ eta sigma t (-u) v n +
        t1GTerm chi psi eta⁻¹ sigma t u (-v) n + t1GTerm chi psi⁻¹ eta⁻¹ sigma t (-u) (-v) n) -
      stechkinK * (t1GTerm chi psi eta (stechkinSigma sigma) t u v n +
        t1GTerm chi psi⁻¹ eta (stechkinSigma sigma) t (-u) v n +
        t1GTerm chi psi eta⁻¹ (stechkinSigma sigma) t u (-v) n +
        t1GTerm chi psi⁻¹ eta⁻¹ (stechkinSigma sigma) t (-u) (-v) n) := by ring
  rw [hrewrite, hpoly, hpoly]
  convert hbound using 1
  ring

end LiuWang.Proof.MultiZeroRepulsion.Continuation
