import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralLcm

set_option autoImplicit false
noncomputable section

open Complex
open ArithmeticFunction hiding log
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.NearOneDensity.Continuation

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1

def lwdProduct {d e : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) : DirichletCharacter ℂ (Nat.lcm d e) :=
  mixedQuotient chi psi⁻¹

theorem lwdProduct_apply {d e : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (n : ℕ) :
    lwdProduct chi psi n = chi n * psi n := by
  simp only [lwdProduct, mixedQuotient_nat_apply,
    BombieriVinogradov.DirichletCharacter.conj_apply_eq_inv_apply, inv_inv]

theorem lwdProduct_phase {d e n : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (hn : n ≠ 0) (t u : ℝ) :
    phase (lwdProduct chi psi) (t + u) n = phase chi t n * phase psi u n := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [phase, lwdProduct_apply, ofReal_add]
  rw [show -(I * ((t : ℂ) + u)) = -(I * (t : ℂ)) + -(I * (u : ℂ)) by ring,
    cpow_add _ _ hnc]
  ring

def lwdGTerm {d e f : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f)
    (sigma t u v : ℝ) (n : ℕ) : ℝ :=
  eulerTerm (1 : DirichletCharacter ℂ 1) sigma 0 n +
    eulerTerm chi sigma t n + eulerTerm psi sigma u n + eulerTerm eta sigma v n +
    eulerTerm (lwdProduct chi psi) sigma (t + u) n +
    eulerTerm (lwdProduct chi eta) sigma (t + v) n +
    eulerTerm (lwdProduct psi eta) sigma (u + v) n +
    eulerTerm (lwdProduct (lwdProduct chi psi) eta) sigma (t + u + v) n

def lwdFourGTerm {d e f : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f)
    (sigma t u v : ℝ) (n : ℕ) : ℝ :=
  lwdGTerm chi psi eta sigma t u v n +
    lwdGTerm chi psi⁻¹ eta sigma t (-u) v n +
    lwdGTerm chi psi eta⁻¹ sigma t u (-v) n +
    lwdGTerm chi psi⁻¹ eta⁻¹ sigma t (-u) (-v) n

theorem lwdFourGTerm_factor {d e f n : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f)
    (hn : n ≠ 0) (sigma t u v : ℝ) :
    lwdFourGTerm chi psi eta sigma t u v n =
      4 * Λ n * (n : ℝ) ^ (-sigma) * (1 + (phase chi t n).re) *
        (1 + (phase psi u n).re) * (1 + (phase eta v n).re) := by
  have hu : IsUnit (n : ZMod 1) := by
    rw [Subsingleton.elim (n : ZMod 1) 1]
    exact isUnit_one
  simp only [lwdFourGTerm, lwdGTerm, eulerTerm_phase _ hn, phase_one hu,
    lwdProduct_phase _ _ hn, phase_inv, one_re, mul_re, mul_im, conj_re, conj_im]
  ring

theorem lwdFourGTerm_nonneg {d e f : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f)
    (sigma t u v : ℝ) (n : ℕ) :
    0 ≤ lwdFourGTerm chi psi eta sigma t u v n := by
  by_cases hn : n = 0
  · simp [lwdFourGTerm, lwdGTerm, eulerTerm, hn]
  rw [lwdFourGTerm_factor chi psi eta hn]
  have hc := (neg_le_abs (phase chi t n).re).trans
    ((abs_re_le_norm _).trans (phase_norm_le_one chi hn t))
  have hp := (neg_le_abs (phase psi u n).re).trans
    ((abs_re_le_norm _).trans (phase_norm_le_one psi hn u))
  have he := (neg_le_abs (phase eta v n).re).trans
    ((abs_re_le_norm _).trans (phase_norm_le_one eta hn v))
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num) vonMangoldt_nonneg)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by linarith)) (by linarith)) (by linarith)

theorem lwdFourGTerm_antitone {d e f : ℕ} (chi : DirichletCharacter ℂ d)
    (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f)
    {sigma tau : ℝ} (hs : sigma ≤ tau) (t u v : ℝ) (n : ℕ) :
    lwdFourGTerm chi psi eta tau t u v n ≤ lwdFourGTerm chi psi eta sigma t u v n := by
  by_cases hn : n = 0
  · simp [lwdFourGTerm, lwdGTerm, eulerTerm, hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have he : lwdFourGTerm chi psi eta tau t u v n =
      (n : ℝ) ^ (sigma - tau) * lwdFourGTerm chi psi eta sigma t u v n := by
    rw [lwdFourGTerm_factor chi psi eta hn, lwdFourGTerm_factor chi psi eta hn]
    have hr : (n : ℝ) ^ (sigma - tau) * (n : ℝ) ^ (-sigma) = (n : ℝ) ^ (-tau) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    rw [← hr]
    ring
  rw [he]
  have hf := Real.rpow_le_one_of_one_le_of_nonpos hn1 (show sigma - tau ≤ 0 by linarith)
  simpa using mul_le_mul_of_nonneg_right hf (lwdFourGTerm_nonneg chi psi eta sigma t u v n)

def lwdG {d e f : ℕ} [NeZero d] [NeZero e] [NeZero f]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) (sigma t u v : ℝ) : ℝ :=
  dampedLogDeriv (1 : DirichletCharacter ℂ 1) sigma (stechkinSigma sigma) stechkinK 0 +
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t +
    dampedLogDeriv psi sigma (stechkinSigma sigma) stechkinK u +
    dampedLogDeriv eta sigma (stechkinSigma sigma) stechkinK v +
    dampedLogDeriv (lwdProduct chi psi) sigma (stechkinSigma sigma) stechkinK (t + u) +
    dampedLogDeriv (lwdProduct chi eta) sigma (stechkinSigma sigma) stechkinK (t + v) +
    dampedLogDeriv (lwdProduct psi eta) sigma (stechkinSigma sigma) stechkinK (u + v) +
    dampedLogDeriv (lwdProduct (lwdProduct chi psi) eta)
      sigma (stechkinSigma sigma) stechkinK (t + u + v)

theorem lwdG_hasSum {d e f : ℕ} [NeZero d] [NeZero e] [NeZero f]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) {sigma : ℝ} (hs : 1 < sigma) (t u v : ℝ) :
    HasSum (fun n => lwdGTerm chi psi eta sigma t u v n -
      stechkinK * lwdGTerm chi psi eta (stechkinSigma sigma) t u v n)
      (lwdG chi psi eta sigma t u v) := by
  have hsum {a : ℝ} (ha : 1 < a) :=
    (((((((eulerTerm_hasSum (1 : DirichletCharacter ℂ 1) ha 0).add
      (eulerTerm_hasSum chi ha t)).add (eulerTerm_hasSum psi ha u)).add
      (eulerTerm_hasSum eta ha v)).add (eulerTerm_hasSum (lwdProduct chi psi) ha (t + u))).add
      (eulerTerm_hasSum (lwdProduct chi eta) ha (t + v))).add
      (eulerTerm_hasSum (lwdProduct psi eta) ha (u + v))).add
      (eulerTerm_hasSum (lwdProduct (lwdProduct chi psi) eta) ha (t + u + v))
  have hh := (hsum hs).sub ((hsum (hs.trans_le (stechkinSigma_ge hs))).mul_left stechkinK)
  convert hh using 1 <;> first | rfl | (dsimp [lwdG, dampedLogDeriv]; ring)

theorem lwd_2_13 {d e f : ℕ} [NeZero d] [NeZero e] [NeZero f]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) {sigma : ℝ} (hs : 1 < sigma) (t u v : ℝ) :
    0 ≤ lwdG chi psi eta sigma t u v +
      lwdG chi psi⁻¹ eta sigma t (-u) v +
      lwdG chi psi eta⁻¹ sigma t u (-v) +
      lwdG chi psi⁻¹ eta⁻¹ sigma t (-u) (-v) := by
  have hh := (((lwdG_hasSum chi psi eta hs t u v).add
    (lwdG_hasSum chi psi⁻¹ eta hs t (-u) v)).add
    (lwdG_hasSum chi psi eta⁻¹ hs t u (-v))).add
    (lwdG_hasSum chi psi⁻¹ eta⁻¹ hs t (-u) (-v))
  rw [← hh.tsum_eq]
  apply tsum_nonneg
  intro n
  have ha := lwdFourGTerm_antitone chi psi eta (stechkinSigma_ge hs) t u v n
  have hb := mul_le_mul_of_nonneg_right stechkinK_mem.2
    (lwdFourGTerm_nonneg chi psi eta (stechkinSigma sigma) t u v n)
  dsimp [lwdFourGTerm] at ha hb
  linarith

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1
