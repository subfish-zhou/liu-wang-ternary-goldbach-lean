import LiuWang.Proof.MultiZeroRepulsion.OrdinaryMass
import BombieriVinogradov.Helpers.DirichletCharacter.ComplexConjugation

/-! Same-weight Euler positivity for independent complex characters and heights. -/

set_option autoImplicit false
noncomputable section
open Complex
open ArithmeticFunction hiding log
open scoped Classical ComplexConjugate LSeries.notation
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.MultiZeroRepulsion

def phase {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  chi n * (n : ℂ) ^ (-(I * (t : ℂ)))

theorem phase_one {q n : ℕ} (hu : IsUnit (n : ZMod q)) :
    phase (1 : DirichletCharacter ℂ q) 0 n = 1 := by
  simp [phase, MulChar.one_apply hu]

theorem phase_mul {q n : ℕ} (chi psi : DirichletCharacter ℂ q)
    (hn : n ≠ 0) (t u : ℝ) :
    phase (chi * psi) (t + u) n = phase chi t n * phase psi u n := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [phase, MulChar.mul_apply, ofReal_add]
  rw [show -(I * ((t : ℂ) + u)) = -(I * (t : ℂ)) + -(I * (u : ℂ)) by ring,
    cpow_add _ _ hnc]
  ring

theorem phase_inv {q n : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) :
    phase chi⁻¹ (-t) n = conj (phase chi t n) := by
  rw [phase, phase, map_mul, BombieriVinogradov.DirichletCharacter.conj_apply_eq_inv_apply]
  congr 1
  have hh := BombieriVinogradov.Complex.conj_natCast_cpow_conj n
    (-(I * ((-t : ℝ) : ℂ)))
  simpa using hh.symm

theorem phase_norm {q n : ℕ} (chi : DirichletCharacter ℂ q)
    (hn : n ≠ 0) (hu : IsUnit (n : ZMod q)) (t : ℝ) : ‖phase chi t n‖ = 1 := by
  rw [phase, norm_mul, ← hu.unit_spec, DirichletCharacter.unit_norm_eq_one chi hu.unit,
    one_mul, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)]
  norm_num [Complex.mul_re]

def eulerTerm {q : ℕ} (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (n : ℕ) : ℝ :=
  (LSeries.term (↗chi * ↗Λ) ((sigma : ℂ) + I * t) n).re

theorem eulerTerm_phase {q n : ℕ} (chi : DirichletCharacter ℂ q)
    (hn : n ≠ 0) (sigma t : ℝ) :
    eulerTerm chi sigma t n = Λ n * (n : ℝ) ^ (-sigma) * (phase chi t n).re := by
  unfold eulerTerm phase
  rw [LSeries.term_of_ne_zero hn, Pi.mul_apply, div_eq_mul_inv, ← cpow_neg,
    natCast_cpow_neg_add_I_mul hn]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im]
  ring

theorem eulerTerm_hasSum {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    HasSum (eulerTerm chi sigma t) (-(logDeriv chi.LFunction ((sigma : ℂ) + I * t)).re) := by
  have hr : 1 < ((sigma : ℂ) + I * t).re := by simpa [mul_re] using hs
  have hh := hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hr).LSeriesHasSum
  change HasSum (eulerTerm chi sigma t) _ at hh
  change HasSum (eulerTerm chi sigma t) (-logDeriv chi.LFunction ((sigma : ℂ) + I * t)).re
  simpa only [eulerTerm, logDeriv, Pi.div_apply, ← neg_div,
    neg_logDeriv_LFunction_eq_twist_vonMangoldt _ hr] using hh

theorem damped_polynomial_nonneg {q : ℕ} [NeZero q] {ι : Type*}
    (s : Finset ι) (chi : ι → DirichletCharacter ℂ q) (t c : ι → ℝ)
    (hp : ∀ n : ℕ, n ≠ 0 → IsUnit (n : ZMod q) →
      0 ≤ ∑ j ∈ s, c j * (phase (chi j) (t j) n).re)
    {sigma sigma1 k : ℝ} (hs : 1 < sigma) (hss : sigma ≤ sigma1)
    (hk : k ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ ∑ j ∈ s, c j * dampedLogDeriv (chi j) sigma sigma1 k (t j) := by
  let w a n := ∑ j ∈ s, c j * eulerTerm (chi j) a (t j) n
  have hsum {a : ℝ} (ha : 1 < a) :
      HasSum (w a) (∑ j ∈ s, c j * (-(logDeriv (chi j).LFunction ((a : ℂ) + I * t j)).re)) :=
    hasSum_sum (fun j _ => (eulerTerm_hasSum (chi j) ha (t j)).mul_left (c j))
  have hn (n : ℕ) : 0 ≤ w sigma n - k * w sigma1 n := by
    by_cases hz : n = 0
    · simp [w, eulerTerm, hz]
    by_cases hu : IsUnit (n : ZMod q)
    · have hw (a : ℝ) : w a n =
          (Λ n * (n : ℝ) ^ (-a)) * ∑ j ∈ s, c j * (phase (chi j) (t j) n).re := by
        dsimp [w]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [eulerTerm_phase _ hz]
        ring
      rw [hw, hw]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      have hm : (n : ℝ) ^ (-sigma1) ≤ (n : ℝ) ^ (-sigma) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      have hn0 : 0 ≤ Λ n * (n : ℝ) ^ (-sigma1) :=
        mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hkm := mul_le_mul_of_nonneg_right hk.2 hn0
      have hb := mul_le_mul_of_nonneg_left hm (show 0 ≤ Λ n from vonMangoldt_nonneg)
      nlinarith [hp n hz hu]
    · have hz' (j : ι) : chi j n = 0 := MulChar.map_nonunit _ hu
      simp [w, eulerTerm, LSeries.term_of_ne_zero hz, hz']
  have hh : 0 ≤ ∑' n, (w sigma n - k * w sigma1 n) := tsum_nonneg hn
  rw [((hsum hs).sub ((hsum (hs.trans_le hss)).mul_left k)).tsum_eq] at hh
  convert hh using 1
  simp only [dampedLogDeriv, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_neg_distrib, mul_add, mul_neg]
  congr 1
  rw [neg_neg]
  apply Finset.sum_congr rfl
  intro j _
  ring

def pairCharacters {q : ℕ} (chi psi : DirichletCharacter ℂ q) :
    Fin 5 → DirichletCharacter ℂ q := ![1, chi, psi, chi * psi, chi * psi⁻¹]

def pairHeights (t u : ℝ) : Fin 5 → ℝ := ![0, t, u, t + u, t - u]

def pairCoefficients : Fin 5 → ℝ := ![2, 2, 2, 1, 1]

theorem pair_phase_nonneg {q n : ℕ} (chi psi : DirichletCharacter ℂ q)
    (hn : n ≠ 0) (hu : IsUnit (n : ZMod q)) (t u : ℝ) :
    0 ≤ ∑ j : Fin 5, pairCoefficients j *
      (phase (pairCharacters chi psi j) (pairHeights t u j) n).re := by
  have hchi := (neg_le_abs (phase chi t n).re).trans (abs_re_le_norm _)
  have hpsi := (neg_le_abs (phase psi u n).re).trans (abs_re_le_norm _)
  rw [phase_norm chi hn hu] at hchi
  rw [phase_norm psi hn hu] at hpsi
  have he : (∑ j : Fin 5, pairCoefficients j *
      (phase (pairCharacters chi psi j) (pairHeights t u j) n).re) =
      2 * (1 + (phase chi t n).re) * (1 + (phase psi u n).re) := by
    simp only [Fin.sum_univ_succ, pairCharacters, pairHeights, pairCoefficients,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    rw [phase_one hu, phase_mul chi psi hn, sub_eq_add_neg, phase_mul chi psi⁻¹ hn, phase_inv]
    simp only [one_re, mul_re, conj_re, conj_im]
    ring
  rw [he]
  exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)

theorem pair_euler_nonneg {q : ℕ} [NeZero q] (chi psi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t u : ℝ) :
    0 ≤ ∑ j : Fin 5, pairCoefficients j *
      dampedLogDeriv (pairCharacters chi psi j) sigma (stechkinSigma sigma) stechkinK
        (pairHeights t u j) :=
  damped_polynomial_nonneg Finset.univ (pairCharacters chi psi) (pairHeights t u)
    pairCoefficients (fun _n hn hu => pair_phase_nonneg chi psi hn hu t u)
    hs (stechkinSigma_ge hs) stechkinK_mem

end LiuWang.Proof.MultiZeroRepulsion
