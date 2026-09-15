import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import LiuWang.Proof.Campaign20260915.ZetaValidation.NormalizedEvaluation
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
noncomputable section

open Complex Filter Finset
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def gammaLogBranch (z : ℂ) : ℂ := limUnder atTop (Complex.logGammaSeq z)

theorem exp_gammaLogBranch {z : ℂ} (hz : 0 < z.re) :
    Complex.exp (gammaLogBranch z) = Complex.Gamma z := by
  have ht := (Complex.cauchySeq_logGammaSeq hz).tendsto_limUnder
  have he := Complex.continuous_exp.continuousAt.tendsto.comp ht
  have hseq : (fun n => Complex.exp (Complex.logGammaSeq z n)) =ᶠ[atTop]
      Complex.GammaSeq z := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact Complex.exp_logGammaSeq hz hn
  exact tendsto_nhds_unique (he.congr' hseq) (Complex.GammaSeq_tendsto_Gamma z)

theorem log_successor_error {n : ℕ} (hn : 1 ≤ n) :
    |Real.log ((n : ℝ) + 1) - Real.log n - 1 / ((n : ℝ) + 1)| ≤
      1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) / (n + 1) by positivity)
  have hu := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at hl hu
  have ha : (n : ℝ) / (n + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by field_simp; ring
  have hb : ((n : ℝ) + 1) / n - 1 - 1 / ((n : ℝ) + 1) =
      1 / ((n : ℝ) * ((n : ℝ) + 1)) := by field_simp; ring
  rw [ha] at hl
  rw [abs_le]
  constructor
  · linarith [show (0 : ℝ) ≤ 1 / ((n : ℝ) * ((n : ℝ) + 1)) by positivity]
  · linarith

theorem logGammaSeq_step_bound {z : ℂ} (hz : 0 < z.re) {n : ℕ}
    (hn : 1 ≤ n) (hnz : 2 * ‖z‖ ≤ (n : ℝ)) :
    ‖Complex.logGammaSeq z (n + 1) - Complex.logGammaSeq z n‖ ≤
      (‖z‖ + ‖z‖ ^ 2) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hw : ‖z / ((n : ℂ) + 1)‖ = ‖z‖ / ((n : ℝ) + 1) := by
    rw [norm_div, Complex.norm_natCast_add_one]
  have hw2 : ‖z / ((n : ℂ) + 1)‖ ≤ 1 / 2 := by
    rw [hw, div_le_iff₀ (by positivity)]
    linarith
  have hl : ‖z / ((n : ℂ) + 1) - log (1 + z / ((n : ℂ) + 1))‖ ≤
      ‖z / ((n : ℂ) + 1)‖ ^ 2 := by
    rw [norm_sub_rev]
    have h := Complex.norm_log_one_add_sub_self_le (lt_of_le_of_lt hw2 (by norm_num))
    have hi : (1 - ‖z / ((n : ℂ) + 1)‖)⁻¹ ≤ (2 : ℝ) := by
      rw [← one_div, div_le_iff₀ (by linarith)]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg ‖z / ((n : ℂ) + 1)‖)]
  have he :
      z * ((Real.log ((n : ℝ) + 1) - Real.log n : ℝ) : ℂ) -
        log (1 + z / ((n : ℂ) + 1)) =
      z * ((Real.log ((n : ℝ) + 1) - Real.log n - 1 / ((n : ℝ) + 1) : ℝ) : ℂ) +
        (z / ((n : ℂ) + 1) - log (1 + z / ((n : ℂ) + 1))) := by
    push_cast
    ring
  rw [Complex.logGammaSeq_succ_sub hz, he]
  have hb := mul_le_mul_of_nonneg_left (log_successor_error hn) (norm_nonneg z)
  have hh := norm_add_le
    (z * ((Real.log ((n : ℝ) + 1) - Real.log n - 1 / ((n : ℝ) + 1) : ℝ) : ℂ))
    (z / ((n : ℂ) + 1) - log (1 + z / ((n : ℂ) + 1)))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hh
  have hp : (‖z‖ / ((n : ℝ) + 1)) ^ 2 ≤
      ‖z‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [div_pow]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith
  rw [hw] at hl
  have ht : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) =
      1 / ((n : ℝ) * ((n : ℝ) + 1)) := by field_simp; ring
  rw [ht]
  calc
    _ ≤ ‖z‖ * (1 / ((n : ℝ) * ((n : ℝ) + 1))) +
        ‖z‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
      hh.trans (add_le_add hb (hl.trans hp))
    _ = _ := by ring

theorem gammaLogBranch_error {z : ℂ} (hz : 0 < z.re) {N : ℕ}
    (hN : 1 ≤ N) (hNz : 2 * ‖z‖ ≤ (N : ℝ)) :
    ‖gammaLogBranch z - Complex.logGammaSeq z N‖ ≤ (‖z‖ + ‖z‖ ^ 2) / N := by
  let C : ℝ := ‖z‖ + ‖z‖ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfinite (k : ℕ) :
      ‖Complex.logGammaSeq z (N + k) - Complex.logGammaSeq z N‖ ≤
        C * (1 / (N : ℝ) - 1 / ((N + k : ℕ) : ℝ)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hNk : (N : ℝ) ≤ (N + k : ℕ) := by exact_mod_cast Nat.le_add_right N k
      have hb := logGammaSeq_step_bound hz (n := N + k) (by omega) (hNz.trans hNk)
      have ht := norm_add_le
        (Complex.logGammaSeq z (N + k + 1) - Complex.logGammaSeq z (N + k))
        (Complex.logGammaSeq z (N + k) - Complex.logGammaSeq z N)
      rw [sub_add_sub_cancel] at ht
      rw [Nat.add_succ]
      push_cast at hb ih ⊢
      dsimp [C] at ih ⊢
      linarith
  have ht : Tendsto (fun k => Complex.logGammaSeq z (N + k)) atTop (𝓝 (gammaLogBranch z)) := by
    simpa [gammaLogBranch, Function.comp_def, Nat.add_comm] using
      (Complex.cauchySeq_logGammaSeq hz).tendsto_limUnder.comp (tendsto_add_atTop_nat N)
  apply le_of_tendsto (ht.sub_const (Complex.logGammaSeq z N)).norm
  apply Filter.Eventually.of_forall
  intro k
  have h := hfinite k
  have hp : 0 ≤ 1 / (((N + k : ℕ) : ℝ)) := by positivity
  dsimp [C] at h hC
  simp only [div_eq_mul_inv] at h hp ⊢
  nlinarith [mul_nonneg hC hp]

def criticalGammaArgument (t : ℝ) : ℝ :=
  (gammaLogBranch (criticalPoint t / 2) -
    criticalPoint t / 2 * (Real.log Real.pi : ℂ)).im

def criticalGammaArgumentApprox (t : ℝ) (N : ℕ) : ℝ :=
  (Complex.logGammaSeq (criticalPoint t / 2) N -
    criticalPoint t / 2 * (Real.log Real.pi : ℂ)).im

theorem criticalGammaArgument_error (t : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hNz : 2 * ‖criticalPoint t / 2‖ ≤ (N : ℝ)) :
    |criticalGammaArgument t - criticalGammaArgumentApprox t N| ≤
      (‖criticalPoint t / 2‖ + ‖criticalPoint t / 2‖ ^ 2) / N := by
  have h := gammaLogBranch_error (z := criticalPoint t / 2)
    (by norm_num [criticalPoint, Complex.div_re, Complex.normSq_apply]) hN hNz
  have hi := abs_im_le_norm
    (gammaLogBranch (criticalPoint t / 2) - Complex.logGammaSeq (criticalPoint t / 2) N)
  have he : criticalGammaArgument t - criticalGammaArgumentApprox t N =
      (gammaLogBranch (criticalPoint t / 2) -
        Complex.logGammaSeq (criticalPoint t / 2) N).im := by
    simp only [criticalGammaArgument, criticalGammaArgumentApprox, sub_im]
    ring
  rw [he]
  exact hi.trans h

theorem exp_gammaLogBranch_completed (t : ℝ) :
    Complex.exp (gammaLogBranch (criticalPoint t / 2) -
      criticalPoint t / 2 * (Real.log Real.pi : ℂ)) =
      Gammaℝ (criticalPoint t) := by
  rw [Complex.exp_sub, exp_gammaLogBranch (by norm_num [criticalPoint,
    Complex.div_re, Complex.normSq_apply] : 0 < (criticalPoint t / 2).re),
    Gammaℝ_def, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'),
    Complex.ofReal_log Real.pi_pos.le]
  rw [show log (Real.pi : ℂ) * (-criticalPoint t / 2) =
    -(criticalPoint t / 2 * log (Real.pi : ℂ)) by ring, Complex.exp_neg]
  ring

theorem exp_im_eq_exp_div_norm (w : ℂ) :
    Complex.exp ((w.im : ℂ) * I) = Complex.exp w / (‖Complex.exp w‖ : ℂ) := by
  have he : w = (w.re : ℂ) + (w.im : ℂ) * I := (Complex.re_add_im w).symm
  conv_rhs => rw [he]
  rw [Complex.exp_add]
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, ofReal_re, I_re,
    ofReal_im, I_im, mul_zero, sub_self, Real.exp_zero, mul_one]
  rw [← Complex.ofReal_exp]
  field_simp

theorem criticalGammaPhase_eq_exp_argument (t : ℝ) :
    criticalGammaPhase t = Complex.exp ((criticalGammaArgument t : ℂ) * I) := by
  rw [criticalGammaArgument, exp_im_eq_exp_div_norm, exp_gammaLogBranch_completed]
  rfl

theorem unitPhase_distance_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * I) - Complex.exp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have he : Complex.exp ((a : ℂ) * I) - Complex.exp ((b : ℂ) * I) =
      Complex.exp ((b : ℂ) * I) * (Complex.exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 1
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

theorem criticalGammaPhase_approx_error (t : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hNz : 2 * ‖criticalPoint t / 2‖ ≤ (N : ℝ)) :
    ‖criticalGammaPhase t -
      Complex.exp ((criticalGammaArgumentApprox t N : ℂ) * I)‖ ≤
        (‖criticalPoint t / 2‖ + ‖criticalPoint t / 2‖ ^ 2) / N := by
  rw [criticalGammaPhase_eq_exp_argument]
  exact (unitPhase_distance_le _ _).trans (criticalGammaArgument_error t hN hNz)

#print axioms exp_gammaLogBranch
#print axioms gammaLogBranch_error
#print axioms criticalGammaArgument_error
#print axioms criticalGammaPhase_approx_error

end LiuWang.Proof.Campaign20260915.ZetaValidation
