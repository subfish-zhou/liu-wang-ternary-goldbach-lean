import LiuWang.Proof.SourceRoute.MajorException.Continuation.ConductorMaximum

set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate

def logRational (x : ℝ) : ℝ :=
  x/(1+x) + x/2 - x/(2*(1+x)) + x^2/(12*(1+x)^2) - x^2/12

def logLowerError (x : ℝ) : ℝ := Real.log (1+x) - logRational x
def logUpperError (x : ℝ) : ℝ :=
  logRational x - x^4/(120*(1+x)^4) + x^4/120 - Real.log (1+x)

theorem logLowerError_deriv {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt logLowerError (x^4/(6*(1+x)^3)) x := by
  have h1 : 1+x ≠ 0 := by positivity
  have h := (hasDerivAt_id x).const_add 1
  have h2 : 2*(1+x) ≠ 0 := mul_ne_zero (by norm_num) h1
  have h12 : 12*(1+x)^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 h1)
  have hR := (((((hasDerivAt_id x).div h h1).add
    ((hasDerivAt_id x).div_const 2)).sub
    ((hasDerivAt_id x).div (h.const_mul 2) h2)).add
    (((hasDerivAt_id x).pow 2).div ((h.pow 2).const_mul 12) h12)).sub
    (((hasDerivAt_id x).pow 2).div_const 12)
  apply ((h.log h1).sub hR).congr_deriv
  dsimp
  field_simp
  ring

theorem logUpperError_deriv {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt logUpperError (x^6*(x^2+5*x+5)/(30*(1+x)^5)) x := by
  have h1 : 1+x ≠ 0 := by positivity
  have h := (hasDerivAt_id x).const_add 1
  have hd := ((logLowerError_deriv hx).neg.add
    (((hasDerivAt_id x).pow 4).div_const 120)).sub
    (((hasDerivAt_id x).pow 4).div ((h.pow 4).const_mul 120)
      (mul_ne_zero (by norm_num) (pow_ne_zero 4 h1)))
  have he : logUpperError = fun t =>
      -logLowerError t + t^4/120 - t^4/(120*(1+t)^4) := by
    funext t
    dsimp [logUpperError, logLowerError]
    ring
  rw [he]
  apply hd.congr_deriv
  dsimp
  field_simp
  ring

theorem logRational_bounds {x : ℝ} (hx : 0 ≤ x) :
    logRational x ≤ Real.log (1+x) ∧
      Real.log (1+x) ≤ logRational x - x^4/(120*(1+x)^4) + x^4/120 := by
  have hl : MonotoneOn logLowerError (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t ht
      exact (logLowerError_deriv ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (logLowerError_deriv (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(logLowerError_deriv (interior_subset ht)).deriv]
      have ht0 : 0 ≤ t := interior_subset ht
      positivity
  have hu : MonotoneOn logUpperError (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t ht
      exact (logUpperError_deriv ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (logUpperError_deriv (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(logUpperError_deriv (interior_subset ht)).deriv]
      have ht0 : 0 ≤ t := interior_subset ht
      positivity
  have hlow := hl (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx hx
  have hupp := hu (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx hx
  norm_num [logLowerError, logUpperError, logRational] at hlow hupp
  dsimp [logRational]
  constructor <;> linarith

def gammaUpperSeq (n : ℕ) : ℝ :=
  (harmonic (n+1) : ℝ) - Real.log (n+1) -
    1/(2*(n+1)) + 1/(12*(n+1)^2)

def gammaLowerSeq (n : ℕ) : ℝ :=
  gammaUpperSeq n - 1/(120*(n+1)^4)

theorem gammaUpperSeq_step (n : ℕ) : gammaUpperSeq (n+1) ≤ gammaUpperSeq n := by
  have hn : 0 < (n : ℝ)+1 := by positivity
  have hl := (logRational_bounds (x := 1/((n : ℝ)+1)) (by positivity)).1
  have he : Real.log (1+1/((n : ℝ)+1)) =
      Real.log ((n : ℝ)+2)-Real.log ((n : ℝ)+1) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  rw [he] at hl
  have hd : gammaUpperSeq (n+1)-gammaUpperSeq n =
      logRational (1/((n : ℝ)+1)) -
        (Real.log ((n : ℝ)+2)-Real.log ((n : ℝ)+1)) := by
    dsimp [gammaUpperSeq, logRational]
    rw [harmonic_succ (n+1)]
    push_cast
    simp only [add_assoc, one_add_one_eq_two]
    field_simp
    ring
  linarith

theorem gammaLowerSeq_step (n : ℕ) : gammaLowerSeq n ≤ gammaLowerSeq (n+1) := by
  have hn : 0 < (n : ℝ)+1 := by positivity
  have hl := (logRational_bounds (x := 1/((n : ℝ)+1)) (by positivity)).2
  have he : Real.log (1+1/((n : ℝ)+1)) =
      Real.log ((n : ℝ)+2)-Real.log ((n : ℝ)+1) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  rw [he] at hl
  have hd : gammaLowerSeq (n+1)-gammaLowerSeq n =
      logRational (1/((n : ℝ)+1)) -
        (1/((n : ℝ)+1))^4/(120*(1+1/((n : ℝ)+1))^4) +
        (1/((n : ℝ)+1))^4/120 -
        (Real.log ((n : ℝ)+2)-Real.log ((n : ℝ)+1)) := by
    dsimp [gammaLowerSeq, gammaUpperSeq, logRational]
    rw [harmonic_succ (n+1)]
    push_cast
    simp only [add_assoc, one_add_one_eq_two]
    field_simp
    ring
  nlinarith

theorem gammaUpperSeq_tendsto :
    Tendsto gammaUpperSeq atTop (nhds Real.eulerMascheroniConstant) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
  have hi := tendsto_inv_atTop_zero.comp hn
  have hh := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hc := (hh.sub (hi.const_mul (1/2))).add ((hi.pow 2).const_mul (1/12))
  convert hc using 1
  · funext n
    dsimp [gammaUpperSeq]
    push_cast
    field_simp
  · norm_num

theorem gammaLowerSeq_tendsto :
    Tendsto gammaLowerSeq atTop (nhds Real.eulerMascheroniConstant) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
  have hi := tendsto_inv_atTop_zero.comp hn
  have hc := gammaUpperSeq_tendsto.sub ((hi.pow 4).const_mul (1/120))
  convert hc using 1
  · funext n
    dsimp [gammaLowerSeq]
    field_simp
  · norm_num

theorem gamma_corrected_harmonic (n : ℕ) :
    gammaLowerSeq n ≤ Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant ≤ gammaUpperSeq n :=
  ⟨(monotone_nat_of_le_succ gammaLowerSeq_step).ge_of_tendsto gammaLowerSeq_tendsto n,
    (antitone_nat_of_succ_le gammaUpperSeq_step).le_of_tendsto gammaUpperSeq_tendsto n⟩

theorem eulerGamma_interval :
    (0.57721565 : ℝ) ≤ Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant ≤ 0.57721568 := by
  have h := gamma_corrected_harmonic 31
  have he : Real.log (32 : ℝ) = 5*Real.log 2 := by
    rw [show (32 : ℝ) = 2^5 by norm_num, Real.log_pow]
    norm_num
  norm_num [gammaLowerSeq, gammaUpperSeq] at h
  rw [he] at h
  constructor <;> linarith [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate
