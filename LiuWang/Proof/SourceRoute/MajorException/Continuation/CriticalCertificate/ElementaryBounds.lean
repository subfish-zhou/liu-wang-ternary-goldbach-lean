import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.GammaBounds

set_option autoImplicit false
noncomputable section
open Finset

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate

def expPoly (x : ℝ) : ℝ := ∑ i ∈ range 20, x^i/(i.factorial : ℝ)
def expError (x : ℝ) : ℝ := |x|^20*(21/((20 : ℕ).factorial*20 : ℝ))
def logPoly (x : ℝ) : ℝ := ∑ i ∈ range 32, x^(i+1)/(i+1 : ℝ)
def logError (x : ℝ) : ℝ := |x|^33/(1-|x|)

theorem exp_small_bounds {x lo hi : ℝ} (hx : |x| ≤ 1)
    (hl : lo ≤ expPoly x-expError x) (hu : expPoly x+expError x ≤ hi) :
    lo ≤ Real.exp x ∧ Real.exp x ≤ hi := by
  have h := Real.exp_bound hx (show 0 < (20 : ℕ) by norm_num)
  change |Real.exp x-expPoly x| ≤ expError x at h
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

theorem log_scaled_bounds {t lo hi : ℝ} (ht : 0 < t) (hx : |1-t/16| < 1)
    (hl : lo ≤ 4*0.6931471803-logPoly (1-t/16)-logError (1-t/16))
    (hu : 4*0.6931471808-logPoly (1-t/16)+logError (1-t/16) ≤ hi) :
    lo ≤ Real.log t ∧ Real.log t ≤ hi := by
  have h := Real.abs_log_sub_add_sum_range_le hx 32
  change |logPoly (1-t/16)+Real.log (1-(1-t/16))| ≤ logError (1-t/16) at h
  have he : Real.log (1-(1-t/16)) = Real.log t-4*Real.log 2 := by
    rw [show 1-(1-t/16) = t/16 by ring, Real.log_div ht.ne' (by norm_num)]
    rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
    norm_num
  rw [he, abs_le] at h
  constructor <;> linarith [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

theorem exp_nat_scale {x lo hi : ℝ} {m : ℕ} (hl0 : 0 ≤ lo)
    (h : lo ≤ Real.exp x ∧ Real.exp x ≤ hi) :
    lo^m ≤ Real.exp ((m : ℝ)*x) ∧ Real.exp ((m : ℝ)*x) ≤ hi^m := by
  rw [Real.exp_nat_mul]
  exact ⟨pow_le_pow_left₀ hl0 h.1 m, pow_le_pow_left₀ (Real.exp_pos _).le h.2 m⟩

theorem gammaFactor_interval :
    (1.78107239 : ℝ) ≤ gammaFactor ∧ gammaFactor ≤ 1.78107245 := by
  have hlo : (1.78107239 : ℝ) ≤ Real.exp 0.57721565 :=
    (exp_small_bounds (x := 0.57721565) (lo := 1.78107239) (hi := 1.78107245)
      (by norm_num)
      (by norm_num [expPoly, expError, sum_range_succ])
      (by norm_num [expPoly, expError, sum_range_succ])).1
  have hhi : Real.exp (0.57721568 : ℝ) ≤ 1.78107245 :=
    (exp_small_bounds (x := 0.57721568) (lo := 1.78107239) (hi := 1.78107245)
      (by norm_num)
      (by norm_num [expPoly, expError, sum_range_succ])
      (by norm_num [expPoly, expError, sum_range_succ])).2
  exact ⟨hlo.trans (Real.exp_le_exp.mpr eulerGamma_interval.1),
    (Real.exp_le_exp.mpr eulerGamma_interval.2).trans hhi⟩

theorem pi_interval :
    (3.14159265358979323846 : ℝ) ≤ Real.pi ∧ Real.pi ≤ 3.14159265358979323847 :=
  ⟨Real.pi_gt_d20.le, Real.pi_lt_d20.le⟩

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate
