import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.ConcretePartition

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

def roundDown (n : ℕ) (x : ℝ) : ℝ := (⌊x * 10 ^ n⌋ : ℝ) / 10 ^ n
def roundUp (n : ℕ) (x : ℝ) : ℝ := (⌈x * 10 ^ n⌉ : ℝ) / 10 ^ n

theorem roundDown_le (n : ℕ) (x : ℝ) : roundDown n x ≤ x := by
  unfold roundDown
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 10 ^ n)).mpr
  exact Int.floor_le _

theorem le_roundUp (n : ℕ) (x : ℝ) : x ≤ roundUp n x := by
  unfold roundUp
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ n)).mpr
  exact Int.le_ceil _

def expSeries (x : ℝ) : ℝ := ∑ k ∈ Finset.range 32, (x / 256) ^ k / k.factorial
def expError (x : ℝ) : ℝ := |x / 256| ^ (32 : ℕ) * (33 / ((Nat.factorial 32 : ℝ) * 32))
def expBaseLower (x : ℝ) : ℝ := max 0 (roundDown 40 (expSeries x - expError x))
def expBaseUpper (x : ℝ) : ℝ := roundUp 40 (expSeries x + expError x)
def expLower (x : ℝ) : ℝ := max 0 (roundDown 80 (expBaseLower x ^ (256 : ℕ)))
def expUpper (x : ℝ) : ℝ := roundUp 80 (expBaseUpper x ^ (256 : ℕ))

theorem exp_bounds {x : ℝ} (hx : |x| ≤ 256) :
    expLower x ≤ Real.exp x ∧ Real.exp x ≤ expUpper x := by
  have hs := Real.exp_bound (x := x / 256)
    (by rw [abs_div]; norm_num; linarith) (n := 32) (by norm_num)
  have hs' : |Real.exp (x / 256) - expSeries x| ≤ expError x := by
    simpa only [expSeries, expError, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.cast_ofNat] using hs
  have hb := abs_sub_le_iff.mp hs'
  have hlo : expBaseLower x ≤ Real.exp (x / 256) := by
    apply max_le (Real.exp_pos _).le
    exact (roundDown_le _ _).trans (by linarith [hb.2])
  have hup : Real.exp (x / 256) ≤ expBaseUpper x :=
    (show Real.exp (x / 256) ≤ expSeries x + expError x by linarith [hb.1]).trans
      (le_roundUp _ _)
  have hlo0 : 0 ≤ expBaseLower x := le_max_left _ _
  have hlow := pow_le_pow_left₀ hlo0 hlo 256
  have hupp := pow_le_pow_left₀ (Real.exp_pos _).le hup 256
  have he : Real.exp (x / 256) ^ (256 : ℕ) = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [he] at hlow hupp
  exact ⟨max_le (Real.exp_pos _).le ((roundDown_le _ _).trans hlow),
    hupp.trans (le_roundUp _ _)⟩

theorem expLower_nonneg (x : ℝ) : 0 ≤ expLower x := le_max_left _ _

theorem mul_exp_upper {a x : ℝ} (hx : |x| ≤ 256) :
    a * Real.exp x ≤ a * (if 0 ≤ a then expUpper x else expLower x) := by
  split_ifs with ha
  · exact mul_le_mul_of_nonneg_left (exp_bounds hx).2 ha
  · exact mul_le_mul_of_nonpos_left (exp_bounds hx).1 (le_of_not_ge ha)

theorem mul_exp_lower {a x : ℝ} (hx : |x| ≤ 256) :
    a * (if 0 ≤ a then expLower x else expUpper x) ≤ a * Real.exp x := by
  split_ifs with ha
  · exact mul_le_mul_of_nonneg_left (exp_bounds hx).1 ha
  · exact mul_le_mul_of_nonpos_left (exp_bounds hx).2 (le_of_not_ge ha)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
