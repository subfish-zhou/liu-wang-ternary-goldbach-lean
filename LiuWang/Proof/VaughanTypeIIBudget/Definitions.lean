import LiuWang.Proof.VaughanTypeII.Main
import LiuWang.Proof.VaughanTypeI.Main

/-! 第二类有限二进预算的纯标量对象；不声称实际核行满足此预算。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeIIBudget

open Interfaces Parameters VaughanTypeII
open scoped BigOperators

def scalarRowBudget (N : ℕ) (M : ℝ) (q : ℕ) : ℝ :=
  3 * (N : ℝ) / q + 3 * M +
    ((N : ℝ) / M) * (1 + Real.log q) + (q : ℝ) * (1 + Real.log q)

def kappa : ℝ := Real.sqrt ((6111 / 10000) * (31 / 100))

def termA (N q : ℕ) : ℝ :=
  (N : ℝ) * (q : ℝ) ^ ((-1 : ℝ) / 2) * sourceL N ^ (2 : ℕ)

def termB (N : ℕ) : ℝ :=
  (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5)

def termC (N q : ℕ) : ℝ :=
  (N : ℝ) ^ ((1 : ℝ) / 2) * (q : ℝ) ^ ((1 : ℝ) / 2) *
    sourceL N ^ ((5 : ℝ) / 2)

def scalarDyadicBudget (N q : ℕ) : ℝ :=
  kappa * Real.sqrt (N : ℝ) * Real.log ((N : ℝ) / sourceVaughanV N) *
    ∑ j ∈ Finset.range (dyadicCount N), Real.sqrt (scalarRowBudget N (dyadicScale N j) q)

theorem scalarRowBudget_nonneg {N q : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hq : 1 ≤ (q : ℝ)) : 0 ≤ scalarRowBudget N M q := by
  have hlog := Real.log_nonneg hq
  unfold scalarRowBudget
  positivity

theorem terms_nonneg {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (q : ℕ) :
    0 ≤ termA N q ∧ 0 ≤ termB N ∧ 0 ≤ termC N q := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  unfold termA termB termC
  exact ⟨by positivity, by positivity, by positivity⟩

end LiuWang.Proof.VaughanTypeIIBudget
