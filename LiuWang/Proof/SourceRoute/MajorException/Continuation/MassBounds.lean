import LiuWang.Proof.SourceRoute.MajorException.Continuation.MassTail

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation

def massBudget : MassKind → ℝ
  | .squarefree => 2.82682
  | .all => 3.39102

def rationalMassCertificate (j : MassKind) : ℝ :=
  ((3.141593 : ℝ)^2/6) * correctionHead j / (1-(3/40000 : ℝ))

theorem fixed_head_certificate (j : MassKind) :
    rationalMassCertificate j ≤ massBudget j := by
  cases j <;> norm_num [rationalMassCertificate, correctionHead, zetaCorrection,
    Decimal.oddPrimes_hundred, massBudget]

theorem fixed_head_precision (j : MassKind) :
    correctionHead j ≤
      massBudget j * (1-(3/40000 : ℝ)) * 6 / (3.141593 : ℝ)^2 := by
  have h := fixed_head_certificate j
  dsimp [rationalMassCertificate] at h
  norm_num at h ⊢
  nlinarith

theorem finiteMass_rational_bound (j : MassKind) (X : ℕ) :
    (∑ n ∈ Icc 1 X, massTerm j n) ≤ rationalMassCertificate j := by
  apply (finiteMass_analytic_bound j X).trans
  dsimp [rationalMassCertificate]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_right _ (correctionHead_pos j).le
  have hp := Real.pi_lt_d6
  have hp0 := Real.pi_pos
  nlinarith

theorem mass_bound (j : MassKind) (X : ℕ) :
    (∑ n ∈ Icc 1 X, massTerm j n) ≤ massBudget j :=
  (finiteMass_rational_bound j X).trans (fixed_head_certificate j)

theorem squarefreeTotientMass_bound (X : ℕ) : squarefreeTotientMass X ≤ 2.82682 :=
  mass_bound .squarefree X

theorem totientMass_bound (X : ℕ) : totientMass X ≤ 3.39102 :=
  mass_bound .all X

end LiuWang.Proof.SourceRoute.MajorException.Continuation
