import LiuWang.Proof.SourceRoute.MajorException.Continuation.MassBounds

set_option autoImplicit false
noncomputable section
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation

def roundedHead : MassKind → ℝ
  | .squarefree => 1.7183
  | .all => 2.0613

def certifiedReserve : MassKind → ℝ
  | .squarefree => 0.000245
  | .all => 0.000192

theorem four_decimal_head (j : MassKind) : correctionHead j ≤ roundedHead j := by
  cases j <;> norm_num [correctionHead, zetaCorrection, Decimal.oddPrimes_hundred, roundedHead]

theorem four_decimal_head_suffices (j : MassKind) :
    ((3.141593 : ℝ)^2/6)*roundedHead j/(1-(3/40000 : ℝ)) ≤ massBudget j := by
  cases j <;> norm_num [roundedHead, massBudget]

theorem three_decimal_upward_rounding_insufficient :
    (2.82682 : ℝ) < ((3.141593 : ℝ)^2/6)*1.719/(1-(3/40000 : ℝ)) ∧
    (3.39102 : ℝ) < ((3.141593 : ℝ)^2/6)*2.062/(1-(3/40000 : ℝ)) := by
  norm_num

theorem head_lower_milligrid :
    (1.718 : ℝ) < correctionHead .squarefree ∧
      (2.061 : ℝ) < correctionHead .all := by
  constructor <;> norm_num [correctionHead, zetaCorrection, Decimal.oddPrimes_hundred]

theorem exact_head_reserve (j : MassKind) :
    rationalMassCertificate j + certifiedReserve j ≤ massBudget j := by
  cases j <;> norm_num [rationalMassCertificate, correctionHead, zetaCorrection,
    Decimal.oddPrimes_hundred, massBudget, certifiedReserve]

theorem exact_head_stronger_bounds :
    rationalMassCertificate .squarefree ≤ 2.826575 ∧
      rationalMassCertificate .all ≤ 3.390828 := by
  constructor <;> norm_num [rationalMassCertificate, correctionHead, zetaCorrection,
    Decimal.oddPrimes_hundred]

theorem squarefreeTotientMass_stronger (X : ℕ) : squarefreeTotientMass X ≤ 2.826575 :=
  (finiteMass_rational_bound .squarefree X).trans exact_head_stronger_bounds.1

theorem totientMass_stronger (X : ℕ) : totientMass X ≤ 3.390828 :=
  (finiteMass_rational_bound .all X).trans exact_head_stronger_bounds.2

end LiuWang.Proof.SourceRoute.MajorException.Continuation
