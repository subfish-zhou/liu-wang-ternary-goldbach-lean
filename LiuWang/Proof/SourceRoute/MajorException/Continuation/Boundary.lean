import LiuWang.Proof.SourceRoute.MajorException.Continuation.ConductorMaximum

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation

theorem mass_zero_boundary : squarefreeTotientMass 0 = 0 ∧ totientMass 0 = 0 := by
  simp [squarefreeTotientMass, totientMass]

theorem nonsquarefree_mass_terms_differ :
    massTerm .squarefree 4 = 0 ∧ massTerm .all 4 = 1/4 := by
  have h4 : ¬Squarefree (4 : ℕ) := by decide
  have ht : Nat.totient 4 = 2 := by decide
  norm_num [massTerm, moebiusWeight_eq, h4, ht]

theorem local_factors_two_differ :
    localMass .squarefree 2 = 2 ∧ localMass .all 2 = 7/3 := by
  norm_num [localMass]

theorem nonsquarefree_conductor_pure_cost (j : PureKind) (hj : j ≠ .cubic) :
    paidArithmeticFactor 4 j = 0 := by
  have h4 : ¬Squarefree (4 : ℕ) := by decide
  cases j <;> simp_all [paidArithmeticFactor, moebiusWeight_eq]

theorem positive_unrestricted_prime_power :
    massTerm .all (2^2) > 0 := by
  have ht : Nat.totient 4 = 2 := by decide
  norm_num [massTerm, ht]

theorem paper_domain_lower_corner : paperDomain 987 3100 := by
  norm_num [paperDomain]

theorem original_three_scalar_targets :
    sourceScalarBudget .linear = 0.0000025636 ∧
      sourceScalarBudget .quadratic = 0.00013 ∧ sourceScalarBudget .cubic = 0.028 := by
  norm_num [sourceScalarBudget]

theorem each_critical_point_is_interior (j : PureKind) :
    8 < criticalPoint j ∧ criticalPoint j < 16 :=
  (criticalPoint_spec j).1

theorem all_original_mass_targets (X : ℕ) :
    squarefreeTotientMass X ≤ 2.82682 ∧ totientMass X ≤ 3.39102 :=
  ⟨squarefreeTotientMass_bound X, totientMass_bound X⟩

end LiuWang.Proof.SourceRoute.MajorException.Continuation
