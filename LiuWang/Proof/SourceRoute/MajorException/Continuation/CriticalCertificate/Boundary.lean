import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.Consumer

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate

theorem dyadic_bracket_width (j : PureKind) :
    endpoint j true-endpoint j false = (1/4194304 : ℝ) := by
  cases j <;> norm_num [endpoint]

theorem all_critical_intervals_inside_original (j : PureKind) :
    Set.Icc (endpoint j false) (endpoint j true) ⊆ Set.Ioo (8 : ℝ) 16 := by
  intro t ht
  have h := endpoint_domain j
  exact ⟨h.1.trans_le ht.1, ht.2.trans_lt h.2.2⟩

theorem all_critical_values_strict (j : PureKind) :
    criticalValue j < sourceScalarBudget j := by
  have h := certifiedValue_budget j
  have hv := criticalValue_certified j
  linarith [h.1, h.2]

theorem nonsquarefree_mu_not_replaced :
    muFactor 4 .linear = 0 ∧ muFactor 4 .quadratic = 0 ∧ muFactor 4 .cubic = 1 := by
  have h4 : ¬Squarefree (4 : ℕ) := by decide
  simp [muFactor, moebiusWeight_eq, h4]

theorem stronger_masses_retained :
    paidMassCoefficient .linear = 2.826575 ∧ paidMassCoefficient .quadratic = 2.826575 ∧
      paidMassCoefficient .cubic = 3.390828 := by
  norm_num [paidMassCoefficient]

theorem lower_domain_corner (j : PureKind) :
    conductorScalar j 987 3100 ≤ certifiedValue j :=
  paper_scalar_stronger j (by norm_num [paperDomain])

theorem pure_cost_savings :
    (0.000021+0.00108+0.09403 : ℝ) -
      (pureCostBudget .linear+pureCostBudget .quadratic+pureCostBudget .cubic) = 0.00011511 := by
  norm_num [pureCostBudget]

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate
