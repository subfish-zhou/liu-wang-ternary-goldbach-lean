import LiuWang.Proof.ArcGeometry.Main

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Interval
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.ArcGeometry
open AnalyticNumberTheory.LargeSieve

section Unconditional

variable (N a q : Nat) (α : Real) (k : Int)

example (hi : sourceIndex a q) : 0 < q := sourceIndex_den_pos hi

example : α ∈ approximationArc N a q ↔
    |α - rationalCenter a q| ≤ 1 / ((q : Real) * sourceQ N) :=
  mem_approximationArc_iff N a q α

example : α ∈ majorCoreArc N a q ↔
    |α - rationalCenter a q| ≤ deltaRadius N q :=
  mem_majorCoreArc_iff N a q α

example : MeasurableSet (M1 N) := measurableSet_M1 N
example : MeasurableSet (M2 N) := measurableSet_M2 N
example : MeasurableSet (M3 N) := measurableSet_M3 N
example : MeasurableSet (M4 N) := measurableSet_M4 N

example : volume (frontier (sourceDomain N)) = 0 := sourceDomain_frontier_null N

example : Disjoint (M1 N) (M2 N) := disjoint_M1_M2 N

example : Disjoint ((M1 N ∪ M2 N) ∪ M3 N) (M4 N) := disjoint_firstThree_M4 N

example (hα : α ∈ M1 N) :
    ∃ (q a : Nat) (η : Real), (q : Real) ≤ sourceP N ∧ sourceIndex a q ∧
      α = rationalCenter a q + η ∧ |η| ≤ deltaRadius N q :=
  M1_eta_range hα

example (hα : α ∈ M2 N) :
    ∃ (q a : Nat) (η : Real), (q : Real) ≤ sourceP N ∧ sourceIndex a q ∧
      α = rationalCenter a q + η ∧ deltaRadius N q < |η| ∧
      |η| ≤ 1 / ((q : Real) * sourceQ N) :=
  M2_eta_range hα

example (hα : α ∈ M3 N) :
    ∃ (q a : Nat) (η : Real), sourceP N < (q : Real) ∧
      (q : Real) ≤ sourceP1 N ∧ sourceIndex a q ∧
      α = rationalCenter a q + η ∧ |η| ≤ 1 / ((q : Real) * sourceQ N) :=
  M3_eta_range hα

example {Q : Real} (hQ : 1 < Q) (hα : α ∈ Set.Icc (1 / Q) (1 + 1 / Q)) :
    ∃ (q a : Nat), (q : Real) ≤ Q ∧ sourceIndex a q ∧
      |α - rationalCenter a q| ≤ 1 / ((q : Real) * Q) :=
  dirichlet_real_cutoff hQ hα

example : S N (α + k) = S N α := S_add_int N α k

example :
    S N (α + k) ^ 3 * charReal (-(N : Real) * (α + k)) =
      S N α ^ 3 * charReal (-(N : Real) * α) :=
  circleKernel_add_int N α k

example : Function.Periodic (S N) 1 := periodic_S N

example :
    Function.Periodic (fun α : Real => S N α ^ 3 * charReal (-(N : Real) * α)) 1 :=
  periodic_circleKernel N

example : Continuous (fun α : Real => S N α ^ 3 * charReal (-(N : Real) * α)) :=
  continuous_circleKernel N

example :
    (∫ α in sourceDomain N, S N α ^ 3 * charReal (-(N : Real) * α)) =
      (lambdaTripleCount N : Complex) :=
  circleIntegral_sourceDomain N

end Unconditional

section Geometry

variable {N a q b r : Nat} (hN : Real.exp 2000 ≤ (N : Real))

example (hi : sourceIndex a q) :
    majorCoreArc N a q ⊆ approximationArc N a q :=
  majorCoreArc_subset_approximationArc hN hi

example (hi : sourceIndex a q) (hq : (q : Real) ≤ sourceP1 N) :
    approximationArc N a q ⊆ sourceDomain N :=
  approximationArc_subset_sourceDomain hN hi hq

example (ha : sourceIndex a q) (hb : sourceIndex b r)
    (hq : (q : Real) ≤ sourceP1 N) (hr : (r : Real) ≤ sourceP1 N)
    (hne : (a, q) ≠ (b, r)) :
    Disjoint (approximationArc N a q) (approximationArc N b r) :=
  approximationArc_disjoint hN ha hb hq hr hne

example : (frontier (M1 N)).Finite := finite_frontier_M1 hN
example : (frontier (M2 N)).Finite := finite_frontier_M2 hN
example : (frontier (M3 N)).Finite := finite_frontier_M3 hN
example : (frontier (M4 N)).Finite := finite_frontier_M4 hN

example :
    volume (frontier (M1 N)) = 0 ∧ volume (frontier (M2 N)) = 0 ∧
      volume (frontier (M3 N)) = 0 ∧ volume (frontier (M4 N)) = 0 :=
  fourArc_frontier_null hN

example : M1 N ⊆ sourceDomain N := M1_subset_sourceDomain hN
example : M2 N ⊆ sourceDomain N := M2_subset_sourceDomain hN
example : M3 N ⊆ sourceDomain N := M3_subset_sourceDomain hN

example : ((M1 N ∪ M2 N) ∪ M3 N) ∪ M4 N = sourceDomain N := fourArc_cover hN

example : Disjoint (M1 N) (M3 N) := disjoint_M1_M3 hN
example : Disjoint (M2 N) (M3 N) := disjoint_M2_M3 hN

example {α : Real} (hα : α ∈ sourceDomain N) :
    ∃ (q a : Nat), (q : Real) ≤ sourceQ N ∧ sourceIndex a q ∧
      α ∈ approximationArc N a q :=
  sourceDomain_rational_approximation hN hα

example {α : Real} (hα : α ∈ M4 N) :
    ∃ (q a : Nat), sourceP1 N < (q : Real) ∧ (q : Real) ≤ sourceQ N ∧
      sourceIndex a q ∧ α ∈ approximationArc N a q :=
  M4_rational_approximation hN hα

example {α : Real} (hα : α ∈ M4 N) :
    ∃ (q a : Nat) (η : Real), sourceL N ^ 6 ≤ (q : Real) ∧
      (q : Real) ≤ sourceQ N ∧ sourceIndex a q ∧
      α = rationalCenter a q + η ∧ |η| ≤ 1 / ((q : Real) * sourceQ N) :=
  M4_eta_range hN hα

example {f : Real → Complex} (hf : IntegrableOn f (sourceDomain N)) :
    (∫ α in sourceDomain N, f α) =
      (∫ α in M1 N, f α) + (∫ α in M2 N, f α) +
      (∫ α in M3 N, f α) + (∫ α in M4 N, f α) :=
  integral_fourArc hN hf

example (hi : sourceIndex a q) (f : Real → Complex) :
    (∫ α in majorCoreArc N a q, f α) =
      ∫ η in -deltaRadius N q..deltaRadius N q, f (rationalCenter a q + η) :=
  integral_majorCoreArc_translate hN hi f

example :
    (∫ α in M1 N, S N α ^ 3 * charReal (-(N : Real) * α)) +
      (∫ α in M2 N, S N α ^ 3 * charReal (-(N : Real) * α)) +
      (∫ α in M3 N, S N α ^ 3 * charReal (-(N : Real) * α)) +
      (∫ α in M4 N, S N α ^ 3 * charReal (-(N : Real) * α)) =
      (lambdaTripleCount N : Complex) :=
  circleIntegral_fourArc hN

end Geometry

section Endpoints

example :
    ∃ (q a : Nat), (q : Real) ≤ (5 : Real) / 2 ∧ sourceIndex a q ∧
      |(1 + 1 / ((5 : Real) / 2)) - rationalCenter a q| ≤
        1 / ((q : Real) * ((5 : Real) / 2)) :=
  dirichlet_real_cutoff (by norm_num) (by constructor <;> norm_num)

example :
    ∃ (q a : Nat), (q : Real) ≤ (5 : Real) / 2 ∧ sourceIndex a q ∧
      |(1 / ((5 : Real) / 2)) - rationalCenter a q| ≤
        1 / ((q : Real) * ((5 : Real) / 2)) :=
  dirichlet_real_cutoff (by norm_num) (by constructor <;> norm_num)

example {N : Nat} (hN : Real.exp 3100 ≤ (N : Real)) :
    ((M1 N ∪ M2 N) ∪ M3 N) ∪ M4 N = sourceDomain N :=
  fourArc_cover (exp_2000_le_of_exp_3100_le hN)

example {N : Nat} :
    Disjoint (M1 N) (M4 N) ∧ Disjoint (M2 N) (M4 N) ∧ Disjoint (M3 N) (M4 N) := by
  have h := Set.disjoint_union_left.1 (disjoint_firstThree_M4 N)
  exact ⟨(Set.disjoint_union_left.1 h.1).1, (Set.disjoint_union_left.1 h.1).2, h.2⟩

example {N : Nat} (hN : Real.exp 3100 ≤ (N : Real)) :
    (∫ α in M1 N, S N α ^ 3 * charReal (-(N : Real) * α)) +
      (∫ α in M2 N, S N α ^ 3 * charReal (-(N : Real) * α)) +
      (∫ α in M3 N, S N α ^ 3 * charReal (-(N : Real) * α)) +
      (∫ α in M4 N, S N α ^ 3 * charReal (-(N : Real) * α)) =
      ∫ α in (0 : Real)..1, S N α ^ 3 * charReal (-(N : Real) * α) := by
  rw [circleIntegral_fourArc (exp_2000_le_of_exp_3100_le hN),
    circleIntegral_eq_lambdaTripleCount]

end Endpoints
