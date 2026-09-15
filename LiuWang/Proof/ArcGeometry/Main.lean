import LiuWang.Proof.Parameters.Main
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Geometry of the literal Liu--Wang arcs

The sets are those of `Interfaces.Main`, including the closed endpoints and
the removal of the whole of `M1` in `M2`. All geometric parameter estimates
come from `Parameters.Main`. The domain here is the stronger `N ≥ exp 2000`;
in particular no parity restriction or rounding of the real cutoffs is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Interval

namespace LiuWang.Proof.ArcGeometry

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open AnalyticNumberTheory.LargeSieve

theorem sourceIndex_den_pos {a q : Nat} (h : sourceIndex a q) : 0 < q :=
  lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one h.1) h.2.1

theorem mem_approximationArc_iff (N a q : Nat) (α : Real) :
    α ∈ approximationArc N a q ↔
      |α - rationalCenter a q| ≤ 1 / ((q : Real) * sourceQ N) := by
  rw [abs_le]
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem mem_majorCoreArc_iff (N a q : Nat) (α : Real) :
    α ∈ majorCoreArc N a q ↔ |α - rationalCenter a q| ≤ deltaRadius N q := by
  rw [abs_le]
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem majorCoreArc_subset_approximationArc {N a q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hi : sourceIndex a q) :
    majorCoreArc N a q ⊆ approximationArc N a q := by
  intro α hα
  exact (mem_approximationArc_iff N a q α).2
    (((mem_majorCoreArc_iff N a q α).1 hα).trans
      (deltaRadius_le_approximationRadius hN (sourceIndex_den_pos hi)))

theorem approximationArc_subset_sourceDomain {N a q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hi : sourceIndex a q)
    (hq : (q : Real) ≤ sourceP1 N) :
    approximationArc N a q ⊆ sourceDomain N := by
  have hqr : (0 : Real) < q := by exact_mod_cast sourceIndex_den_pos hi
  have hq1 : (1 : Real) ≤ q := by exact_mod_cast sourceIndex_den_pos hi
  have ha1 : (1 : Real) ≤ a := by exact_mod_cast hi.1
  have haq : (a : Real) ≤ q := by exact_mod_cast hi.2.1
  have hQ := sourceQ_pos hN
  have hsum : (q : Real) + 1 ≤ sourceQ N := by
    have := sourceP1_lt_sourceQ_half hN
    linarith
  have hleft : 1 / sourceQ N ≤
      rationalCenter a q - 1 / ((q : Real) * sourceQ N) := by
    apply (le_sub_iff_add_le).2
    calc
      1 / sourceQ N + 1 / ((q : Real) * sourceQ N) =
          (((q : Real) + 1) / sourceQ N) / q := by field_simp
      _ ≤ 1 / (q : Real) :=
        div_le_div_of_nonneg_right ((div_le_one hQ).2 hsum) hqr.le
      _ ≤ rationalCenter a q := div_le_div_of_nonneg_right ha1 hqr.le
  have hright : rationalCenter a q + 1 / ((q : Real) * sourceQ N) ≤
      1 + 1 / sourceQ N := by
    apply add_le_add ((div_le_one hqr).2 haq)
    exact one_div_le_one_div_of_le hQ (by nlinarith)
  intro α hα
  exact ⟨hleft.trans hα.1, hα.2.trans hright⟩

private theorem index_eq_of_cross_eq {a q b r : Nat}
    (ha : sourceIndex a q) (hb : sourceIndex b r) (h : a * r = b * q) :
    a = b ∧ q = r := by
  have hqr : q ∣ r := ha.2.2.symm.dvd_of_dvd_mul_left
    (show q ∣ a * r from ⟨b, by nlinarith [h]⟩)
  have hrq : r ∣ q := hb.2.2.symm.dvd_of_dvd_mul_left
    (show r ∣ b * q from ⟨a, by nlinarith [h]⟩)
  have heq := Nat.dvd_antisymm hqr hrq
  subst r
  exact ⟨Nat.eq_of_mul_eq_mul_right (sourceIndex_den_pos ha) h, rfl⟩

theorem approximationArc_disjoint {N a q b r : Nat}
    (hN : Real.exp 2000 ≤ (N : Real))
    (ha : sourceIndex a q) (hb : sourceIndex b r)
    (hq : (q : Real) ≤ sourceP1 N) (hr : (r : Real) ≤ sourceP1 N)
    (hne : (a, q) ≠ (b, r)) :
    Disjoint (approximationArc N a q) (approximationArc N b r) := by
  have hqr : (0 : Real) < q := by exact_mod_cast sourceIndex_den_pos ha
  have hrr : (0 : Real) < r := by exact_mod_cast sourceIndex_den_pos hb
  have hQ := sourceQ_pos hN
  have hcross : a * r ≠ b * q := by
    intro h
    obtain ⟨rfl, rfl⟩ := index_eq_of_cross_eq ha hb h
    exact hne rfl
  have hgap : (1 : Real) ≤ |(a : Real) * r - (b : Real) * q| := by
    rcases lt_or_gt_of_ne hcross with h | h
    · have hc : (a : Real) * r + 1 ≤ (b : Real) * q := by
        exact_mod_cast Nat.succ_le_of_lt h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hc : (b : Real) * q + 1 ≤ (a : Real) * r := by
        exact_mod_cast Nat.succ_le_of_lt h
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hsep : 1 / ((q : Real) * r) ≤
      |rationalCenter a q - rationalCenter b r| := by
    rw [rationalCenter, rationalCenter, div_sub_div _ _ hqr.ne' hrr.ne',
      abs_div, abs_of_pos (mul_pos hqr hrr)]
    exact div_le_div_of_nonneg_right (by simpa only [mul_comm] using hgap)
      (mul_pos hqr hrr).le
  have hsmall : (q : Real) + r < sourceQ N := by
    have := sourceP1_lt_sourceQ_half hN
    linarith
  have hradii : 1 / ((q : Real) * sourceQ N) + 1 / ((r : Real) * sourceQ N) <
      1 / ((q : Real) * r) := by
    calc
      _ = (((q : Real) + r) / sourceQ N) / ((q : Real) * r) := by
        field_simp; ring
      _ < _ := div_lt_div_of_pos_right ((div_lt_one hQ).2 hsmall) (mul_pos hqr hrr)
  apply Set.disjoint_left.2
  intro α hα hβ
  have h₁ := (mem_approximationArc_iff N a q α).1 hα
  have h₂ := (mem_approximationArc_iff N b r α).1 hβ
  have ht := abs_sub_le (rationalCenter a q) α (rationalCenter b r)
  rw [abs_sub_comm (rationalCenter a q) α] at ht
  linarith

theorem measurableSet_M1 (N : Nat) : MeasurableSet (M1 N) := by
  change MeasurableSet {α | ∃ (q a : Nat), (q : Real) ≤ sourceP N ∧
    sourceIndex a q ∧ α ∈ majorCoreArc N a q}
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter measurableSet_Icc)

theorem measurableSet_M2 (N : Nat) : MeasurableSet (M2 N) := by
  change MeasurableSet {α | ∃ (q a : Nat), (q : Real) ≤ sourceP N ∧
    sourceIndex a q ∧ α ∈ approximationArc N a q ∧ α ∉ M1 N}
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (measurableSet_Icc.inter (measurableSet_M1 N).compl))

theorem measurableSet_M3 (N : Nat) : MeasurableSet (M3 N) := by
  change MeasurableSet {α | ∃ (q a : Nat), sourceP N < (q : Real) ∧
    (q : Real) ≤ sourceP1 N ∧ sourceIndex a q ∧ α ∈ approximationArc N a q}
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter measurableSet_Icc))

theorem measurableSet_M4 (N : Nat) : MeasurableSet (M4 N) :=
  measurableSet_Icc.diff
    (((measurableSet_M1 N).union (measurableSet_M2 N)).union (measurableSet_M3 N))

private theorem finite_frontier_Icc (a b : Real) :
    (frontier (Set.Icc a b)).Finite := by
  by_cases h : a ≤ b
  · rw [frontier_Icc h]
    exact Set.toFinite _
  · simp [Set.Icc_eq_empty_of_lt (lt_of_not_ge h)]

private theorem finite_frontier_union {s t : Set Real}
    (hs : (frontier s).Finite) (ht : (frontier t).Finite) :
    (frontier (s ∪ t)).Finite :=
  (hs.union ht).subset ((frontier_union_subset s t).trans
    (Set.union_subset_union Set.inter_subset_left Set.inter_subset_right))

private theorem finite_frontier_sdiff {s t : Set Real}
    (hs : (frontier s).Finite) (ht : (frontier t).Finite) :
    (frontier (s \ t)).Finite := by
  rw [Set.sdiff_eq]
  apply (hs.union ht).subset
  simpa only [frontier_compl] using (frontier_inter_subset s tᶜ).trans
    (Set.union_subset_union Set.inter_subset_left Set.inter_subset_right)

private theorem finite_frontier_nat_union (m : Nat) (F : Nat → Set Real)
    (hF : ∀ q, (frontier (F q)).Finite) :
    (frontier {α | ∃ q ≤ m, α ∈ F q}).Finite := by
  induction m with
  | zero => simpa using hF 0
  | succ m ih =>
    have heq : {α | ∃ q ≤ m + 1, α ∈ F q} =
        {α | ∃ q ≤ m, α ∈ F q} ∪ F (m + 1) := by
      ext α
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨q, hq, hα⟩
        rcases Nat.le_succ_iff.1 hq with hq | rfl
        · exact Or.inl ⟨q, hq, hα⟩
        · exact Or.inr hα
      · rintro (⟨q, hq, hα⟩ | hα)
        · exact ⟨q, hq.trans (Nat.le_succ _), hα⟩
        · exact ⟨m + 1, le_rfl, hα⟩
    rw [heq]
    exact finite_frontier_union ih (hF _)

private theorem finite_frontier_farey_union {B : Real} (hB : 0 ≤ B)
    (p : Nat → Nat → Prop) (F : Nat → Nat → Set Real)
    (hF : ∀ q a, (frontier (F q a)).Finite) :
    (frontier {α | ∃ (q a : Nat), (q : Real) ≤ B ∧
      sourceIndex a q ∧ p q a ∧ α ∈ F q a}).Finite := by
  classical
  have heq : {α | ∃ (q a : Nat), (q : Real) ≤ B ∧
      sourceIndex a q ∧ p q a ∧ α ∈ F q a} =
      {α | ∃ q ≤ ⌊B⌋₊, α ∈ {α | ∃ a ≤ q,
        α ∈ if sourceIndex a q ∧ p q a then F q a else ∅}} := by
    ext α
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, a, hq, hi, hp, hα⟩
      exact ⟨q, (Nat.le_floor_iff hB).2 hq, a, hi.2.1, by simp [hi, hp, hα]⟩
    · rintro ⟨q, hq, a, _, hα⟩
      split_ifs at hα with hp
      · exact ⟨q, a, (Nat.le_floor_iff hB).1 hq, hp.1, hp.2, hα⟩
      · exact False.elim hα
  rw [heq]
  apply finite_frontier_nat_union
  intro q
  apply finite_frontier_nat_union
  intro a
  split_ifs
  · exact hF q a
  · simp

theorem finite_frontier_M1 {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    (frontier (M1 N)).Finite := by
  simpa only [M1, true_and] using finite_frontier_farey_union (sourceP_pos hN).le
    (fun _ _ => True) (fun q a => majorCoreArc N a q)
    (fun q a => finite_frontier_Icc _ _)

theorem finite_frontier_M2 {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    (frontier (M2 N)).Finite := by
  have heq : M2 N = {α | ∃ (q a : Nat), (q : Real) ≤ sourceP N ∧
      sourceIndex a q ∧ True ∧ α ∈ approximationArc N a q} \ M1 N := by
    ext α
    simp only [M2, Set.mem_ofPred_eq, Set.mem_sdiff, true_and]
    constructor
    · rintro ⟨q, a, hq, hi, hα, hn⟩
      exact ⟨⟨q, a, hq, hi, hα⟩, hn⟩
    · rintro ⟨⟨q, a, hq, hi, hα⟩, hn⟩
      exact ⟨q, a, hq, hi, hα, hn⟩
  rw [heq]
  exact finite_frontier_sdiff
    (finite_frontier_farey_union (sourceP_pos hN).le (fun _ _ => True)
      (fun q a => approximationArc N a q) (fun q a => finite_frontier_Icc _ _))
    (finite_frontier_M1 hN)

theorem finite_frontier_M3 {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    (frontier (M3 N)).Finite := by
  have heq : M3 N = {α | ∃ (q a : Nat), (q : Real) ≤ sourceP1 N ∧
      sourceIndex a q ∧ sourceP N < (q : Real) ∧ α ∈ approximationArc N a q} := by
    ext α
    simp only [M3, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, a, hP, hq, hi, hα⟩
      exact ⟨q, a, hq, hi, hP, hα⟩
    · rintro ⟨q, a, hq, hi, hP, hα⟩
      exact ⟨q, a, hP, hq, hi, hα⟩
  rw [heq]
  exact finite_frontier_farey_union (sourceP1_pos hN).le
    (fun q _ => sourceP N < (q : Real))
    (fun q a => approximationArc N a q) (fun q a => finite_frontier_Icc _ _)

theorem finite_frontier_M4 {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    (frontier (M4 N)).Finite :=
  finite_frontier_sdiff (finite_frontier_Icc _ _)
    (finite_frontier_union
      (finite_frontier_union (finite_frontier_M1 hN) (finite_frontier_M2 hN))
      (finite_frontier_M3 hN))

theorem fourArc_frontier_null {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    volume (frontier (M1 N)) = 0 ∧ volume (frontier (M2 N)) = 0 ∧
      volume (frontier (M3 N)) = 0 ∧ volume (frontier (M4 N)) = 0 :=
  ⟨(finite_frontier_M1 hN).measure_zero volume, (finite_frontier_M2 hN).measure_zero volume,
    (finite_frontier_M3 hN).measure_zero volume, (finite_frontier_M4 hN).measure_zero volume⟩

theorem sourceDomain_frontier_null (N : Nat) :
    volume (frontier (sourceDomain N)) = 0 :=
  (finite_frontier_Icc _ _).measure_zero volume

theorem M1_subset_sourceDomain {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    M1 N ⊆ sourceDomain N := by
  rintro α ⟨q, a, hq, hi, hα⟩
  exact approximationArc_subset_sourceDomain hN hi (hq.trans (sourceP_le_sourceP1 hN))
    (majorCoreArc_subset_approximationArc hN hi hα)

theorem M2_subset_sourceDomain {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    M2 N ⊆ sourceDomain N := by
  rintro α ⟨q, a, hq, hi, hα, _⟩
  exact approximationArc_subset_sourceDomain hN hi (hq.trans (sourceP_le_sourceP1 hN)) hα

theorem M3_subset_sourceDomain {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    M3 N ⊆ sourceDomain N := by
  rintro α ⟨q, a, _, hq, hi, hα⟩
  exact approximationArc_subset_sourceDomain hN hi hq hα

theorem fourArc_cover {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    ((M1 N ∪ M2 N) ∪ M3 N) ∪ M4 N = sourceDomain N := by
  have hsub : (M1 N ∪ M2 N) ∪ M3 N ⊆ sourceDomain N :=
    Set.union_subset (Set.union_subset (M1_subset_sourceDomain hN)
      (M2_subset_sourceDomain hN)) (M3_subset_sourceDomain hN)
  exact Set.union_sdiff_cancel hsub

theorem disjoint_M1_M2 (N : Nat) : Disjoint (M1 N) (M2 N) := by
  apply Set.disjoint_left.2
  rintro α h₁ ⟨q, a, _, _, _, h₂⟩
  exact h₂ h₁

theorem disjoint_M1_M3 {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    Disjoint (M1 N) (M3 N) := by
  apply Set.disjoint_left.2
  rintro α ⟨q, a, hq, ha, hα⟩ ⟨r, b, hr, hr₁, hb, hβ⟩
  have hne : (a, q) ≠ (b, r) := by
    rintro ⟨⟩
    exact (not_lt_of_ge hq) hr
  exact (Set.disjoint_left.1 (approximationArc_disjoint hN ha hb
    (hq.trans (sourceP_le_sourceP1 hN)) hr₁ hne))
    (majorCoreArc_subset_approximationArc hN ha hα) hβ

theorem disjoint_M2_M3 {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    Disjoint (M2 N) (M3 N) := by
  apply Set.disjoint_left.2
  rintro α ⟨q, a, hq, ha, hα, _⟩ ⟨r, b, hr, hr₁, hb, hβ⟩
  have hne : (a, q) ≠ (b, r) := by
    rintro ⟨⟩
    exact (not_lt_of_ge hq) hr
  exact (Set.disjoint_left.1 (approximationArc_disjoint hN ha hb
    (hq.trans (sourceP_le_sourceP1 hN)) hr₁ hne)) hα hβ

theorem disjoint_firstThree_M4 (N : Nat) :
    Disjoint ((M1 N ∪ M2 N) ∪ M3 N) (M4 N) :=
  Set.disjoint_left.2 fun _ h₁ h₂ => h₂.2 h₁

theorem M1_eta_range {N : Nat} {α : Real} (hα : α ∈ M1 N) :
    ∃ (q a : Nat) (η : Real), (q : Real) ≤ sourceP N ∧ sourceIndex a q ∧
      α = rationalCenter a q + η ∧ |η| ≤ deltaRadius N q := by
  obtain ⟨q, a, hq, hi, hcore⟩ := hα
  exact ⟨q, a, α - rationalCenter a q, hq, hi, by ring,
    (mem_majorCoreArc_iff N a q α).1 hcore⟩

theorem M2_eta_range {N : Nat} {α : Real} (hα : α ∈ M2 N) :
    ∃ (q a : Nat) (η : Real), (q : Real) ≤ sourceP N ∧ sourceIndex a q ∧
      α = rationalCenter a q + η ∧ deltaRadius N q < |η| ∧
      |η| ≤ 1 / ((q : Real) * sourceQ N) := by
  obtain ⟨q, a, hq, hi, happrox, hn⟩ := hα
  refine ⟨q, a, α - rationalCenter a q, hq, hi, by ring, ?_,
    (mem_approximationArc_iff N a q α).1 happrox⟩
  apply lt_of_not_ge
  intro h
  exact hn ⟨q, a, hq, hi, (mem_majorCoreArc_iff N a q α).2 h⟩

theorem M3_eta_range {N : Nat} {α : Real} (hα : α ∈ M3 N) :
    ∃ (q a : Nat) (η : Real), sourceP N < (q : Real) ∧
      (q : Real) ≤ sourceP1 N ∧ sourceIndex a q ∧
      α = rationalCenter a q + η ∧ |η| ≤ 1 / ((q : Real) * sourceQ N) := by
  obtain ⟨q, a, hqP, hq, hi, happrox⟩ := hα
  exact ⟨q, a, α - rationalCenter a q, hqP, hq, hi, by ring,
    (mem_approximationArc_iff N a q α).1 happrox⟩

/-- The `floor Q + 1` form of Dirichlet's lemma preserves the real cutoff.
The part above `1`, including the closed right endpoint, uses `a = q = 1`. -/
theorem dirichlet_real_cutoff {Q α : Real} (hQ : 1 < Q)
    (hα : α ∈ Set.Icc (1 / Q) (1 + 1 / Q)) :
    ∃ (q a : Nat), (q : Real) ≤ Q ∧ sourceIndex a q ∧
      |α - rationalCenter a q| ≤ 1 / ((q : Real) * Q) := by
  have hQ0 : 0 < Q := by linarith
  by_cases hα1 : 1 ≤ α
  · refine ⟨1, 1, by simpa using hQ.le, by norm_num [sourceIndex], ?_⟩
    simp only [rationalCenter, Nat.cast_one, div_one, one_mul]
    rw [abs_of_nonneg (by linarith)]
    linarith [hα.2]
  have hfloor : 0 < ⌊Q⌋₊ :=
    lt_of_lt_of_le Nat.zero_lt_one ((Nat.le_floor_iff hQ0.le).2 (by simpa using hQ.le))
  obtain ⟨r, herr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hfloor
  have hd : (0 : Real) < r.den := by exact_mod_cast r.pos
  have hd1 : (1 : Real) ≤ r.den := by exact_mod_cast r.pos
  have hdenQ : (r.den : Real) ≤ Q :=
    (by exact_mod_cast hden : (r.den : Real) ≤ ⌊Q⌋₊).trans (Nat.floor_le hQ0.le)
  have hstrict : |α - (r : Real)| < 1 / ((r.den : Real) * Q) :=
    herr.trans_lt (one_div_lt_one_div_of_lt (mul_pos hd hQ0) (by
      have := Nat.lt_floor_add_one Q
      nlinarith))
  have hrpos : (0 : Real) < r := by
    have hrad : 1 / ((r.den : Real) * Q) ≤ 1 / Q :=
      one_div_le_one_div_of_le hQ0 (by nlinarith)
    have := (abs_lt.1 hstrict).2
    linarith [hα.1]
  have hnumpos : 0 < r.num := Rat.num_pos.2 (by exact_mod_cast hrpos)
  have hnumcast : (r.num : Real) = (r : Real) * r.den := by
    rw [Rat.cast_def, div_mul_cancel₀ _ hd.ne']
  have hnumle : r.num ≤ (r.den : Int) := by
    by_contra hn
    have hn' : (r.den : Real) + 1 ≤ r.num := by
      exact_mod_cast (show (r.den : Int) + 1 ≤ r.num by omega)
    have hrad : 1 / ((r.den : Real) * Q) < 1 / r.den :=
      one_div_lt_one_div_of_lt hd (by nlinarith)
    have hrα : (r : Real) - α < 1 / r.den := by
      have := (abs_lt.1 hstrict).1
      linarith
    have hmul := (lt_div_iff₀ hd).1 hrα
    nlinarith
  have habs : (r.num.natAbs : Real) = r.num := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : Int => (z : Real)) (Int.natAbs_of_nonneg hnumpos.le)
  have hacenter : rationalCenter r.num.natAbs r.den = (r : Real) := by
    rw [rationalCenter, habs, Rat.cast_def]
  refine ⟨r.den, r.num.natAbs, hdenQ, ⟨?_, ?_, r.reduced⟩, ?_⟩
  · have : (0 : Real) < r.num.natAbs := by rw [habs]; exact_mod_cast hnumpos
    exact Nat.succ_le_of_lt (by exact_mod_cast this)
  · have : (r.num.natAbs : Real) ≤ r.den := by rw [habs]; exact_mod_cast hnumle
    exact_mod_cast this
  · rw [hacenter]
    exact hstrict.le

theorem sourceDomain_rational_approximation {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) {α : Real} (hα : α ∈ sourceDomain N) :
    ∃ (q a : Nat), (q : Real) ≤ sourceQ N ∧ sourceIndex a q ∧
      α ∈ approximationArc N a q := by
  obtain ⟨q, a, hq, hi, happrox⟩ :=
    dirichlet_real_cutoff (by linarith [two_lt_sourceQ hN]) hα
  exact ⟨q, a, hq, hi, (mem_approximationArc_iff N a q α).2 happrox⟩

theorem M4_rational_approximation {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) {α : Real} (hα : α ∈ M4 N) :
    ∃ (q a : Nat), sourceP1 N < (q : Real) ∧ (q : Real) ≤ sourceQ N ∧
      sourceIndex a q ∧ α ∈ approximationArc N a q := by
  obtain ⟨q, a, hq, hi, happrox⟩ := sourceDomain_rational_approximation hN hα.1
  refine ⟨q, a, ?_, hq, hi, happrox⟩
  by_contra h
  have hq₁ : (q : Real) ≤ sourceP1 N := le_of_not_gt h
  apply hα.2
  by_cases hqP : (q : Real) ≤ sourceP N
  · exact Or.inl (Or.inr ⟨q, a, hqP, hi, happrox,
      fun h₁ => hα.2 (Or.inl (Or.inl h₁))⟩)
  · exact Or.inr ⟨q, a, lt_of_not_ge hqP, hq₁, hi, happrox⟩

theorem M4_eta_range {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) {α : Real} (hα : α ∈ M4 N) :
    ∃ (q a : Nat) (η : Real), sourceL N ^ 6 ≤ (q : Real) ∧
      (q : Real) ≤ sourceQ N ∧ sourceIndex a q ∧
      α = rationalCenter a q + η ∧ |η| ≤ 1 / ((q : Real) * sourceQ N) := by
  obtain ⟨q, a, hq₁, hq, hi, happrox⟩ := M4_rational_approximation hN hα
  exact ⟨q, a, α - rationalCenter a q, hq₁.le, hq, hi, by ring,
    (mem_approximationArc_iff N a q α).1 happrox⟩

theorem integral_fourArc {N : Nat} (hN : Real.exp 2000 ≤ (N : Real))
    {f : Real → Complex} (hf : IntegrableOn f (sourceDomain N)) :
    (∫ α in sourceDomain N, f α) =
      (∫ α in M1 N, f α) + (∫ α in M2 N, f α) +
      (∫ α in M3 N, f α) + (∫ α in M4 N, f α) := by
  have h₁ := hf.mono_set (M1_subset_sourceDomain hN)
  have h₂ := hf.mono_set (M2_subset_sourceDomain hN)
  have h₃ := hf.mono_set (M3_subset_sourceDomain hN)
  have h₄ := hf.mono_set (show M4 N ⊆ sourceDomain N from Set.sdiff_subset)
  conv_lhs => rw [← fourArc_cover hN]
  rw [setIntegral_union (disjoint_firstThree_M4 N) (measurableSet_M4 N)
      ((h₁.union h₂).union h₃) h₄,
    setIntegral_union (Set.disjoint_union_left.2 ⟨disjoint_M1_M3 hN, disjoint_M2_M3 hN⟩)
      (measurableSet_M3 N) (h₁.union h₂) h₃,
    setIntegral_union (disjoint_M1_M2 N) (measurableSet_M2 N) h₁ h₂]

theorem S_add_int (N : Nat) (α : Real) (k : Int) : S N (α + k) = S N α := by
  unfold S LiuWang.Fourier.liuWangExpSum LiuWang.Fourier.indexedExpSum
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  rw [mul_add]
  convert charReal_periodic_int ((n : Real) * α) ((n : Int) * k) using 1 <;> push_cast <;> rfl

theorem circleKernel_add_int (N : Nat) (α : Real) (k : Int) :
    S N (α + k) ^ 3 * charReal (-(N : Real) * (α + k)) =
      S N α ^ 3 * charReal (-(N : Real) * α) := by
  rw [S_add_int, mul_add]
  congr 1
  convert charReal_periodic_int (-(N : Real) * α) (-(N : Int) * k) using 1
  push_cast
  rfl

theorem periodic_S (N : Nat) : Function.Periodic (S N) 1 := by
  intro α
  simpa using S_add_int N α 1

theorem periodic_circleKernel (N : Nat) :
    Function.Periodic (fun α : Real => S N α ^ 3 * charReal (-(N : Real) * α)) 1 := by
  intro α
  simpa using circleKernel_add_int N α 1

theorem integral_majorCoreArc_translate {N a q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hi : sourceIndex a q) (f : Real → Complex) :
    (∫ α in majorCoreArc N a q, f α) =
      ∫ η in -deltaRadius N q..deltaRadius N q, f (rationalCenter a q + η) := by
  have hd := (deltaRadius_pos hN (sourceIndex_den_pos hi)).le
  rw [majorCoreArc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show
      rationalCenter a q - deltaRadius N q ≤ rationalCenter a q + deltaRadius N q by linarith)]
  simpa only [add_comm, sub_eq_add_neg] using
    (intervalIntegral.integral_comp_add_right f (rationalCenter a q)
      (a := -deltaRadius N q) (b := deltaRadius N q)).symm

theorem continuous_circleKernel (N : Nat) :
    Continuous (fun α : Real => S N α ^ 3 * charReal (-(N : Real) * α)) := by
  unfold S LiuWang.Fourier.liuWangExpSum LiuWang.Fourier.indexedExpSum charReal
  fun_prop

theorem circleIntegral_sourceDomain (N : Nat) :
    (∫ α in sourceDomain N, S N α ^ 3 * charReal (-(N : Real) * α)) =
      (lambdaTripleCount N : Complex) := by
  rw [sourceDomain, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show 1 / sourceQ N ≤ 1 + 1 / sourceQ N by linarith)]
  simpa only [add_comm] using LiuWang.Fourier.integral_liuWangExpSum_cube N (1 / sourceQ N)

theorem circleIntegral_fourArc {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    (∫ α in M1 N, S N α ^ 3 * charReal (-(N : Real) * α)) +
      (∫ α in M2 N, S N α ^ 3 * charReal (-(N : Real) * α)) +
      (∫ α in M3 N, S N α ^ 3 * charReal (-(N : Real) * α)) +
      (∫ α in M4 N, S N α ^ 3 * charReal (-(N : Real) * α)) =
      (lambdaTripleCount N : Complex) := by
  rw [← integral_fourArc hN ((continuous_circleKernel N).integrableOn_Icc)]
  exact circleIntegral_sourceDomain N

end LiuWang.Proof.ArcGeometry
