import LiuWang.Proof.MajorArcApproximation.Model

/-! # 原核心弧有限家族与实际 M1 积分 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open MeasureTheory
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ArcGeometry LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.MajorArcApproximation

def numerators (q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)

theorem mem_numerators {a q : ℕ} :
    a ∈ numerators q ↔ sourceIndex a q := by
  simp only [numerators, Finset.mem_filter, Finset.mem_Icc, sourceIndex]
  tauto

def coreIndices (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (denominators (sourceP N)).sigma numerators

theorem mem_coreIndices {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (i : Σ _ : ℕ, ℕ) :
    i ∈ coreIndices N ↔ (i.1 : ℝ) ≤ sourceP N ∧ sourceIndex i.2 i.1 := by
  rw [coreIndices, Finset.mem_sigma, mem_denominators (sourceP_pos hN).le, mem_numerators]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · exact fun h => ⟨⟨h.2.1.trans h.2.2.1, h.1⟩, h.2⟩

theorem M1_eq_core_union {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    M1 N = ⋃ i ∈ coreIndices N, majorCoreArc N i.2 i.1 := by
  ext alpha
  simp only [Set.mem_iUnion, M1, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, a, hq, hi, ha⟩
    exact ⟨⟨q, a⟩, (mem_coreIndices hN _).mpr ⟨hq, hi⟩, ha⟩
  · rintro ⟨⟨q, a⟩, hi, ha⟩
    have hh := (mem_coreIndices hN _).mp hi
    exact ⟨q, a, hh.1, hh.2, ha⟩

theorem core_pairwise_disjoint {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    Set.Pairwise (coreIndices N : Set (Σ _ : ℕ, ℕ)) (fun i j =>
      Disjoint (majorCoreArc N i.2 i.1) (majorCoreArc N j.2 j.1)) := by
  intro i hi j hj hij
  have ha := (mem_coreIndices hN i).mp hi
  have hb := (mem_coreIndices hN j).mp hj
  apply (approximationArc_disjoint hN ha.2 hb.2
    (ha.1.trans (sourceP_le_sourceP1 hN)) (hb.1.trans (sourceP_le_sourceP1 hN)) ?_).mono
    (majorCoreArc_subset_approximationArc hN ha.2) (majorCoreArc_subset_approximationArc hN hb.2)
  intro he
  apply hij
  have hq := congrArg Prod.snd he
  have haa := congrArg Prod.fst he
  cases i
  cases j
  simp_all

theorem integral_M1_eq_sum {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ alpha in M1 N, f alpha) =
      ∑ i ∈ coreIndices N,
        ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
          f (rationalCenter i.2 i.1 + eta) := by
  rw [M1_eq_core_union hN]
  have he := integral_biUnion_finset (μ := volume) (f := f) (s := fun i : Σ _ : ℕ, ℕ =>
    majorCoreArc N i.2 i.1) (coreIndices N) (fun _ _ => measurableSet_Icc)
    (core_pairwise_disjoint hN) (fun _ _ => hf.integrableOn_Icc)
  rw [he]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_majorCoreArc_translate hN ((mem_coreIndices hN i).mp hi).2 f

theorem delta_le {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q) :
    deltaRadius N q ≤ sourceP N / ((q : ℝ) * N) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (nat_pos_of_exp_le hN)
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hP := sourceP_pos hN
  have he : deltaRadius N q = (3.36 / (10 * Real.pi)) * (sourceP N / ((q : ℝ) * N)) := by
    unfold deltaRadius
    ring
  rw [he]
  have hc : (3.36 : ℝ) / (10 * Real.pi) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq (one_mul _)

def totalLength (N : ℕ) : ℝ :=
  ∑ i ∈ coreIndices N, 2 * deltaRadius N i.1

theorem totalLength_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    totalLength N ≤ 2 * sourceP N ^ 2 / (N : ℝ) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (nat_pos_of_exp_le hN)
  have hP := sourceP_pos hN
  unfold totalLength coreIndices
  rw [Finset.sum_sigma]
  calc
    _ ≤ ∑ q ∈ denominators (sourceP N), 2 * sourceP N / (N : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
      have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq0
      have hc : ((numerators q).card : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (Finset.card_filter_le (Finset.Icc 1 q) _).trans_eq
          (by simp)
      simp only [Finset.sum_const, nsmul_eq_mul]
      calc
        _ ≤ (q : ℝ) * (2 * (sourceP N / ((q : ℝ) * N))) :=
          mul_le_mul hc (mul_le_mul_of_nonneg_left (delta_le hN hq0) (by norm_num))
            (by linarith [deltaRadius_pos hN hq0]) (by positivity)
        _ = _ := by field_simp
    _ = ((denominators (sourceP N)).card : ℝ) * (2 * sourceP N / (N : ℝ)) := by simp
    _ ≤ sourceP N * (2 * sourceP N / (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa [denominators] using Nat.floor_le (sourceP_pos hN).le
    _ = _ := by ring

def majorIntegral (N : ℕ) : ℂ :=
  ∫ alpha in M1 N, S N alpha^3 * AnalyticNumberTheory.LargeSieve.charReal (-(N : ℝ)*alpha)

def modelIntegral (N : ℕ) : ℂ :=
  ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
    model N i.2 i.1 eta^3 * arcPhase N i.2 i.1 eta

theorem majorIntegral_eq_sum {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    majorIntegral N =
      ∑ i ∈ coreIndices N, ∫ eta in -deltaRadius N i.1..deltaRadius N i.1,
        S N (rationalCenter i.2 i.1 + eta)^3 * arcPhase N i.2 i.1 eta :=
  integral_M1_eq_sum hN _ (continuous_circleKernel N)

end LiuWang.Proof.MajorArcApproximation
