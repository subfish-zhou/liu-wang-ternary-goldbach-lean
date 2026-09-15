import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Continuation.Effective.WindowExtension
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.LittlewoodEntire

/-! The frozen generic Littlewood identity on actual nonprincipal H, with produced family borders.
The horizontal term is retained: no horizontal numerical budget or weighted count is assumed.
-/

set_option autoImplicit false
noncomputable section

open Complex Set MeasureTheory Finset
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
  (horizontalLog rectangle_littlewood_entire rectangle_logs_integrable)

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective

theorem H_zeros_countable {q : ℕ} [NeZero q] {chi : Character q} (hchi : chi ≠ 1)
    {X : ℝ} (hX : 3 < X) : {s : ℂ | H chi X s = 0}.Countable := by
  apply (MeromorphicOn.divisor_support_countable (H chi X) univ).mono
  intro s hs
  rw [Function.mem_support, MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => (differentiable_H hchi X).analyticAt z) (mem_univ s),
    ← Nat.cast_analyticOrderNatAt (analyticOrder_H_ne_top hchi hX s)]
  have ho := ((differentiable_H hchi X).analyticAt s).analyticOrderAt_eq_zero
  rw [← Nat.cast_analyticOrderNatAt (analyticOrder_H_ne_top hchi hX s)] at ho
  simp only [Nat.cast_eq_zero] at ho ⊢
  simpa using ho.not.mpr (not_ne_iff.mpr hs)

theorem family_H_boundary_perturbation (q : ℕ) [NeZero q]
    {X a T eps : ℝ} (hX : 3 < X) (heps : 0 < eps) :
    ∃ a' ∈ Ioo (a - eps) a, ∃ T' ∈ Ioo T (T + eps),
      ∀ chi ∈ nonprincipalCharacters q,
        ∀ s ∈ RectangleBorder ((a' : ℂ) - T' * I) ((2 : ℂ) + T' * I),
          H chi X s ≠ 0 := by
  let Z : Set ℂ := ⋃ chi ∈ (nonprincipalCharacters q : Set (Character q)), {s | H chi X s = 0}
  have hZ : Z.Countable := (nonprincipalCharacters q).finite_toSet.countable.biUnion
    (fun chi hchi => H_zeros_countable ((mem_nonprincipalCharacters chi).mp hchi) hX)
  obtain ⟨a', ha', ha⟩ := ((hZ.image Complex.re).dense_compl ℝ).exists_mem_open
    isOpen_Ioo (nonempty_Ioo.mpr (by linarith : a - eps < a))
  have hbad := (hZ.image Complex.im).union (hZ.image (fun s : ℂ => -s.im))
  obtain ⟨T', hT', hT⟩ := (hbad.dense_compl ℝ).exists_mem_open
    isOpen_Ioo (nonempty_Ioo.mpr (by linarith : T < T + eps))
  refine ⟨a', ha, T', hT, ?_⟩
  intro chi hchi s hs hz
  have hzZ : s ∈ Z := mem_iUnion.mpr ⟨chi, mem_iUnion.mpr ⟨hchi, hz⟩⟩
  have hr : s.re ≠ a' := fun h => ha' ⟨s, hzZ, h⟩
  have hi : s.im ≠ T' := fun h => hT' (Or.inl ⟨s, hzZ, h⟩)
  have hn : s.im ≠ -T' := fun h => hT' (Or.inr ⟨s, hzZ, by linarith⟩)
  have htwo : s.re ≠ 2 := fun h => H_ne_zero_on_two chi h hX hz
  simp [RectangleBorder] at hs
  rcases hs with ((hs | hs) | hs) | hs
  · exact hn hs.2
  · exact hr hs.1
  · exact hi hs.2
  · exact htwo hs.1

def horizontalDifference (q : ℕ) [NeZero q] (X a u : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q,
    ((∫ x in a..2, (horizontalLog (H chi X) 2 u u x).im) -
      (∫ x in a..2, (horizontalLog (H chi X) 2 u (-u) x).im))) / q.totient

def weightedContour (q : ℕ) [NeZero q] (X a u : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q,
    (RectangleIntegral' (fun s => (s - ((a : ℂ) - u * I)) * logDeriv (H chi X) s)
      ((a : ℂ) - u * I) ((2 : ℂ) + u * I)).re) / q.totient

theorem family_littlewood (q : ℕ) [NeZero q] {X a u : ℝ}
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - u * I) ((2 : ℂ) + u * I), H chi X s ≠ 0) :
    2 * Real.pi * weightedContour q X a u =
      logSideDifference q X a u + horizontalDifference q X a u := by
  have hi (chi : Character q) (hchi : chi ∈ nonprincipalCharacters q) :
      2 * Real.pi *
        (RectangleIntegral' (fun s => (s - ((a : ℂ) - u * I)) * logDeriv (H chi X) s)
          ((a : ℂ) - u * I) ((2 : ℂ) + u * I)).re =
        (∫ t in -u..u, (Real.log ‖H chi X ((a : ℂ) + t * I)‖ -
          Real.log ‖H chi X ((2 : ℂ) + t * I)‖)) +
        ((∫ x in a..2, (horizontalLog (H chi X) 2 u u x).im) -
          (∫ x in a..2, (horizontalLog (H chi X) 2 u (-u) x).im)) := by
    have hc := (mem_nonprincipalCharacters chi).mp hchi
    have h := rectangle_littlewood_entire (differentiable_H hc X)
      (a := a) (b := 2) (c := -u) (d := u) (by simpa [sub_eq_add_neg] using hb chi hchi)
    have hir := log_H_vertical_integrable hc X 2 u
    norm_num only [ofReal_ofNat] at hir
    rw [intervalIntegral.integral_sub (log_H_vertical_integrable hc X a u) hir]
    simp only [ofReal_neg, ofReal_ofNat, neg_mul, ← sub_eq_add_neg] at h
    exact h.trans (by ring)
  unfold weightedContour logSideDifference horizontalDifference
  rw [← add_div, ← sum_add_distrib, ← mul_div_assoc, mul_sum]
  exact congrArg (fun r : ℝ => r / q.totient) (sum_congr rfl hi)

theorem family_littlewood_effective (q : ℕ) [NeZero q] {y sigma u : ℝ}
    (hy : 2 ≤ y) (hqy : (q : ℝ) ≤ y) (hs : sigma ∈ Set.Icc (3 / 4) 1) (hu : 0 ≤ u)
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((sigma : ℂ) - u * I) ((2 : ℂ) + u * I), H chi ((q : ℝ) * y) s ≠ 0) :
    2 * Real.pi * weightedContour q ((q : ℝ) * y) sigma u ≤
      (1 + u / y) ^ 3 *
        (169024 * balancedPower q y sigma * (1 + Real.log ((q : ℝ) * y)) ^ 5) +
          horizontalDifference q ((q : ℝ) * y) sigma u := by
  rw [family_littlewood q hb]
  exact add_le_add (logSideDifference_effective_all_heights q hy hqy hs hu) le_rfl

theorem produced_family_littlewood_effective (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {y sigma eps : ℝ} (hy : 2 ≤ y) (hqy : (q : ℝ) ≤ y)
    (hs : sigma ≤ 1) (heps : 0 < eps) (ha : 3 / 4 ≤ sigma - eps) :
    ∃ a ∈ Ioo (sigma - eps) sigma, ∃ u ∈ Ioo y (y + eps),
      (∀ chi ∈ nonprincipalCharacters q,
        ∀ s ∈ RectangleBorder ((a : ℂ) - u * I) ((2 : ℂ) + u * I), H chi ((q : ℝ) * y) s ≠ 0) ∧
      2 * Real.pi * weightedContour q ((q : ℝ) * y) a u ≤
        4563648 * balancedPower q y (sigma - eps) * (1 + Real.log ((q : ℝ) * y)) ^ 5 +
          horizontalDifference q ((q : ℝ) * y) a u := by
  have hqr : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hX : 3 < (q : ℝ) * y := by nlinarith
  obtain ⟨a, ha', u, hu', hb⟩ := family_H_boundary_perturbation q hX heps (a := sigma) (T := y)
  refine ⟨a, ha', u, hu', hb, ?_⟩
  have haI : a ∈ Set.Icc (3 / 4) 1 := ⟨by linarith [ha'.1], by linarith [ha'.2]⟩
  have hu : 0 ≤ u := by linarith [hu'.1]
  have hk : (1 + u / y) ^ 3 ≤ 27 := by
    have hdiv : u / y ≤ 2 := (div_le_iff₀ (by linarith : 0 < y)).mpr (by linarith [hu'.2])
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + u / y)
      (show 1 + u / y ≤ 3 by linarith) 3
    norm_num at h
    exact h
  have hW := balancedPower_antitone (by linarith : (1 : ℝ) ≤ q) (by linarith : 1 ≤ y)
    (by linarith : 0 ≤ sigma - eps) ha'.1.le
  have hL := Real.log_nonneg (show 1 ≤ (q : ℝ) * y by linarith)
  have hcost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW
    (by norm_num : (0 : ℝ) ≤ 169024)) (by positivity : 0 ≤ (1 + Real.log ((q : ℝ) * y)) ^ 5)
  have hnon := (balancedPower_pos (show (0 : ℝ) < q by linarith) (by linarith : 0 < y) a).le
  have h := mul_le_mul hk hcost (by positivity) (by norm_num : (0 : ℝ) ≤ 27)
  exact (family_littlewood_effective q hy hqy haI hu hb).trans
    (add_le_add (h.trans_eq (by ring)) le_rfl)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVEffective
