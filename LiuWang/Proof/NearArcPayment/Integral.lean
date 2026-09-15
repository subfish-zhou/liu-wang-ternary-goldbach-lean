import LiuWang.Proof.NearArcPayment.Consumer
import LiuWang.Proof.MajorArcApproximation.Interaction

/-!
# Unconditional M2 integral payment

The shell cells are disjoint subsets of the original approximation arcs.
The paid coefficient multiplies E2 only. The remaining fee is an integral
of the actual signed zero packet against the actual quadratic energy.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment

open Interfaces Parameters ArcGeometry CompleteExpansion MinorArcEnergy MajorArcApproximation
open AnalyticNumberTheory.LargeSieve

def shell (N a q : ℕ) : Set ℝ := approximationArc N a q \ M1 N

theorem measurableSet_shell (N a q : ℕ) : MeasurableSet (shell N a q) :=
  measurableSet_Icc.diff (measurableSet_M1 N)

theorem M2_eq_shell_union {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    M2 N = ⋃ i ∈ coreIndices N, shell N i.2 i.1 := by
  ext alpha
  simp only [Set.mem_iUnion, M2, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, a, hq, hi, he, hn⟩
    exact ⟨⟨q, a⟩, (mem_coreIndices hN _).mpr ⟨hq, hi⟩, he, hn⟩
  · rintro ⟨⟨q, a⟩, hi, he, hn⟩
    have hh := (mem_coreIndices hN _).mp hi
    exact ⟨q, a, hh.1, hh.2, he, hn⟩

theorem shell_pairwise_disjoint {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    Set.Pairwise (coreIndices N : Set (Σ _ : ℕ, ℕ)) (fun i j =>
      Disjoint (shell N i.2 i.1) (shell N j.2 j.1)) := by
  intro i hi j hj hij
  have ha := (mem_coreIndices hN i).mp hi
  have hb := (mem_coreIndices hN j).mp hj
  apply (approximationArc_disjoint hN ha.2 hb.2
    (ha.1.trans (sourceP_le_sourceP1 hN)) (hb.1.trans (sourceP_le_sourceP1 hN)) ?_).mono
    Set.sdiff_subset Set.sdiff_subset
  intro he
  apply hij
  have hq := congrArg Prod.snd he
  have haa := congrArg Prod.fst he
  cases i
  cases j
  simp_all

theorem integral_M2_eq_shell_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (f : ℝ → E) (hf : Continuous f) :
    (∫ alpha in M2 N, f alpha) =
      ∑ i ∈ coreIndices N, ∫ alpha in shell N i.2 i.1, f alpha := by
  rw [M2_eq_shell_union hN]
  exact integral_biUnion_finset (coreIndices N) (fun i _ => measurableSet_shell N i.2 i.1)
    (shell_pairwise_disjoint hN) (fun _ _ => hf.integrableOn_Icc.mono_set Set.sdiff_subset)

theorem shell_same_eta {N a q : ℕ} (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) {alpha : ℝ} (ha : alpha ∈ shell N a q) :
    deltaRadius N q < |alpha - rationalCenter a q| ∧
      |alpha - rationalCenter a q| ≤ 1 / ((q : ℝ) * sourceQ N) := by
  refine ⟨?_, (mem_approximationArc_iff N a q alpha).mp ha.1⟩
  apply lt_of_not_ge
  intro hh
  exact ha.2 ⟨q, a, hq, hi, (mem_majorCoreArc_iff N a q alpha).mpr hh⟩

def shellZeroCost (N a q : ℕ) : ℝ :=
  ∫ alpha in shell N a q,
    ‖packet N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2

def weightedPacketCost (N : ℕ) : ℝ :=
  ∑ i ∈ coreIndices N, shellZeroCost N i.2 i.1

theorem shellZeroCost_nonneg (N a q : ℕ) : 0 ≤ shellZeroCost N a q :=
  integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))

theorem weightedPacketCost_nonneg (N : ℕ) : 0 ≤ weightedPacketCost N :=
  Finset.sum_nonneg (fun i _ => shellZeroCost_nonneg N i.2 i.1)

theorem shellZeroCost_eq_values {q : ℕ} [NeZero q] (N a : ℕ)
    (hi : sourceIndex a q) :
    shellZeroCost N a q =
      ∫ alpha in shell N a q,
        ‖(q.totient : ℂ)⁻¹ * ∑ chi : Character q, CharacterExpansion.G a chi *
          ∑ rho ∈ zeroValues chi (sourceT N),
            (analyticOrderNatAt chi.LFunction rho : ℂ) *
              Jrho N rho (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
  unfold shellZeroCost
  simp only [packet_eq, zeroPacket_eq_all_values N a _ hi.2.2, zeroValueSum]

theorem shell_integral_le_paid {N a q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) :
    ‖∫ alpha in shell N a q, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.0781 * (N : ℝ) / sourceL N) * (∫ alpha in shell N a q, ‖S N alpha‖ ^ 2) +
        shellZeroCost N a q := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  let : NeZero q := ⟨Nat.ne_of_gt (sourceIndex_den_pos hi)⟩
  have hf : IntegrableOn (fun alpha => S N alpha ^ 3 * charReal (-(N : ℝ) * alpha))
      (shell N a q) := (continuous_circleKernel N).integrableOn_Icc.mono_set Set.sdiff_subset
  have he : IntegrableOn (fun alpha => ‖S N alpha‖ ^ 2) (shell N a q) :=
    (continuous_energy N).integrableOn_Icc.mono_set Set.sdiff_subset
  have hz : IntegrableOn (fun alpha =>
      ‖packet N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2) (shell N a q) :=
    (((continuous_packet (nat_pos_of_exp_le hN) a q).comp
      (continuous_id.sub continuous_const)).norm.mul
        (continuous_energy N)).integrableOn_Icc.mono_set Set.sdiff_subset
  calc
    _ ≤ ∫ alpha in shell N a q, ‖S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ alpha in shell N a q,
        (0.0781 * (N : ℝ) / sourceL N) * ‖S N alpha‖ ^ 2 +
          ‖packet N a q (alpha - rationalCenter a q)‖ * ‖S N alpha‖ ^ 2 := by
      apply setIntegral_mono_on hf.norm ((he.const_mul _).add hz) (measurableSet_shell N a q)
      intro alpha ha
      obtain ⟨hlo, hhi⟩ := shell_same_eta hq hi ha
      have hb := (S_le_paid_and_packet hN0 hi hq hlo hhi).trans
        (add_le_add (paid_terms_le hN (sourceIndex_den_pos hi) hq) le_rfl)
      rw [show rationalCenter a q + (alpha - rationalCenter a q) = alpha by ring] at hb
      simp only [Pi.add_apply]
      rw [norm_circleKernel, packet_eq]
      have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖S N alpha‖)
      nlinarith
    _ = _ := by rw [integral_add (he.const_mul _) hz, integral_const_mul]; rfl

theorem M2_integral_le_paid_weighted_packet {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.0781 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        weightedPacketCost N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  rw [integral_M2_eq_shell_sum hN0 _ (continuous_circleKernel N)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ coreIndices N,
        ((0.0781 * (N : ℝ) / sourceL N) * (∫ alpha in shell N i.2 i.1, ‖S N alpha‖ ^ 2) +
          shellZeroCost N i.2 i.1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (mem_coreIndices hN0 i).mp hi
      exact shell_integral_le_paid hN hh.1 hh.2
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← integral_M2_eq_shell_sum hN0 _ (continuous_energy N)]
      rfl

theorem M2_integral_le_4012_of_weighted_packet {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hz : weightedPacketCost N ≤
      (0.3231 * (N : ℝ) / sourceL N) * ∫ alpha in M2 N, ‖S N alpha‖ ^ 2) :
    ‖∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)‖ ≤
      (0.4012 * (N : ℝ) / sourceL N) * ∫ alpha in M2 N, ‖S N alpha‖ ^ 2 := by
  have hh := M2_integral_le_paid_weighted_packet hN
  calc
    _ ≤ (0.0781 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) +
        (0.3231 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) :=
      hh.trans (add_le_add le_rfl hz)
    _ = _ := by ring

theorem lambdaTripleCount_ge_M2_paid {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in M1 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M3 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re +
      (∫ alpha in M4 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)).re -
      (0.0781 * (N : ℝ) / sourceL N) * (∫ alpha in M2 N, ‖S N alpha‖ ^ 2) -
      weightedPacketCost N ≤ lambdaTripleCount N := by
  have he := congrArg Complex.re
    (circleIntegral_fourArc (exp_2000_le_of_exp_3100_le hN))
  simp only [Complex.add_re, Complex.ofReal_re] at he
  have hr := Complex.re_le_norm
    (-(∫ alpha in M2 N, S N alpha ^ 3 * charReal (-(N : ℝ) * alpha)))
  simp only [Complex.neg_re, norm_neg] at hr
  have hb := M2_integral_le_paid_weighted_packet hN
  linarith

end LiuWang.Proof.NearArcPayment
