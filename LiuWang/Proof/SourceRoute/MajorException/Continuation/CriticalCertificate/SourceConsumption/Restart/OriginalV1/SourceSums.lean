import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1.PureBounds

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.MajorException
open LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1

def modulusSum (N r : ℕ) (F : (q : ℕ) → [NeZero q] → ℂ) : ℂ :=
  ∑ q ∈ denominators (sourceP N), if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    if r ∣ q then F q else 0

def I15 (N : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  modulusSum N d.modulus (fun q _ => I15arc N q d e)

def I16 (N : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  modulusSum N d.modulus (fun q _ => I16arc N q d e)

def I17 (N : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  modulusSum N d.modulus (fun q _ => I17arc N q d e)

def I18 (N : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  modulusSum N d.modulus (fun q _ => I18arc N q d e)

def I19 (N : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  modulusSum N d.modulus (fun q _ => I19arc N q d e)

def I110 (N : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) : ℂ :=
  modulusSum N d.modulus (fun q _ => I110arc N q d e)

theorem modulusSum_bound {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (r : ℕ)
    (F : (q : ℕ) → [NeZero q] → ℂ) (B : ℕ → ℝ)
    (hF : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → r ∣ q → ‖F q‖ ≤ B q) :
    ‖modulusSum N r F‖ ≤
      ∑ q ∈ denominators (sourceP N), if r ∣ q then B q else 0 := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  have hqs := (mem_denominators (sourceP_pos (exp_2000_le_of_exp_3100_le hN)).le q).mp hq
  have hq0 : q ≠ 0 := by omega
  let : NeZero q := ⟨hq0⟩
  simp only [dif_neg hq0]
  split_ifs with hd
  · exact hF q hqs.2 hd
  · simp only [norm_zero, le_refl]

def lemma2Budget (N q : ℕ) : ℝ :=
  8.2e-10 / sourceL N + 0.063 * q / sourceL N ^ 4

theorem lemma2Budget_pos {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (q : ℕ) :
    0 < lemma2Budget N q := by
  have hl := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  unfold lemma2Budget
  positivity

theorem I16_original_sum {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hlow : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      retainedSum N q (omegaCutoff N q) d e ≤ 8.2e-10 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4) :
    ‖I16 N d e‖ ≤ ∑ q ∈ denominators (sourceP N), if d.modulus ∣ q then
      6 * moebiusWeight q * Real.sqrt d.modulus * Real.sqrt q / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * principalRoot * exceptionalScale N e.re *
          radiusRoot N q * lemma2Budget N q else 0 := by
  apply modulusSum_bound hN
  intro q _ hq hdq
  exact I16_holder hN hd hdq (lemma2Budget_pos hN q)
    (ordinaryMass_le_original hN d e (hlow q hq hdq) (hhigh q hq hdq))

theorem I17_original_sum {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hlow : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      retainedSum N q (omegaCutoff N q) d e ≤ 8.2e-10 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4) :
    ‖I17 N d e‖ ≤ ∑ q ∈ denominators (sourceP N), if d.modulus ∣ q then
      3 * Real.sqrt d.modulus * q / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * exceptionalScale N e.re *
          radiusRoot N q ^ 2 * lemma2Budget N q ^ 2 else 0 := by
  apply modulusSum_bound hN
  intro q _ hq hdq
  exact I17_holder hN hd hdq (lemma2Budget_pos hN q)
    (ordinaryMass_le_original hN d e (hlow q hq hdq) (hhigh q hq hdq))

theorem I19_original_sum {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hlow : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      retainedSum N q (omegaCutoff N q) d e ≤ 8.2e-10 / sourceL N)
    (hhigh : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → d.modulus ∣ q →
      WeightedHighZeros.highSum N q ≤ 0.0126 * q / sourceL N ^ 4) :
    ‖I19 N d e‖ ≤ ∑ q ∈ denominators (sourceP N), if d.modulus ∣ q then
      3 * d.modulus * Real.sqrt q / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * exceptionalScale N e.re ^ 2 *
          radiusRoot N q * lemma2Budget N q else 0 := by
  apply modulusSum_bound hN
  intro q _ hq hdq
  exact I19_holder hN hd hdq (lemma2Budget_pos hN q)
    (ordinaryMass_le_original hN d e (hlow q hq hdq) (hhigh q hq hdq))

theorem I15_original_sum {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    ‖I15 N d e‖ ≤ ∑ q ∈ denominators (sourceP N), if d.modulus ∣ q then
      3 * moebiusWeight q * Real.sqrt d.modulus / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * principalRoot ^ 2 * exceptionalScale N e.re else 0 := by
  apply modulusSum_bound hN
  intro q _ _ hdq
  exact I15_holder_cubic_constants hN hd hdq

theorem I18_original_sum {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    ‖I18 N d e‖ ≤ ∑ q ∈ denominators (sourceP N), if d.modulus ∣ q then
      3 * moebiusWeight q * d.modulus / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * principalRoot * exceptionalScale N e.re ^ 2 else 0 := by
  apply modulusSum_bound hN
  intro q _ _ hdq
  exact I18_holder_cubic_constants hN hd hdq

theorem I110_original_sum {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    ‖I110 N d e‖ ≤ ∑ q ∈ denominators (sourceP N), if d.modulus ∣ q then
      (d.modulus * Real.sqrt d.modulus) / (q.totient : ℝ) ^ 2 *
        (N : ℝ) ^ 2 * exceptionalScale N e.re ^ 3 else 0 := by
  apply modulusSum_bound hN
  intro q _ _ hdq
  exact I110_holder_cubic_constants hN hd hdq

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.OriginalV1
