import LiuWang.Proof.Campaign20260915.Totient.RSCountPhi
import LiuWang.Proof.Campaign20260915.ZetaMomentTransport.Multiplicity
import LiuWang.Proof.DirichletZeroCount.Applications.Coarse
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter Set
open scoped Topology
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.ZetaMomentTransport
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.Campaign20260915.Totient

def rsPositivePhiTerm (K : ℝ) (m : ℕ) (L : ℝ)
    (p : RiemannXiDivisorZeroIndex) : ℝ :=
  if K < (riemannXiDivisorZeroValue p).im then
    rsPhi m L (riemannXiDivisorZeroValue p).im else 0

theorem rsPositivePhiTerm_nonneg {K : ℝ} (hK : 0 ≤ K) (m : ℕ) (L : ℝ)
    (p : RiemannXiDivisorZeroIndex) : 0 ≤ rsPositivePhiTerm K m L p := by
  unfold rsPositivePhiTerm
  split_ifs with hp
  · exact (rsPhi_pos m L (hK.trans_lt hp)).le
  · rfl

theorem rsPositivePhiTerm_summable {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m) :
    Summable (rsPositivePhiTerm K m L) := by
  have hK1 : 1 < K := by linarith [rsA_ge_thousand]
  apply Summable.of_nonneg_of_le (rsPositivePhiTerm_nonneg (by linarith) m L)
    (f := rsHighTerm K m 0) _ (rsHighTerm_summable hK le_rfl hm)
  intro p
  unfold rsPositivePhiTerm
  split_ifs with hp
  · have hg : 0 < (riemannXiDivisorZeroValue p).im := by linarith
    simpa [rsHighTerm, abs_of_pos hg, hp] using rsPhi_le_power m hL (hK1.trans hp)
  · unfold rsHighTerm
    split_ifs <;> positivity

theorem rs_positiveCount_coarse {t : ℝ} (ht : 10000 ≤ t) :
    (positiveCount t : ℝ) ≤ 10 * t * Real.log t := by
  have he := zetaClosedCount_eq_two_positiveCount t
  rw [zetaClosedCount_eq_principal] at he
  have hc := (count_principal_le 1 0 (by linarith : 0 ≤ t)).trans
    (Applications.principalBound_le_ten (q := 1) ht)
  norm_num only [Nat.cast_one, one_mul] at hc
  rw [he] at hc
  push_cast at hc
  linarith [Nat.cast_nonneg (positiveCount t) (α := ℝ)]

theorem rs_positiveCount_phi_tendsto {L : ℝ} {m : ℕ} (hL : 0 ≤ L) (hm : 1 ≤ m) :
    Tendsto (fun t => (positiveCount t : ℝ) * rsPhi m L t) atTop (𝓝 0) := by
  have hb : Tendsto (fun t : ℝ => 10 * (Real.log t / t)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul 10
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_ge_atTop (10000 : ℝ)] with t ht
    exact mul_nonneg (Nat.cast_nonneg _) (rsPhi_pos m L (by linarith)).le
  · filter_upwards [eventually_ge_atTop (10000 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hp : t ^ 2 ≤ t ^ (m + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hphi : rsPhi m L t ≤ 1 / t ^ 2 :=
      (rsPhi_le_power m hL (by linarith)).trans
        (one_div_le_one_div_of_le (by positivity) hp)
    calc
      _ ≤ (10 * t * Real.log t) * (1 / t ^ 2) :=
        mul_le_mul (rs_positiveCount_coarse ht) hphi
          (rsPhi_pos m L ht0).le (by
            have hl := Real.log_pos (by linarith : 1 < t)
            positivity)
      _ = _ := by field_simp

theorem rs_positiveWindow_phi_tendsto {K L : ℝ} {m : ℕ}
    (hK : rsA ≤ K) (hL : 0 ≤ L) (hm : 1 ≤ m) :
    Tendsto (rsPositiveWindowSum (rsPhi m L) K) atTop
      (𝓝 (∑' p, rsPositivePhiTerm K m L p)) := by
  classical
  have hK0 : 0 < K := by linarith [rsA_ge_thousand]
  let f (T : ℝ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
    if |(riemannXiDivisorZeroValue p).im| ≤ T then rsPositivePhiTerm K m L p else 0
  have hlim : Tendsto (fun T => ∑' p, f T p) atTop
      (𝓝 (∑' p, rsPositivePhiTerm K m L p)) := by
    apply tendsto_tsum_of_dominated_convergence (rsPositivePhiTerm_summable hK hL hm)
    · intro p
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop |(riemannXiDivisorZeroValue p).im|] with T hT
      simp [f, hT]
    · apply Filter.Eventually.of_forall
      intro T p
      have hn := rsPositivePhiTerm_nonneg hK0.le m L p
      dsimp [f]
      split_ifs
      · simp only [abs_of_nonneg hn, le_refl]
      · simpa only [abs_zero] using hn
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro T
  dsimp only
  rw [tsum_eq_sum (s := xiWindow 0 T) (by
    intro p hp
    have hn : ¬ |(riemannXiDivisorZeroValue p).im| ≤ T := by
      simpa only [mem_xiWindow, sub_zero] using hp
    simp [f, hn])]
  have he :
      (∑ p ∈ xiWindow 0 T, f T p) =
      ∑ p ∈ xiWindow 0 T, if K < (riemannXiDivisorZeroValue p).im then
        rsPhi m L (riemannXiDivisorZeroValue p).im else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : |(riemannXiDivisorZeroValue p).im| ≤ T := by
      simpa only [mem_xiWindow, sub_zero] using hp
    simp [f, hp', rsPositivePhiTerm]
  rw [he, sum_xiWindow_eq_zeta T (fun z => if K < z.im then rsPhi m L z.im else 0)]
  simp only [rsPositiveWindowSum, positiveValues, Finset.sum_filter, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hp : K < z.im
  · simp [hp, hK0.trans hp]
  · simp [hp]

#print axioms rsPositivePhiTerm_nonneg
#print axioms rsPositivePhiTerm_summable
#print axioms rs_positiveCount_coarse
#print axioms rs_positiveCount_phi_tendsto
#print axioms rs_positiveWindow_phi_tendsto

end LiuWang.Proof.Campaign20260915.Totient
