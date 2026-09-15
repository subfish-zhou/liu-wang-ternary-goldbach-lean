import LiuWang.Proof.Campaign20260915.Totient.RSZeroRegion
import LiuWang.Proof.ChebyshevBound.HighHeight.ZeroTail

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.Totient

def rsPhi (m : ℕ) (L t : ℝ) : ℝ :=
  Real.exp (-(L / (rsR * Real.log t))) / t ^ (m + 1)

def rsHighTerm (K : ℝ) (m : ℕ) (L : ℝ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
  if K < |(riemannXiDivisorZeroValue p).im| then
    Real.exp (((riemannXiDivisorZeroValue p).re - 1) * L) /
      |(riemannXiDivisorZeroValue p).im| ^ (m + 1)
  else 0

theorem rsHighTerm_le_phi {K L : ℝ} (hK : rsA ≤ K) (hL : 0 ≤ L)
    (m : ℕ) (p : RiemannXiDivisorZeroIndex) :
    rsHighTerm K m L p ≤
      if K < |(riemannXiDivisorZeroValue p).im| then
        rsPhi m L |(riemannXiDivisorZeroValue p).im| else 0 := by
  unfold rsHighTerm
  split_ifs with hp
  · have hg := rs_zero_gap p (hK.trans hp.le)
    have hm := mul_le_mul_of_nonneg_right hg.le hL
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hm]
  · exact le_rfl

private theorem power_tail_le {K : ℝ} (hK : 1 ≤ K) (n : ℕ)
    (p : RiemannXiDivisorZeroIndex) :
    (if K < |(riemannXiDivisorZeroValue p).im| then
      1 / |(riemannXiDivisorZeroValue p).im| ^ (n + 2) else 0) ≤
        xiHeightTail K p / K ^ n := by
  unfold xiHeightTail
  split_ifs with hp
  · have ht : 0 < |(riemannXiDivisorZeroValue p).im| := by linarith
    have ht2 : 0 < (riemannXiDivisorZeroValue p).im ^ 2 := by
      simpa only [sq_abs] using sq_pos_of_pos ht
    have hn := pow_le_pow_left₀ (by linarith : 0 ≤ K) hp.le n
    rw [pow_add, sq_abs]
    calc
      _ ≤ 1 / (K ^ n * (riemannXiDivisorZeroValue p).im ^ 2) :=
        one_div_le_one_div_of_le (by positivity) (by gcongr)
      _ = _ := by ring
  · simp

theorem rsHighTerm_summable {K L : ℝ} (hK : rsA ≤ K) (hL : 0 ≤ L)
    {m : ℕ} (hm : 1 ≤ m) :
    Summable (rsHighTerm K m L) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hK2 : 2 ≤ K := by linarith [rsA_ge_thousand]
  apply Summable.of_nonneg_of_le (fun p => by unfold rsHighTerm; split_ifs <;> positivity)
    (f := fun p => xiHeightTail K p / K ^ n)
  · intro p
    have h := power_tail_le (show 1 ≤ K by linarith) n p
    apply le_trans ?_ h
    unfold rsHighTerm
    split_ifs with hp
    · have he : Real.exp (((riemannXiDivisorZeroValue p).re - 1) * L) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (by linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).2]) hL)
      simpa only [Nat.add_comm 1 n, Nat.add_assoc] using
        div_le_div_of_nonneg_right he (by positivity :
          0 ≤ |(riemannXiDivisorZeroValue p).im| ^ (n + 2))
    · exact le_rfl
  · exact (xiHeightTail_summable hK2).div_const _

theorem rsHighTerm_sum_le_power_tail {K L : ℝ} (hK : rsA ≤ K) (hL : 0 ≤ L)
    (n : ℕ) :
    (∑' p, rsHighTerm K (n + 1) L p) ≤ (2 * Real.log K + 2) / K ^ (n + 1) := by
  have hK16 : 16 ≤ K := by linarith [rsA_ge_thousand]
  have hpoint (p : RiemannXiDivisorZeroIndex) :
      rsHighTerm K (n + 1) L p ≤ xiHeightTail K p / K ^ n := by
    apply le_trans ?_ (power_tail_le (by linarith) n p)
    unfold rsHighTerm
    split_ifs with hp
    · have he : Real.exp (((riemannXiDivisorZeroValue p).re - 1) * L) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (by linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).2]) hL)
      exact div_le_div_of_nonneg_right he (by positivity)
    · exact le_rfl
  have hs := (rsHighTerm_summable hK hL (by omega : 1 ≤ n + 1)).tsum_le_tsum
    hpoint ((xiHeightTail_summable (by linarith : 2 ≤ K)).div_const (K ^ n))
  rw [tsum_div_const] at hs
  exact hs.trans ((div_le_div_of_nonneg_right (xiHeightTail_sum_le hK16)
    (by positivity)).trans_eq (by rw [pow_succ]; ring))

theorem rsHighTerm_sum_le_cutoff {K T L : ℝ} (hK : rsA ≤ K) (hKT : K ≤ T)
    (hL : 0 ≤ L) (n : ℕ) :
    (∑' p, rsHighTerm K (n + 1) L p) ≤
      Real.exp (-(L / (rsR * Real.log T))) * ((2 * Real.log K + 2) / K ^ (n + 1)) +
        (2 * Real.log T + 2) / T ^ (n + 1) := by
  let E := Real.exp (-(L / (rsR * Real.log T)))
  have hpoint (p : RiemannXiDivisorZeroIndex) :
      rsHighTerm K (n + 1) L p ≤
        E * rsHighTerm K (n + 1) 0 p + rsHighTerm T (n + 1) L p := by
    by_cases hp : K < |(riemannXiDivisorZeroValue p).im|
    · by_cases ht : T < |(riemannXiDivisorZeroValue p).im|
      · have hnon : 0 ≤ E * rsHighTerm K (n + 1) 0 p := by
          simp only [rsHighTerm, if_pos hp]
          dsimp [E]
          positivity
        simp only [rsHighTerm, if_pos hp, if_pos ht] at hnon ⊢
        linarith
      · have ht' : |(riemannXiDivisorZeroValue p).im| ≤ T := le_of_not_gt ht
        have hγ : 1 < |(riemannXiDivisorZeroValue p).im| := by
          linarith [rsA_ge_thousand.trans (hK.trans hp.le)]
        have hlog := Real.log_le_log (by positivity) ht'
        have hi := one_div_le_one_div_of_le
          (mul_pos rsR_pos (Real.log_pos hγ))
          (mul_le_mul_of_nonneg_left hlog rsR_pos.le)
        have hg := hi.trans (rs_zero_gap p (hK.trans hp.le)).le
        have he : Real.exp (((riemannXiDivisorZeroValue p).re - 1) * L) ≤ E := by
          apply Real.exp_le_exp.mpr
          have hm := mul_le_mul_of_nonneg_right hg hL
          simp only [div_eq_mul_inv] at hm ⊢
          nlinarith only [hm]
        simp only [rsHighTerm, if_pos hp, if_neg ht, mul_zero, Real.exp_zero, add_zero]
        simpa only [mul_one_div] using div_le_div_of_nonneg_right he
          (by positivity : 0 ≤ |(riemannXiDivisorZeroValue p).im| ^ (n + 1 + 1))
    · have ht : ¬ T < |(riemannXiDivisorZeroValue p).im| := by linarith
      simp only [rsHighTerm, if_neg hp, if_neg ht, mul_zero, add_zero, le_refl]
  have hs0 := rsHighTerm_summable hK (by norm_num : (0 : ℝ) ≤ 0) (by omega : 1 ≤ n + 1)
  have hsT := rsHighTerm_summable (hK.trans hKT) hL (by omega : 1 ≤ n + 1)
  have hs := (rsHighTerm_summable hK hL (by omega : 1 ≤ n + 1)).tsum_le_tsum hpoint
    ((hs0.mul_left E).add hsT)
  rw [Summable.tsum_add (hs0.mul_left E) hsT, tsum_mul_left] at hs
  exact hs.trans (add_le_add
    (mul_le_mul_of_nonneg_left (rsHighTerm_sum_le_power_tail hK (by norm_num) n)
      (Real.exp_pos _).le)
    (rsHighTerm_sum_le_power_tail (hK.trans hKT) hL n))

#print axioms rsHighTerm_le_phi
#print axioms rsHighTerm_sum_le_cutoff

end LiuWang.Proof.Campaign20260915.Totient
