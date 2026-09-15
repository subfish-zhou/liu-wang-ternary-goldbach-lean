import LiuWang.Proof.Campaign20260915.Density.RightPointFinite

set_option autoImplicit false
noncomputable section

open Finset Complex Filter
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.Campaign20260915.Density

theorem complete_mu_tail_point_energy (q : ℕ) [NeZero q] {X d : ℝ} {s : ℂ}
    (hX : 11 * (q : ℝ) ≤ X) (hd : 0 < d) (hd1 : d ≤ 1) (hs : 1 + d ≤ s.re) :
    (∑ chi : Character q, ‖∑' n : ℕ,
      LSeries.term (twistedMu chi) s (n + ⌈X⌉₊)‖ ^ 2) ≤
      1.1 * X ^ (-2 * d) * (1 + 1 / d) ^ 2 := by
  let S (M : ℕ) := (range M).image (fun n => n + ⌈X⌉₊)
  let a (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX0 : 0 < X := by linarith
  have hN : 0 < ⌈X⌉₊ := Nat.ceil_pos.mpr hX0
  have hse : 1 < s.re := by linarith
  have he (chi : Character q) (M : ℕ) :
      characterPolynomial chi (S M) a =
        ∑ n ∈ range M, LSeries.term (twistedMu chi) s (n + ⌈X⌉₊) := by
    unfold characterPolynomial S
    rw [sum_image (fun _ _ _ _ h => Nat.add_right_cancel h)]
    apply sum_congr rfl
    intro n _
    rw [LSeries.term_of_ne_zero (by omega)]
    dsimp [a, twistedMu]
    ring
  have hlim (chi : Character q) :
      Tendsto (fun M => characterPolynomial chi (S M) a) atTop
        (nhds (∑' n : ℕ, LSeries.term (twistedMu chi) s (n + ⌈X⌉₊))) := by
    have hm : LSeriesSummable (twistedMu chi) s :=
      chi.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hse)
    have ht := (summable_nat_add_iff ⌈X⌉₊).mpr hm
    simpa only [he] using ht.hasSum.tendsto_sum_nat
  have hfam := tendsto_finsetSum (univ : Finset (Character q))
    (fun chi _ => (hlim chi).norm.pow 2)
  apply le_of_tendsto hfam
  apply Eventually.of_forall
  intro M
  apply complete_tail_point_energy q hX hd hd1 hs
  intro n hn
  obtain ⟨k, _, rfl⟩ := mem_image.mp hn
  exact (Nat.le_ceil X).trans (Nat.cast_le.mpr (Nat.le_add_left _ _))

theorem complete_f_point_right (q : ℕ) [NeZero q] {X d : ℝ} {s : ℂ}
    (hX : 11 * (q : ℝ) ≤ X) (hd : 0 < d) (hd1 : d ≤ 1) (hs : 1 + d ≤ s.re) :
    (∑ chi : Character q, ‖NonprincipalDensityAdvance.f chi X s‖ ^ 2) ≤
      1.1 * X ^ (-2 * d) * (1 + 1 / d) ^ 4 := by
  have hse : 1 < s.re := by linarith
  have hL (chi : Character q) : ‖chi.LFunction s‖ ≤ 1 + 1 / d := by
    have hi := one_div_le_one_div_of_le hd (show d ≤ s.re - 1 by linarith)
    linarith [norm_LFunction_le chi hse]
  have hpoint (chi : Character q) :
      ‖NonprincipalDensityAdvance.f chi X s‖ ^ 2 ≤
        (1 + 1 / d) ^ 2 * ‖∑' n : ℕ,
          LSeries.term (twistedMu chi) s (n + ⌈X⌉₊)‖ ^ 2 := by
    rw [f_eq_moebius_tail chi hse X, norm_mul, norm_neg, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hL chi) 2) (sq_nonneg _)
  have h := sum_le_sum (s := (univ : Finset (Character q))) (fun chi _ => hpoint chi)
  rw [← mul_sum] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (complete_mu_tail_point_energy q hX hd hd1 hs)
    (sq_nonneg (1 + 1 / d))).trans_eq (by ring))

end LiuWang.Proof.Campaign20260915.Density
