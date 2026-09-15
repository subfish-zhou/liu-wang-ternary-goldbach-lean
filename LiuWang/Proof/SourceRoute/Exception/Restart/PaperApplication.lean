import LiuWang.Proof.SourceRoute.Exception.Restart.Family
import LiuWang.Proof.WeightedLowZeros.Continuation.PaperSource

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros.Continuation
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.SourceRoute.Exception.Restart

theorem paper_source_original_zero_iff {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log (sourceP N)) ≤ rho.re)
    (ht : |rho.im| ≤ sourceP N / q) (hpole : chi ≠ 1 ∨ rho ≠ 1) :
    chi.LFunction rho = 0 ↔ d.modulus ∣ q ∧ chi = inducedAt d q ∧ rho = e := by
  have hx : 10 ≤ sourceP N := by
    change 10 ≤ (sourceL N) ^ 3
    exact (by norm_num : (10 : ℝ) ≤ 3100 ^ 3).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 3)
  have he : (e.re : ℂ) = e := by
    apply Complex.ext <;> simp [hd.2.2.1]
  have hz : datumL d (e.re : ℂ) = 0 := by rw [he]; exact hd.2.1
  simpa only [he] using fixed_source_zero_iff d hx hd.1 hd.2.2.2.2.le hz hq chi hr ht hpole

theorem paper_source_original_noninducing_no_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdq : ¬d.modulus ∣ q) (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log (sourceP N)) ≤ rho.re)
    (ht : |rho.im| ≤ sourceP N / q) (hpole : chi ≠ 1 ∨ rho ≠ 1) : chi.LFunction rho ≠ 0 :=
  fun hz => hdq ((paper_source_original_zero_iff hN hq hd chi hr ht hpole).mp hz).1

end LiuWang.Proof.SourceRoute.Exception.Restart
