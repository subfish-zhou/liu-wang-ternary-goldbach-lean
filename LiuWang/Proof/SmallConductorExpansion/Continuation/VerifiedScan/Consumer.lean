import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Prime163
import LiuWang.Proof.SmallConductorExpansion.Continuation.Through64

/-! # Scan certificates feed the frozen all-character and actual-source APIs -/

set_option autoImplicit false
noncomputable section

open Finset Complex
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

theorem square_word_scan_original_region {q d : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    (gs : Fin d → ℕ) (hg : ∀ i, IsUnit (gs i : ZMod q))
    (words : List (Option (ℕ × ℕ))) (hcover : SquareWordCover q gs words)
    {m n : ℕ} (hm : 1 ≤ m) (hqm : q ∣ m) (hn : 1 < n)
    {A : ℚ} (hA : 0 ≤ A) (hpow : 2 ≤ A ^ n)
    (hcert : ∀ signs : Fin d → Bool,
      periodSum q (squareValues words signs) ≠ 0 ∨
        ∃ P : ℚ, Weighted q (squareValues words signs) m P A)
    {x beta : ℝ} (hlog : (n : ℝ) ≤ 9.645908801 * Real.log x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq gs hg words hcover hm hqm hn hA hpow _ hlog hb
  intro signs
  rcases hcert signs with h | ⟨P, h⟩
  · exact Or.inl (by simpa only [periodSum_eq] using h)
  · exact Or.inr ⟨P, (weighted_iff _ _ _ _ _).mp h⟩

theorem log_scale_dyadic {x : ℝ} {j n : ℕ}
    (hx : (2 : ℝ) ^ j ≤ x) (hn : (n : ℝ) ≤ 9.645908801 * (j : ℝ) * 0.6931471803) :
    (n : ℝ) ≤ 9.645908801 * Real.log x := by
  have hp : (0 : ℝ) < 2 ^ j := pow_pos (by norm_num) _
  have hl := Real.log_le_log hp hx
  rw [Real.log_pow] at hl
  have ht := Real.log_two_gt_d9
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  nlinarith

theorem ordinary_of_level_coverage (paid : ℕ → Prop)
    (hpaid : ∀ (r : ℕ) [NeZero r], paid r →
      ∀ (psi : DirichletCharacter ℂ r), psi ≠ 1 → psi ^ 2 = 1 →
      ∀ {x beta : ℝ}, 10 ≤ x → (r : ℝ) ≤ x →
        1 - 1 / (9.645908801 * Real.log x) ≤ beta → psi.LFunction (beta : ℂ) ≠ 0)
    {x : ℝ} {q : ℕ} [NeZero q] (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (hc : paid chi.conductor) {rho : ℂ}
    (hr : 1 - 1 / (24 * Real.log x) < rho.re) (ht : |rho.im| ≤ x / (q : ℝ))
    (hp : chi ≠ 1 ∨ rho ≠ 1) : chi.LFunction rho ≠ 0 := by
  intro hz
  obtain ⟨d, hd, hdc, _, hdz, hi, _⟩ :=
    RealClosure.family_twentyfour_from_actual_zero hx hq chi rho hr ht hp hz
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  have hn := hpaid d.modulus (by simpa only [hdc] using hc)
    d.character d.ne_one d.square_eq_one hx hd (r24_re_in_original_real_region hx hr)
  exact hn (by simpa only [datumL, he] using hdz)

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
