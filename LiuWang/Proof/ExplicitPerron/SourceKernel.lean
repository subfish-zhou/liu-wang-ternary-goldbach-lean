import LiuWang.Proof.ExplicitPerron.NearSum
import LiuWang.Proof.ExplicitPerron.SourceConstants

/-!
# Liu--Wang companion, printed Lemma 4.1 (p. 289)

The later reference to "Lemma 4.2" refers to this same mathematical contract.
The lower central contribution is multiplied by `2^b`, not `2*b`.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace LiuWang.Proof.ExplicitPerron

theorem normSum_eq_positiveSeries (a : ℕ → ℂ) (b : ℝ) :
    (∑' n, ‖LSeries.term a (b : ℂ) n‖) =
      ∑' n : ℕ, if n = 0 then 0 else ‖a n‖ / (n : ℝ) ^ b := by
  apply tsum_congr
  intro n
  simpa only [Complex.ofReal_re] using LSeries.norm_term_eq a (b : ℂ) n

def sourceError (a : ℕ → ℂ) (A : ℝ → ℝ) (x b c : ℝ) : ℝ :=
  (x ^ b * (∑' n, ‖LSeries.term a (b : ℂ) n‖) +
    2 ^ b * A x * (x * Real.log x + 3 / 2 * x - 1 / 2) +
    x * A (2 * x) * (Real.log x + Real.log 2 + 2)) / (Real.pi * c * Real.log 2)

theorem source_perron (a : ℕ → ℂ) (A : ℝ → ℝ)
    (hA : Monotone A) (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ A n)
    {m : ℕ} (hm : 1 ≤ m) {b c : ℝ} (hb : 1 < b) (hc : 1 ≤ c)
    (hsum : LSeriesSummable a (b : ℂ)) :
    ‖vertical (seriesIntegrand a ((m : ℝ) + 1 / 2)) b (-c) c -
      ∑ n ∈ Icc 1 m, a n‖ ≤ sourceError a A ((m : ℝ) + 1 / 2) b c := by
  let x : ℝ := (m : ℝ) + 1 / 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx1 : 1 ≤ x := by dsimp [x]; linarith
  have hA1 : 0 ≤ A 1 := (norm_nonneg (a 1)).trans (by simpa using ha 1 le_rfl)
  have hAx : 0 ≤ A x := hA1.trans (hA hx1)
  have hA2x : 0 ≤ A (2 * x) := hA1.trans (hA (by linarith))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow := source_lower_halfHarmonic hm
  have hupp := source_upper_halfHarmonic hm
  change Real.log 2 * halfHarmonic m ≤ Real.log x + 3 / 2 - (1 / 2) / x at hlow
  change Real.log 2 * halfHarmonic (m + 1) ≤ Real.log x + Real.log 2 + 2 at hupp
  have hlow' :
      Real.log 2 * x * halfHarmonic m ≤ x * Real.log x + 3 / 2 * x - 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right hlow hx.le
    have heq : (Real.log x + 3 / 2 - (1 / 2) / x) * x =
        x * Real.log x + 3 / 2 * x - 1 / 2 := by field_simp
    rw [heq] at h
    nlinarith
  have hcentral := centralCost_halfInteger_le a A hA ha hm hb.le
  change centralCost a x b ≤
    2 ^ b * A x * x * halfHarmonic m + A (2 * x) * x * halfHarmonic (m + 1) at hcentral
  have hcentral' : centralCost a x b * Real.log 2 ≤
      2 ^ b * A x * (x * Real.log x + 3 / 2 * x - 1 / 2) +
      x * A (2 * x) * (Real.log x + Real.log 2 + 2) := by
    have h := mul_le_mul_of_nonneg_right hcentral hlog.le
    have hl := mul_le_mul_of_nonneg_left hlow' (show 0 ≤ 2 ^ b * A x by positivity)
    have hu := mul_le_mul_of_nonneg_left hupp (show 0 ≤ x * A (2 * x) by positivity)
    nlinarith
  have hmain := norm_vertical_sub_sum_le_dyadic a (T := c) hx
    (halfInteger_ne_nat m) (zero_lt_one.trans hb) (by linarith) hsum
  rw [floor_halfInteger] at hmain
  apply hmain.trans
  change (x ^ b / Real.log 2 * (∑' n, ‖LSeries.term a (b : ℂ) n‖) +
    centralCost a x b) / (Real.pi * c) ≤ sourceError a A x b c
  have he := (le_div_iff₀ hlog).2 hcentral'
  calc
    _ ≤ (x ^ b / Real.log 2 * (∑' n, ‖LSeries.term a (b : ℂ) n‖) +
        (2 ^ b * A x * (x * Real.log x + 3 / 2 * x - 1 / 2) +
          x * A (2 * x) * (Real.log x + Real.log 2 + 2)) / Real.log 2) /
        (Real.pi * c) := by gcongr
    _ = sourceError a A x b c := by unfold sourceError; ring

theorem source_perron_of_series (a : ℕ → ℂ) (A : ℝ → ℝ) (f : ℂ → ℂ)
    (hf : ∀ s : ℂ, 1 < s.re → f s = LSeries a s)
    (hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hA : Monotone A) (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ A n)
    {m : ℕ} (hm : 1 ≤ m) {b c : ℝ} (hb : 1 < b) (hc : 1 ≤ c) :
    ‖vertical (fun s => f s * (((m : ℝ) + 1 / 2 : ℂ) ^ s / s)) b (-c) c -
      ∑ n ∈ Icc 1 m, a n‖ ≤ sourceError a A ((m : ℝ) + 1 / 2) b c := by
  have heq : vertical (fun s => f s * (((m : ℝ) + 1 / 2 : ℂ) ^ s / s)) b (-c) c =
      vertical (seriesIntegrand a ((m : ℝ) + 1 / 2)) b (-c) c := by
    unfold vertical
    congr 2
    funext u
    dsimp only [seriesIntegrand]
    rw [hf _ (by simpa using hb)]
    push_cast
    rfl
  rw [heq]
  exact source_perron a A hA ha hm hb hc (hsum _ (by simpa using hb))

end LiuWang.Proof.ExplicitPerron
