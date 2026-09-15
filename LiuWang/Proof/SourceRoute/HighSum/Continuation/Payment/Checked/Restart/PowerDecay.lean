import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.Source27Analysis
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Signed polynomial-exponential monotonicity on the whole scaling half-line -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart

def decayPower (K : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  u ^ n * Real.exp (-K * u ^ (7 : ℕ))

def decayDerivative (K : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (n : ℝ) * u ^ (n - 1) - 7 * K * u ^ (n + 6)

theorem decayPower_deriv (K u : ℝ) (n : ℕ) :
    HasDerivAt (decayPower K n)
      (decayDerivative K n u * Real.exp (-K * u ^ (7 : ℕ))) u := by
  have h := ((hasDerivAt_id u).pow n).mul
    ((((hasDerivAt_id u).pow 7).const_mul (-K)).exp)
  convert! h using 1
  dsimp only [decayDerivative, id_eq]
  rw [pow_add]
  norm_num
  ring

theorem decayDerivative_nonpos {K u : ℝ} (hK : 5 ≤ K) (hu : 1 ≤ u)
    {n : ℕ} (hn : n ≤ 27) : decayDerivative K n u ≤ 0 := by
  have hp : u ^ (n - 1) ≤ u ^ (n + 6) :=
    pow_le_pow_right₀ hu (by omega)
  have hnR : (n : ℝ) ≤ 27 := by exact_mod_cast hn
  have h1 := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have h2 := mul_le_mul_of_nonneg_right
    (show (n : ℝ) ≤ 7 * K by linarith) (show 0 ≤ u ^ (n + 6) by positivity)
  unfold decayDerivative
  linarith

theorem decayDerivative_lower {K u : ℝ} (hK : 0 ≤ K) (hu : 1 ≤ u)
    {n : ℕ} (hn : n ≤ 27) :
    -(7 * K * u ^ (33 : ℕ)) ≤ decayDerivative K n u := by
  have hp : u ^ (n + 6) ≤ u ^ (33 : ℕ) :=
    pow_le_pow_right₀ hu (by omega)
  have h1 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 7 * K by positivity)
  have h2 : 0 ≤ (n : ℝ) * u ^ (n - 1) := by positivity
  unfold decayDerivative
  linarith

theorem decayDerivative_leading {K u : ℝ} (hu : 1 ≤ u) :
    decayDerivative K 27 u ≤ (27 - 7 * K) * u ^ (33 : ℕ) := by
  have h := mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hu (by norm_num : 26 ≤ 33)) (by norm_num : (0 : ℝ) ≤ 27)
  norm_num [decayDerivative] at *
  linarith

def signedDecay (K B C D E F u : ℝ) : ℝ :=
  decayPower K 27 u - B * decayPower K 26 u - C * decayPower K 20 u +
    E * decayPower K 19 u + F * decayPower K 13 u - D * decayPower K 12 u

theorem signedDecay_antitone {K B C D E F : ℝ}
    (hK : 5 ≤ K) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hs : B + C + D ≤ 1 / 5) :
    AntitoneOn (signedDecay K B C D E F) (Set.Ici 1) := by
  let d := fun u =>
    (decayDerivative K 27 u - B * decayDerivative K 26 u -
      C * decayDerivative K 20 u + E * decayDerivative K 19 u +
      F * decayDerivative K 13 u - D * decayDerivative K 12 u) *
      Real.exp (-K * u ^ (7 : ℕ))
  have hd (u : ℝ) : HasDerivAt (signedDecay K B C D E F) (d u) u := by
    have hh := (((((decayPower_deriv K u 27).sub
      ((decayPower_deriv K u 26).const_mul B)).sub
        ((decayPower_deriv K u 20).const_mul C)).add
          ((decayPower_deriv K u 19).const_mul E)).add
            ((decayPower_deriv K u 13).const_mul F)).sub
              ((decayPower_deriv K u 12).const_mul D)
    convert! hh using 1
    dsimp only [d]
    ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (1 : ℝ))
    (fun u _ => (hd u).continuousAt.continuousWithinAt)
    (fun u _ => (hd u).hasDerivWithinAt)
  intro u hu
  have hu1 : 1 ≤ u := interior_subset hu
  dsimp only [d]
  apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
  have h0 := decayDerivative_leading (K := K) hu1
  have h1 := mul_le_mul_of_nonneg_left
    (decayDerivative_lower (by linarith : 0 ≤ K) hu1 (n := 26) (by norm_num)) hB
  have h2 := mul_le_mul_of_nonneg_left
    (decayDerivative_lower (by linarith : 0 ≤ K) hu1 (n := 20) (by norm_num)) hC
  have h3 := mul_le_mul_of_nonneg_left
    (decayDerivative_lower (by linarith : 0 ≤ K) hu1 (n := 12) (by norm_num)) hD
  have h4 := mul_nonpos_of_nonneg_of_nonpos hE
    (decayDerivative_nonpos hK hu1 (n := 19) (by norm_num))
  have h5 := mul_nonpos_of_nonneg_of_nonpos hF
    (decayDerivative_nonpos hK hu1 (n := 13) (by norm_num))
  have h6 := mul_le_mul_of_nonneg_right hs (show 0 ≤ 7 * K * u ^ (33 : ℕ) by positivity)
  have h7 := mul_nonpos_of_nonpos_of_nonneg
    (show 27 - (4 / 5 : ℝ) * (7 * K) ≤ 0 by linarith)
    (show 0 ≤ u ^ (33 : ℕ) by positivity)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
