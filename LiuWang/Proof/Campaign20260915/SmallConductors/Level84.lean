import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors

def generators84 : Fin 3 → ℕ := ![5, 11, 13]

def squarePairs84 : List (ℕ × ℕ) :=
  (List.range 84).flatMap fun s => (List.range 8).map fun mask => (s, mask)

def words84 : List (Option (ℕ × ℕ)) :=
  List.ofFn fun a : Fin 84 => squarePairs84.find? fun w =>
    decide (IsUnit (w.1 : ZMod 84) ∧
      (a.val : ZMod 84) = (w.1 : ZMod 84) ^ 2 * squareWord 84 generators84 w.2)

theorem cover84 : SquareWordCover 84 generators84 words84 := by
  decide +kernel

theorem certificates84 : ∀ signs : Fin 3 → Bool,
    VerifiedScan.periodSum 84 (squareValues words84 signs) ≠ 0 ∨
      VerifiedScan.Weighted 84 (squareValues words84 signs) 84 20 (509 / 500) := by
  unfold VerifiedScan.Weighted
  decide +kernel

theorem quadratic_84_original_region (chi : DirichletCharacter ℂ 84)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 84 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply VerifiedScan.square_word_scan_original_region chi hc hsq generators84
    (by decide +kernel) words84 cover84 (m := 84) (by decide) (dvd_refl 84)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_forty (by linarith)) hb
  intro signs
  exact (certificates84 signs).imp_right fun h => ⟨20, h⟩

#print axioms quadratic_84_original_region

end LiuWang.Proof.Campaign20260915.SmallConductors
