import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors

def nextLevel : Fin 9 → ℕ := ![85, 87, 88, 89, 91, 92, 93, 95, 97]

instance nextLevel_neZero (i : Fin 9) : NeZero (nextLevel i) := by
  constructor
  fin_cases i <;> decide

def nextGenerators : Fin 9 → Fin 3 → ℕ :=
  ![![2, 3, 1], ![2, 5, 1], ![3, 5, 7], ![3, 1, 1], ![2, 3, 1],
    ![3, 5, 1], ![2, 11, 1], ![2, 7, 1], ![5, 1, 1]]

def nextWords (i : Fin 9) : List (Option (ℕ × ℕ)) :=
  List.ofFn fun a : Fin (nextLevel i) =>
    ((List.range (nextLevel i)).flatMap fun s =>
      (List.range 8).map fun mask => (s, mask)).find? fun w =>
        decide (IsUnit (w.1 : ZMod (nextLevel i)) ∧
          (a.val : ZMod (nextLevel i)) =
            (w.1 : ZMod (nextLevel i)) ^ 2 *
              squareWord (nextLevel i) (nextGenerators i) w.2)

theorem nextCovers (i : Fin 9) :
    SquareWordCover (nextLevel i) (nextGenerators i) (nextWords i) := by
  fin_cases i <;> decide +kernel

theorem nextCertificates (i : Fin 9) : ∀ signs : Fin 3 → Bool,
    VerifiedScan.periodSum (nextLevel i) (squareValues (nextWords i) signs) ≠ 0 ∨
      VerifiedScan.Weighted (nextLevel i) (squareValues (nextWords i) signs)
        (nextLevel i) 20 (509 / 500) := by
  unfold VerifiedScan.Weighted
  fin_cases i <;> decide +kernel

theorem next_level_original_region (i : Fin 9)
    (chi : DirichletCharacter ℂ (nextLevel i)) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : (nextLevel i : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have h64 : (64 : ℝ) ≤ nextLevel i := by fin_cases i <;> norm_num [nextLevel]
  apply VerifiedScan.square_word_scan_original_region chi hc hsq (nextGenerators i)
    (by fin_cases i <;> decide +kernel) (nextWords i) (nextCovers i)
    (m := nextLevel i) (by fin_cases i <;> decide) (dvd_refl _)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_forty (h64.trans hx)) hb
  intro signs
  exact (nextCertificates i signs).imp_right fun h => ⟨20, h⟩

#print axioms next_level_original_region

end LiuWang.Proof.Campaign20260915.SmallConductors
