import LiuWang.Proof.Campaign20260915.ZetaValidation.PrecisionPhase
import LiuWang.Proof.Campaign20260915.ZetaValidation.DyadicLogarithm
import LiuWang.Proof.Campaign20260915.ZetaValidation.RationalEvaluation
import Mathlib.Data.Nat.Log

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator

open LiuWang.Proof.Campaign20260915.ZetaValidation

structure SharedEntry where
  logCenter : ℚ
  logRadius : ℚ
  weightCenter : ℚ
  weightRadius : ℚ
  deriving DecidableEq

def logExponent (n : ℕ) : ℕ := n.log2 + 1

def makeEntry (D P n : ℕ) : SharedEntry :=
  { logCenter := roundRationalAt D (dyadicLog n (logExponent n) P)
    logRadius := (logExponent n + 1 : ℚ) * (1 / 2) ^ P + 1 / D
    weightCenter := reciprocalSqrtLower n D
    weightRadius := reciprocalSqrtUpper n D - reciprocalSqrtLower n D }

def sharedCache (D P M : ℕ) : List SharedEntry :=
  (List.range M).map (fun j => makeEntry D P (j + 1))

noncomputable section

def EntryValid (n : ℕ) (e : SharedEntry) : Prop :=
  |Real.log (n : ℝ) - (e.logCenter : ℝ)| ≤ (e.logRadius : ℝ) ∧
  0 ≤ (e.weightCenter : ℝ) ∧
  (e.weightCenter : ℝ) ≤ 1 ∧
  |1 / Real.sqrt (n : ℝ) - (e.weightCenter : ℝ)| ≤ (e.weightRadius : ℝ)

theorem logExponent_normalizes {n : ℕ} (hn : 1 ≤ n) :
    1 / 2 ≤ (n : ℚ) / 2 ^ logExponent n ∧
      (n : ℚ) / 2 ^ logExponent n ≤ 1 := by
  have hl := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have hu := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  rw [logExponent, Nat.log2_eq_log_two]
  have hlQ : (2 : ℚ) ^ Nat.log 2 n ≤ n := by exact_mod_cast hl
  have huQ : (n : ℚ) < 2 ^ (Nat.log 2 n + 1) := by exact_mod_cast hu
  constructor
  · rw [le_div_iff₀ (by positivity), pow_succ]
    linarith
  · rw [div_le_one (by positivity)]
    exact huQ.le

theorem makeEntry_valid {D n : ℕ} (hD : 1 ≤ D) (hn : 1 ≤ n) (P : ℕ) :
    EntryValid n (makeEntry D P n) := by
  obtain ⟨hl, hu⟩ := logExponent_normalizes hn
  have hlog := dyadicLog_error hl hu P
  have hr := roundRationalAt_error hD (dyadicLog n (logExponent n) P)
  have hs := reciprocalSqrt_enclosure hn hD
  have ha : (0 : ℝ) ≤ reciprocalSqrtLower n D := by
    unfold reciprocalSqrtLower
    push_cast
    positivity
  have hw : 1 / Real.sqrt (n : ℝ) ≤ 1 := by
    apply (div_le_one (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega)))).mpr
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  refine ⟨?_, ha, hs.1.trans hw, ?_⟩
  · have ht := abs_sub_le (Real.log (n : ℝ)) (dyadicLog n (logExponent n) P : ℝ)
      (roundRationalAt D (dyadicLog n (logExponent n) P) : ℝ)
    rw [abs_sub_comm (dyadicLog n (logExponent n) P : ℝ)] at ht
    dsimp [makeEntry]
    push_cast
    exact ht.trans (add_le_add (by simpa using hlog) hr)
  · dsimp [makeEntry]
    push_cast
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
    exact sub_le_sub_right hs.2 _

theorem sharedCache_getElem {D P M j : ℕ} (hj : j < M) :
    (sharedCache D P M)[j]'(by simpa [sharedCache] using hj) =
      makeEntry D P (j + 1) := by
  simp [sharedCache]

theorem sharedCache_prefix (D P M K : ℕ) (hKM : K ≤ M) :
    (sharedCache D P M).take K = sharedCache D P K := by
  simp [sharedCache, ← List.map_take, List.take_range, Nat.min_eq_left hKM]

theorem sharedCache_valid {D P M j : ℕ} (hD : 1 ≤ D) (hj : j < M) :
    EntryValid (j + 1) ((sharedCache D P M)[j]'(by simpa [sharedCache] using hj)) := by
  rw [sharedCache_getElem hj]
  exact makeEntry_valid hD (by omega) P

#print axioms makeEntry_valid
#print axioms sharedCache_valid

end

end LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator
