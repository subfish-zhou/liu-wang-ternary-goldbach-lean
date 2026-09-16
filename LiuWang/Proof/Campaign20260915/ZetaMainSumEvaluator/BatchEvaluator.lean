import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.CutoffIntervals

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator

open LiuWang.Proof.Campaign20260915.ZetaValidation

def buildSharedCache (S P M : ℕ) : List SharedEntry :=
  let logTwo := logOneMinusSeries (1 / 2) P
  (List.range M).map fun j =>
    let n := j + 1
    let k := logExponent n
    let root := Nat.sqrt (n * S ^ 2)
    let weight : ℚ := (S : ℚ) / (root + 1)
    { logCenter := roundRationalAt S
        (k * logTwo - logOneMinusSeries (1 - (n : ℚ) / 2 ^ k) P)
      logRadius := (k + 1 : ℚ) * (1 / 2) ^ P + 1 / S
      weightCenter := weight
      weightRadius := (S : ℚ) / root - weight }

def evaluateEntries (D : ℕ) (entries : List SharedEntry) (t₀ θ₀ : ℚ) : ℚ :=
  entries.foldl (fun acc e => roundRationalAt D (acc + termValue e t₀ θ₀)) 0

structure BatchInput where
  heightCenter : ℚ
  thetaCenter : ℚ
  terms : ℕ

def evaluatePrefix (D : ℕ) (entries : List SharedEntry) (r : BatchInput) : Option ℚ :=
  if r.terms ≤ entries.length then
    some (evaluateEntries D (entries.take r.terms) r.heightCenter r.thetaCenter)
  else none

def evaluateBatch (D S P M : ℕ) (inputs : List BatchInput) : List (Option ℚ) :=
  let entries := buildSharedCache S P M
  inputs.map (evaluatePrefix D entries)

theorem buildSharedCache_eq (S P M : ℕ) : buildSharedCache S P M = sharedCache S P M := rfl

theorem sharedCache_succ (S P m : ℕ) :
    sharedCache S P (m + 1) = sharedCache S P m ++ [makeEntry S P (m + 1)] := by
  simp [sharedCache, List.range_succ]

theorem evaluateEntries_sharedCache (D S P m : ℕ) (t₀ θ₀ : ℚ) :
    evaluateEntries D (sharedCache S P m) t₀ θ₀ =
      evaluate D (makeEntry S P) t₀ θ₀ m := by
  induction m with
  | zero => simp [sharedCache, evaluateEntries, evaluate, roundedSum]
  | succ m ih =>
    rw [sharedCache_succ]
    simp only [evaluateEntries, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change roundRationalAt D
      (evaluateEntries D (sharedCache S P m) t₀ θ₀ + termValue (makeEntry S P (m + 1)) t₀ θ₀) = _
    rw [ih]
    rfl

theorem evaluatePrefix_sharedCache {D S P M : ℕ} (r : BatchInput) (hm : r.terms ≤ M) :
    evaluatePrefix D (buildSharedCache S P M) r =
      some (evaluate D (makeEntry S P) r.heightCenter r.thetaCenter r.terms) := by
  rw [buildSharedCache_eq]
  have hlen : (sharedCache S P M).length = M := by simp [sharedCache]
  rw [evaluatePrefix, hlen, if_pos hm, sharedCache_prefix S P M r.terms hm,
    evaluateEntries_sharedCache]

theorem evaluatePrefix_insufficient {D : ℕ} {entries : List SharedEntry} {r : BatchInput}
    (h : entries.length < r.terms) : evaluatePrefix D entries r = none := by
  simp [evaluatePrefix, Nat.not_le.mpr h]

theorem evaluateBatch_getElem {D S P M : ℕ} {inputs : List BatchInput} {i : ℕ}
    (hi : i < inputs.length) (hm : (inputs[i]).terms ≤ M) :
    (evaluateBatch D S P M inputs)[i]'(by simpa [evaluateBatch] using hi) =
      some (evaluate D (makeEntry S P) (inputs[i]).heightCenter (inputs[i]).thetaCenter
        (inputs[i]).terms) := by
  simpa only [evaluateBatch, List.getElem_map] using
    evaluatePrefix_sharedCache (D := D) (S := S) (P := P) (inputs[i]) hm

noncomputable section

theorem evaluatePrefix_finite_error {D S P M : ℕ} (hD : 1 ≤ D) (hS : 1 ≤ S)
    (r : BatchInput) (hm : r.terms ≤ M) {t : ℝ} {dt dθ : ℚ}
    (ht : |t - (r.heightCenter : ℝ)| ≤ (dt : ℝ))
    (hθ : |criticalGammaArgument t - (r.thetaCenter : ℝ)| ≤ (dθ : ℝ))
    (hfit : ∀ n, 1 ≤ n → n ≤ r.terms →
      PhaseFits (makeEntry S P n) r.heightCenter r.thetaCenter) :
    ∃ q : ℚ, evaluatePrefix D (buildSharedCache S P M) r = some q ∧
      |finiteMainSum t r.terms - (q : ℝ)| ≤
        (evaluationRadius D (makeEntry S P) r.heightCenter dt dθ r.terms : ℝ) := by
  refine ⟨_, evaluatePrefix_sharedCache r hm, ?_⟩
  exact makeEntry_evaluate_error hD hS ht hθ hfit

theorem evaluatePrefix_sourceWindow_error {D S P M lo hi : ℕ}
    (hD : 1 ≤ D) (hS : 1 ≤ S) (hm : lo ≤ M)
    {a b t₀ θ₀ dt dθ : ℚ} (hw : CutoffWindow a b lo hi)
    {t : ℝ} (hab : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ))
    (ht : |t - (t₀ : ℝ)| ≤ (dt : ℝ))
    (hθ : |criticalGammaArgument t - (θ₀ : ℝ)| ≤ (dθ : ℝ))
    (hfit : ∀ n, 1 ≤ n → n ≤ lo → PhaseFits (makeEntry S P n) t₀ θ₀) :
    ∃ q : ℚ,
      evaluatePrefix D (buildSharedCache S P M) ⟨t₀, θ₀, lo⟩ = some q ∧
      |sourceMainSum t - (q : ℝ)| ≤
        (evaluationRadius D (makeEntry S P) t₀ dt dθ lo : ℝ) + 2 * ((hi - lo : ℕ) : ℝ) := by
  refine ⟨_, evaluatePrefix_sharedCache _ hm, ?_⟩
  exact evaluate_window_error hD _ (fun _ hn _ => makeEntry_valid hS hn P)
    hw hab ht hθ hfit

#print axioms evaluatePrefix_finite_error
#print axioms evaluatePrefix_sourceWindow_error

end

end LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator
