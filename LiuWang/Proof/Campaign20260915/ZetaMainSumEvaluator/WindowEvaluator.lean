import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.BatchEvaluator

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator

open LiuWang.Proof.Campaign20260915.ZetaValidation

def radiusEntries (D : ℕ) (entries : List SharedEntry) (t₀ dt dθ : ℚ) : ℚ :=
  (entries.map (fun e => termRadius e t₀ dt dθ + 1 / D)).sum

structure WindowInput where
  lowerHeight : ℚ
  upperHeight : ℚ
  heightCenter : ℚ
  heightRadius : ℚ
  thetaCenter : ℚ
  thetaRadius : ℚ
  lowerTerms : ℕ
  upperTerms : ℕ

def WindowChecks (r : WindowInput) : Prop :=
  CutoffWindow r.lowerHeight r.upperHeight r.lowerTerms r.upperTerms ∧
  r.lowerHeight ≤ r.upperHeight ∧
  0 ≤ r.heightRadius ∧ 0 ≤ r.thetaRadius ∧
  |r.lowerHeight - r.heightCenter| ≤ r.heightRadius ∧
  |r.upperHeight - r.heightCenter| ≤ r.heightRadius

instance (r : WindowInput) : Decidable (WindowChecks r) := by
  unfold WindowChecks
  infer_instance

def WindowReady (D : ℕ) (entries : List SharedEntry) (r : WindowInput) : Prop :=
  1 ≤ D ∧ r.lowerTerms ≤ entries.length ∧ WindowChecks r ∧
    ∀ e ∈ entries.take r.lowerTerms, PhaseFits e r.heightCenter r.thetaCenter

instance (D : ℕ) (entries : List SharedEntry) (r : WindowInput) :
    Decidable (WindowReady D entries r) := by
  unfold WindowReady
  infer_instance

def windowCenter (D : ℕ) (entries : List SharedEntry) (r : WindowInput) : ℚ :=
  evaluateEntries D (entries.take r.lowerTerms) r.heightCenter r.thetaCenter

def windowRadius (D : ℕ) (entries : List SharedEntry) (r : WindowInput) : ℚ :=
  radiusEntries D (entries.take r.lowerTerms) r.heightCenter r.heightRadius r.thetaRadius +
    2 * (r.upperTerms - r.lowerTerms : ℕ)

def checkedWindow (D : ℕ) (entries : List SharedEntry) (r : WindowInput) :
    Except String (ℚ × ℚ) :=
  if WindowReady D entries r then
    .ok (windowCenter D entries r - windowRadius D entries r,
      windowCenter D entries r + windowRadius D entries r)
  else .error "Invalid rounding grid, cache length, height/cutoff window, radius, or phase scale"

def checkedBatch (D S P M : ℕ) (inputs : List WindowInput) :
    List (Except String (ℚ × ℚ)) :=
  if 1 ≤ S then
    let entries := buildSharedCache S P M
    inputs.map (checkedWindow D entries)
  else inputs.map (fun _ => .error "Reciprocal-square-root and logarithm grid must be positive")

theorem radiusEntries_sharedCache (D S P m : ℕ) (t₀ dt dθ : ℚ) :
    radiusEntries D (sharedCache S P m) t₀ dt dθ =
      evaluationRadius D (makeEntry S P) t₀ dt dθ m := by
  induction m with
  | zero => simp [radiusEntries, sharedCache, evaluationRadius]
  | succ m ih =>
    rw [sharedCache_succ]
    simp only [radiusEntries, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    change radiusEntries D (sharedCache S P m) t₀ dt dθ +
      (termRadius (makeEntry S P (m + 1)) t₀ dt dθ + 1 / D) = _
    rw [ih]
    exact (Finset.sum_range_succ _ _).symm

noncomputable section

theorem windowChecks_height_error {r : WindowInput} (h : WindowChecks r)
    {t : ℝ} (ht : (r.lowerHeight : ℝ) ≤ t ∧ t ≤ (r.upperHeight : ℝ)) :
    |t - (r.heightCenter : ℝ)| ≤ (r.heightRadius : ℝ) := by
  have hl : |(r.lowerHeight : ℝ) - (r.heightCenter : ℝ)| ≤ (r.heightRadius : ℝ) := by
    exact_mod_cast h.2.2.2.2.1
  have hu : |(r.upperHeight : ℝ) - (r.heightCenter : ℝ)| ≤ (r.heightRadius : ℝ) := by
    exact_mod_cast h.2.2.2.2.2
  rw [abs_le] at hl hu ⊢
  constructor <;> linarith [ht.1, ht.2, hl.1, hu.2]

theorem windowReady_error {D S P M : ℕ} (hS : 1 ≤ S) {r : WindowInput}
    (h : WindowReady D (buildSharedCache S P M) r)
    {t : ℝ} (ht : (r.lowerHeight : ℝ) ≤ t ∧ t ≤ (r.upperHeight : ℝ))
    (hθ : |criticalGammaArgument t - (r.thetaCenter : ℝ)| ≤ (r.thetaRadius : ℝ)) :
    |sourceMainSum t - (windowCenter D (buildSharedCache S P M) r : ℝ)| ≤
      (windowRadius D (buildSharedCache S P M) r : ℝ) := by
  have hm : r.lowerTerms ≤ M := by simpa [buildSharedCache] using h.2.1
  have hphase := h.2.2.2
  rw [buildSharedCache_eq, sharedCache_prefix S P M r.lowerTerms hm] at hphase
  have hfit (n : ℕ) (hn : 1 ≤ n) (hN : n ≤ r.lowerTerms) :
      PhaseFits (makeEntry S P n) r.heightCenter r.thetaCenter := by
    apply hphase
    unfold sharedCache
    apply List.mem_map.mpr
    refine ⟨n - 1, List.mem_range.mpr (by omega), ?_⟩
    congr 1
    omega
  have he := evaluate_window_error h.1 (makeEntry S P)
    (fun _ hn _ => makeEntry_valid hS hn P) h.2.2.1.1 ht
    (windowChecks_height_error h.2.2.1 ht) hθ hfit
  rw [windowCenter, windowRadius, buildSharedCache_eq,
    sharedCache_prefix S P M r.lowerTerms hm, evaluateEntries_sharedCache,
    radiusEntries_sharedCache]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using he

theorem checkedWindow_sound {D S P M : ℕ} (hS : 1 ≤ S) {r : WindowInput}
    {bounds : ℚ × ℚ} (hout : checkedWindow D (buildSharedCache S P M) r = .ok bounds)
    {t : ℝ} (ht : (r.lowerHeight : ℝ) ≤ t ∧ t ≤ (r.upperHeight : ℝ))
    (hθ : |criticalGammaArgument t - (r.thetaCenter : ℝ)| ≤ (r.thetaRadius : ℝ)) :
    (bounds.1 : ℝ) ≤ sourceMainSum t ∧ sourceMainSum t ≤ (bounds.2 : ℝ) := by
  unfold checkedWindow at hout
  split_ifs at hout with h
  · cases hout
    have he := abs_le.mp (windowReady_error hS h ht hθ)
    simp only [Rat.cast_sub, Rat.cast_add]
    constructor <;> linarith [he.1, he.2]
theorem checkedBatch_getElem {D S P M : ℕ} (hS : 1 ≤ S)
    {inputs : List WindowInput} {i : ℕ} (hi : i < inputs.length) :
    (checkedBatch D S P M inputs)[i]'(by simpa [checkedBatch, hS] using hi) =
      checkedWindow D (buildSharedCache S P M) (inputs[i]) := by
  simp [checkedBatch, hS]

theorem checkedBatch_sound {D S P M : ℕ} (hS : 1 ≤ S)
    {inputs : List WindowInput} {i : ℕ} (hi : i < inputs.length) {bounds : ℚ × ℚ}
    (hout : (checkedBatch D S P M inputs)[i]'(by simpa [checkedBatch, hS] using hi) = .ok bounds)
    {t : ℝ} (ht : ((inputs[i]).lowerHeight : ℝ) ≤ t ∧ t ≤ ((inputs[i]).upperHeight : ℝ))
    (hθ : |criticalGammaArgument t - ((inputs[i]).thetaCenter : ℝ)| ≤
      ((inputs[i]).thetaRadius : ℝ)) :
    (bounds.1 : ℝ) ≤ sourceMainSum t ∧ sourceMainSum t ≤ (bounds.2 : ℝ) := by
  rw [checkedBatch_getElem hS hi] at hout
  exact checkedWindow_sound hS hout ht hθ

#print axioms checkedWindow_sound
#print axioms checkedBatch_sound

end

end LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator
