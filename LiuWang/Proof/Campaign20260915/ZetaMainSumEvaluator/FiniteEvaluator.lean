import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.SharedCache

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator

open LiuWang.Proof.Campaign20260915.ZetaValidation
open Complex Finset

def phaseArgument (e : SharedEntry) (t₀ θ₀ : ℚ) : ℚ :=
  roundRationalAt (10 ^ 24) (t₀ * e.logCenter - θ₀)

def phaseValue (e : SharedEntry) (t₀ θ₀ : ℚ) : QComplex :=
  unitPhaseAt (10 ^ 40) 40 32 (phaseArgument e t₀ θ₀ / 2 ^ 32)

def PhaseFits (e : SharedEntry) (t₀ θ₀ : ℚ) : Prop :=
  |phaseArgument e t₀ θ₀ / 2 ^ 32| ≤ 1

instance (e : SharedEntry) (t₀ θ₀ : ℚ) : Decidable (PhaseFits e t₀ θ₀) :=
  inferInstanceAs (Decidable (|phaseArgument e t₀ θ₀ / 2 ^ 32| ≤ 1))

def termValue (e : SharedEntry) (t₀ θ₀ : ℚ) : ℚ :=
  2 * e.weightCenter * (phaseValue e t₀ θ₀).1

def termRadius (e : SharedEntry) (t₀ dt dθ : ℚ) : ℚ :=
  2 * (e.weightRadius + e.weightCenter *
    (dt * |e.logCenter| + (|t₀| + dt) * e.logRadius + dθ + 2 / 10 ^ 24))

def roundedSum (D : ℕ) (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | m + 1 => roundRationalAt D (roundedSum D f m + f m)

def evaluate (D : ℕ) (cache : ℕ → SharedEntry) (t₀ θ₀ : ℚ) (m : ℕ) : ℚ :=
  roundedSum D (fun j => termValue (cache (j + 1)) t₀ θ₀) m

def evaluationRadius (D : ℕ) (cache : ℕ → SharedEntry) (t₀ dt dθ : ℚ) (m : ℕ) : ℚ :=
  ∑ j ∈ range m, (termRadius (cache (j + 1)) t₀ dt dθ + 1 / D)

noncomputable section

def sourceTerm (t : ℝ) (n : ℕ) : ℝ :=
  2 * (1 / Real.sqrt (n : ℝ)) *
    Real.cos (t * Real.log (n : ℝ) - criticalGammaArgument t)

def finiteMainSum (t : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ range m, sourceTerm t (j + 1)

theorem phase_input_error {n : ℕ} {e : SharedEntry} (he : EntryValid n e)
    {t : ℝ} {t₀ θ₀ dt dθ : ℚ}
    (ht : |t - (t₀ : ℝ)| ≤ (dt : ℝ))
    (hθ : |criticalGammaArgument t - (θ₀ : ℝ)| ≤ (dθ : ℝ)) :
    |t * Real.log (n : ℝ) - criticalGammaArgument t -
      (phaseArgument e t₀ θ₀ : ℝ)| ≤
      ((dt * |e.logCenter| + (|t₀| + dt) * e.logRadius + dθ + 1 / 10 ^ 24 : ℚ) : ℝ) := by
  have ht0 : 0 ≤ (dt : ℝ) := (abs_nonneg _).trans ht
  have htB : |t| ≤ |(t₀ : ℝ)| + (dt : ℝ) := by
    have h := abs_add_le (t - (t₀ : ℝ)) (t₀ : ℝ)
    rw [sub_add_cancel] at h
    linarith
  have hA := mul_le_mul_of_nonneg_right ht (abs_nonneg (e.logCenter : ℝ))
  have hB := mul_le_mul htB he.1 (abs_nonneg _) (by positivity)
  have hsum := abs_add_le ((t - (t₀ : ℝ)) * (e.logCenter : ℝ))
    (t * (Real.log (n : ℝ) - (e.logCenter : ℝ)))
  have hsub := abs_sub_le (((t - (t₀ : ℝ)) * (e.logCenter : ℝ)) +
    t * (Real.log (n : ℝ) - (e.logCenter : ℝ))) 0
    (criticalGammaArgument t - (θ₀ : ℝ))
  simp only [sub_zero, zero_sub, abs_neg, abs_mul] at hsum hsub
  have hr := roundRationalAt_error (D := 10 ^ 24) (by norm_num)
    (t₀ * e.logCenter - θ₀)
  have hid : t * Real.log (n : ℝ) - criticalGammaArgument t -
      ((t₀ * e.logCenter - θ₀ : ℚ) : ℝ) =
      ((t - (t₀ : ℝ)) * (e.logCenter : ℝ) +
        t * (Real.log (n : ℝ) - (e.logCenter : ℝ))) -
          (criticalGammaArgument t - (θ₀ : ℝ)) := by push_cast; ring
  have htri := abs_sub_le (t * Real.log (n : ℝ) - criticalGammaArgument t)
    ((t₀ * e.logCenter - θ₀ : ℚ) : ℝ) (phaseArgument e t₀ θ₀ : ℝ)
  rw [hid, abs_sub_comm (((t₀ * e.logCenter - θ₀ : ℚ) : ℝ))] at htri
  change |(phaseArgument e t₀ θ₀ : ℝ) - ((t₀ * e.logCenter - θ₀ : ℚ) : ℝ)| ≤ _ at hr
  push_cast
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hr
  linarith

theorem phase_cos_error {n : ℕ} {e : SharedEntry} (he : EntryValid n e)
    {t : ℝ} {t₀ θ₀ dt dθ : ℚ}
    (ht : |t - (t₀ : ℝ)| ≤ (dt : ℝ))
    (hθ : |criticalGammaArgument t - (θ₀ : ℝ)| ≤ (dθ : ℝ))
    (hfit : PhaseFits e t₀ θ₀) :
    |Real.cos (t * Real.log (n : ℝ) - criticalGammaArgument t) -
      ((phaseValue e t₀ θ₀).1 : ℝ)| ≤
      ((dt * |e.logCenter| + (|t₀| + dt) * e.logRadius + dθ + 2 / 10 ^ 24 : ℚ) : ℝ) := by
  have hs := unitPhaseAt_original_scale hfit (k := 32) le_rfl
  have hid : (2 : ℝ) ^ 32 * ((phaseArgument e t₀ θ₀ / 2 ^ 32 : ℚ) : ℝ) =
      (phaseArgument e t₀ θ₀ : ℝ) := by push_cast; ring
  rw [hid] at hs
  have hp := (unitPhase_distance_le
    (t * Real.log (n : ℝ) - criticalGammaArgument t) (phaseArgument e t₀ θ₀ : ℝ)).trans
      (phase_input_error he ht hθ)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (exp (((t * Real.log (n : ℝ) - criticalGammaArgument t : ℝ) : ℂ) * I))
    (exp (((phaseArgument e t₀ θ₀ : ℝ) : ℂ) * I)) (phaseValue e t₀ θ₀).toComplex
  have hre := abs_re_le_norm
    (exp (((t * Real.log (n : ℝ) - criticalGammaArgument t : ℝ) : ℂ) * I) -
      (phaseValue e t₀ θ₀).toComplex)
  simp only [sub_re, exp_ofReal_mul_I_re, QComplex.toComplex, add_re, mul_re,
    ratCast_re, ratCast_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
  change ‖exp (((phaseArgument e t₀ θ₀ : ℝ) : ℂ) * I) -
    (phaseValue e t₀ θ₀).toComplex‖ ≤ _ at hs
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_abs, Rat.cast_div, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one] at hp ⊢
  exact (hre.trans (htri.trans (add_le_add hp hs))).trans_eq (by ring)

theorem termValue_error {n : ℕ} {e : SharedEntry} (he : EntryValid n e)
    {t : ℝ} {t₀ θ₀ dt dθ : ℚ}
    (ht : |t - (t₀ : ℝ)| ≤ (dt : ℝ))
    (hθ : |criticalGammaArgument t - (θ₀ : ℝ)| ≤ (dθ : ℝ))
    (hfit : PhaseFits e t₀ θ₀) :
    |sourceTerm t n - (termValue e t₀ θ₀ : ℝ)| ≤ (termRadius e t₀ dt dθ : ℝ) := by
  have hc := phase_cos_error he ht hθ hfit
  let c := Real.cos (t * Real.log (n : ℝ) - criticalGammaArgument t)
  have hw := mul_le_mul he.2.2.2 (Real.abs_cos_le_one
    (t * Real.log (n : ℝ) - criticalGammaArgument t)) (abs_nonneg _)
      ((abs_nonneg _).trans he.2.2.2)
  have hp := mul_le_mul_of_nonneg_left hc he.2.1
  have htri := abs_add_le
    ((1 / Real.sqrt (n : ℝ) - (e.weightCenter : ℝ)) * c)
    ((e.weightCenter : ℝ) * (c - ((phaseValue e t₀ θ₀).1 : ℝ)))
  rw [abs_mul, abs_mul, abs_of_nonneg he.2.1] at htri
  have hid : sourceTerm t n - (termValue e t₀ θ₀ : ℝ) =
      2 * ((1 / Real.sqrt (n : ℝ) - (e.weightCenter : ℝ)) * c +
        (e.weightCenter : ℝ) * (c - ((phaseValue e t₀ θ₀).1 : ℝ))) := by
    dsimp [sourceTerm, termValue, c]
    push_cast
    ring
  rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  dsimp [termRadius]
  push_cast at hp ⊢
  dsimp [c] at htri
  simp only [mul_one] at hw
  linarith

theorem roundedSum_error {D : ℕ} (hD : 1 ≤ D) (f : ℕ → ℝ) (q E : ℕ → ℚ)
    (m : ℕ) (h : ∀ j < m, |f j - (q j : ℝ)| ≤ (E j : ℝ)) :
    |(∑ j ∈ range m, f j) - (roundedSum D q m : ℝ)| ≤
      ∑ j ∈ range m, ((E j : ℝ) + 1 / D) := by
  induction m with
  | zero => simp [roundedSum]
  | succ m ih =>
    have hi := ih (fun j hj => h j (by omega))
    have hj := h m (by omega)
    have hr := roundRationalAt_error hD (roundedSum D q m + q m)
    have ha := abs_add_le ((∑ j ∈ range m, f j) - (roundedSum D q m : ℝ))
      (f m - (q m : ℝ))
    have ht := abs_sub_le ((∑ j ∈ range m, f j) + f m)
      ((roundedSum D q m : ℝ) + (q m : ℝ))
      (roundRationalAt D (roundedSum D q m + q m) : ℝ)
    have hid : (∑ j ∈ range m, f j) + f m -
        ((roundedSum D q m : ℝ) + (q m : ℝ)) =
        ((∑ j ∈ range m, f j) - (roundedSum D q m : ℝ)) + (f m - (q m : ℝ)) := by ring
    rw [hid, abs_sub_comm ((roundedSum D q m : ℝ) + (q m : ℝ))] at ht
    push_cast at hr
    simp only [sum_range_succ, roundedSum]
    linarith

theorem evaluate_error {D m : ℕ} (hD : 1 ≤ D) (cache : ℕ → SharedEntry)
    (hcache : ∀ n, 1 ≤ n → n ≤ m → EntryValid n (cache n))
    {t : ℝ} {t₀ θ₀ dt dθ : ℚ}
    (ht : |t - (t₀ : ℝ)| ≤ (dt : ℝ))
    (hθ : |criticalGammaArgument t - (θ₀ : ℝ)| ≤ (dθ : ℝ))
    (hfit : ∀ n, 1 ≤ n → n ≤ m → PhaseFits (cache n) t₀ θ₀) :
    |finiteMainSum t m - (evaluate D cache t₀ θ₀ m : ℝ)| ≤
      (evaluationRadius D cache t₀ dt dθ m : ℝ) := by
  have h := roundedSum_error hD (fun j => sourceTerm t (j + 1))
    (fun j => termValue (cache (j + 1)) t₀ θ₀)
    (fun j => termRadius (cache (j + 1)) t₀ dt dθ) m
    (fun j hj => termValue_error (hcache _ (by omega) (by omega)) ht hθ
      (hfit _ (by omega) (by omega)))
  simpa [finiteMainSum, evaluate, evaluationRadius] using h

theorem makeEntry_evaluate_error {D S P m : ℕ} (hD : 1 ≤ D) (hS : 1 ≤ S)
    {t : ℝ} {t₀ θ₀ dt dθ : ℚ}
    (ht : |t - (t₀ : ℝ)| ≤ (dt : ℝ))
    (hθ : |criticalGammaArgument t - (θ₀ : ℝ)| ≤ (dθ : ℝ))
    (hfit : ∀ n, 1 ≤ n → n ≤ m → PhaseFits (makeEntry S P n) t₀ θ₀) :
    |finiteMainSum t m - (evaluate D (makeEntry S P) t₀ θ₀ m : ℝ)| ≤
      (evaluationRadius D (makeEntry S P) t₀ dt dθ m : ℝ) :=
  evaluate_error hD _ (fun _ hn _ => makeEntry_valid hS hn P) ht hθ hfit

#print axioms termValue_error
#print axioms makeEntry_evaluate_error

end

end LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator
