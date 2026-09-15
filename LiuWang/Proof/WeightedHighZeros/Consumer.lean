import LiuWang.Proof.WeightedHighZeros.Shells
import LiuWang.Proof.DirichletZeroCount.Applications.CompleteValues
import LiuWang.Proof.OscillatoryBounds.Consumer

/-!
# Original closed-band, primed-sum and oscillatory consumers

Removing a real exceptional value changes nothing above the positive omega.
The source prime removes that value only; the separate retained-zero identity
also handles the frozen interface's removal of its real reflection.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedHighZeros

def highValues {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : Finset ℂ :=
  bandValues chi (1 / 2) (omegaCutoff N q) (sourceT N)

theorem mem_highValues {N q : ℕ} [NeZero q] {chi : Character q} {rho : ℂ} :
    rho ∈ highValues N chi ↔ chi.LFunction rho = 0 ∧
      1 / 2 ≤ rho.re ∧ rho.re < 1 ∧
        omegaCutoff N q ≤ |rho.im| ∧ |rho.im| ≤ sourceT N := by
  rw [highValues, mem_bandValues]
  constructor
  · rintro ⟨hz, ⟨_, h1, ht⟩, ha, hu⟩
    exact ⟨hz, ha, h1, hu, ht⟩
  · rintro ⟨hz, ha, h1, hu, ht⟩
    exact ⟨hz, ⟨by linarith, h1, ht⟩, ha, hu⟩

theorem highValues_eq_complete {N q : ℕ} [NeZero q] (chi : Character q) :
    highValues N chi = (CompleteExpansion.zeroValues chi (sourceT N)).filter
      (fun rho => omegaCutoff N q ≤ |rho.im|) := by
  simp only [highValues, bandValues, Applications.half_values_eq_complete]

theorem highValue_im_ne_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {chi : Character q} {rho : ℂ}
    (hrho : rho ∈ highValues N chi) : rho.im ≠ 0 := by
  have hpos := Parameters.omegaCutoff_pos
    (Parameters.exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)
  exact abs_pos.mp (hpos.trans_le (mem_highValues.mp hrho).2.2.2.1)

def primedHighSum (N q : ℕ) [NeZero q] (exceptional : Option ℂ) : ℝ :=
  ∑ chi : Character q,
    ∑ rho ∈ (highValues N chi).filter (fun rho => exceptional ≠ some rho),
      (analyticOrderNatAt chi.LFunction rho : ℝ) *
        ((N : ℝ) ^ (rho.re - 1) / |rho.im|)

theorem primedValues_eq_highValues {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (chi : Character q) {exceptional : Option ℂ}
    (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    (highValues N chi).filter (fun rho => exceptional ≠ some rho) = highValues N chi := by
  apply Finset.filter_eq_self.mpr
  intro rho hrho h
  exact highValue_im_ne_zero hN hrho (he rho h)

theorem primedHighSum_eq_highSum {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {exceptional : Option ℂ}
    (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    primedHighSum N q exceptional = highSum N q := by
  unfold primedHighSum
  simp only [primedValues_eq_highValues hN _ he]
  rfl

theorem faithful_choice_real {q : ℕ} [NeZero q] {chi : Character q} {c : ℝ}
    {exceptional : Option ℂ} (he : IsExceptionalZeroChoice' c chi exceptional) :
    ∀ beta, exceptional = some beta → beta.im = 0 := by
  intro beta hb
  subst exceptional
  exact he.2.1

theorem retainedValues_eq_highValues {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (chi : Character q) {exceptional : Option ℂ}
    (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    (highValues N chi).filter (IsRetainedZero' exceptional) = highValues N chi := by
  apply Finset.filter_eq_self.mpr
  intro rho hrho
  cases exceptional with
  | none => trivial
  | some beta =>
    have hi := he beta rfl
    have hne := highValue_im_ne_zero hN hrho
    constructor
    · intro h
      exact hne (h ▸ hi)
    · intro h
      apply hne
      simp [h, hi]

theorem actual_unprimed_mother_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {r : ℝ} (hr : 1 < r) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi (sourceT N)).filter
        (fun rho => omegaCutoff N q ≤ |rho.im|),
          (analyticOrderNatAt chi.LFunction rho : ℝ) *
            ((N : ℝ) ^ (rho.re - 1) / |rho.im|)) ≤ motherBound N q r := by
  simpa only [highSum, bandSum, bandValues, Applications.half_values_eq_complete] using
    highSum_le_motherBound hN hq hr

theorem actual_primed_mother_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {exceptional : Option ℂ} (he : ∀ beta, exceptional = some beta → beta.im = 0)
    {r : ℝ} (hr : 1 < r) :
    primedHighSum N q exceptional ≤ motherBound N q r := by
  rw [primedHighSum_eq_highSum hN he]
  exact highSum_le_motherBound hN hq hr

def highOscillation (N q : ℕ) [NeZero q] (eta : ℝ) : ℂ :=
  ∑ chi : Character q, ∑ rho ∈ highValues N chi,
    (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem highValue_norm_mul_Jrho_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {eta : ℝ}
    (heta : |eta| ≤ deltaRadius N q) {chi : Character q} {rho : ℂ}
    (hrho : rho ∈ highValues N chi) :
    ‖(analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      5 * (N : ℝ) * ((analyticOrderNatAt chi.LFunction rho : ℝ) *
        ((N : ℝ) ^ (rho.re - 1) / |rho.im|)) := by
  have hn := Parameters.natCast_pos_of_exp_le hN
  have hv := mem_highValues.mp hrho
  have heta' : |eta| ≤ |rho.im| / (10 * Real.pi * (N : ℝ)) := by
    rw [Parameters.deltaRadius_eq_omega] at heta
    exact heta.trans (div_le_div_of_nonneg_right hv.2.2.2.1 (by positivity))
  have hj := OscillatoryBounds.Jrho_near (Parameters.nat_pos_of_exp_le hN)
    (by linarith : 0 ≤ rho.re) (highValue_im_ne_zero hN hrho) heta'
  rw [norm_mul, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg _)).trans_eq
  rw [Real.rpow_sub_one hn.ne']
  field_simp

theorem highOscillation_le_weighted {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {eta : ℝ}
    (heta : |eta| ≤ deltaRadius N q) :
    ‖highOscillation N q eta‖ ≤ 5 * (N : ℝ) * highSum N q := by
  calc
    _ ≤ ∑ chi : Character q, ∑ rho ∈ highValues N chi,
        ‖(analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ :=
      (norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun chi _ => norm_sum_le _ _))
    _ ≤ ∑ chi : Character q, ∑ rho ∈ highValues N chi,
        5 * (N : ℝ) * ((analyticOrderNatAt chi.LFunction rho : ℝ) *
          ((N : ℝ) ^ (rho.re - 1) / |rho.im|)) :=
      Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum
        (fun _ hrho => highValue_norm_mul_Jrho_le hN heta hrho))
    _ = _ := by simp only [highSum, bandSum, highValues, Finset.mul_sum]

theorem highOscillation_le_mother {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {eta r : ℝ} (heta : |eta| ≤ deltaRadius N q) (hr : 1 < r) :
    ‖highOscillation N q eta‖ ≤ 5 * (N : ℝ) * motherBound N q r :=
  (highOscillation_le_weighted hN heta).trans
    (mul_le_mul_of_nonneg_left (highSum_le_motherBound hN hq hr) (by positivity))

end LiuWang.Proof.WeightedHighZeros
