import LiuWang.Proof.Campaign20260915.ZetaWinding.TuringEndpoints

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaGramBlocks

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding

def IsGramPoint (n : ℤ) (t : ℝ) : Prop :=
  criticalGammaArgument t = n * Real.pi

def signedZ (n : ℤ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * normalizedCriticalZeta t

def IsGoodGramPoint (n : ℤ) (t : ℝ) : Prop :=
  IsGramPoint n t ∧ 0 < signedZ n t

theorem gram_sign_sq (n : ℤ) : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
  rw [← mul_zpow]
  norm_num

theorem phase_at_gram {n : ℤ} {t : ℝ} (hg : IsGramPoint n t) :
    criticalGammaPhase t = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by
  rw [criticalGammaPhase_eq_exp_argument, hg]
  push_cast
  rw [mul_assoc, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem signedZ_at_gram {n : ℤ} {t : ℝ} (hg : IsGramPoint n t) :
    signedZ n t = (riemannZeta (criticalPoint t)).re := by
  have h := congrArg Complex.re (normalizedCriticalZeta_ofReal t)
  rw [phase_at_gram hg] at h
  simp only [ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero] at h
  rw [signedZ, h]
  calc
    _ = (riemannZeta (criticalPoint t)).re * ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) := by ring
    _ = _ := by rw [gram_sign_sq, mul_one]

theorem goodGram_iff_positive_zeta_re {n : ℤ} {t : ℝ} (hg : IsGramPoint n t) :
    IsGoodGramPoint n t ↔ 0 < (riemannZeta (criticalPoint t)).re := by
  simp only [IsGoodGramPoint, hg, true_and, signedZ_at_gram hg]

theorem goodGram_critical_ne_zero {n : ℤ} {t : ℝ} (hg : IsGoodGramPoint n t) :
    riemannZeta (criticalPoint t) ≠ 0 := by
  have hp := (goodGram_iff_positive_zeta_re hg.1).mp hg
  intro hz
  simp [hz] at hp

theorem exists_gram_in_Ioo {n : ℤ} {a b : ℝ} (hab : a < b)
    (ha : criticalGammaArgument a < n * Real.pi)
    (hb : n * Real.pi < criticalGammaArgument b) :
    ∃ t ∈ Set.Ioo a b, IsGramPoint n t := by
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc hab.le
    criticalGammaArgument_continuous.continuousOn ⟨ha.le, hb.le⟩
  refine ⟨t, ⟨?_, ?_⟩, he⟩
  · by_contra hn
    have ht' : t = a := le_antisymm (not_lt.mp hn) ht.1
    subst t
    linarith
  · by_contra hn
    have ht' : t = b := le_antisymm ht.2 (not_lt.mp hn)
    subst t
    linarith

theorem exists_gram_of_phase_approximations {n : ℤ} {a b : ℝ} (hab : a < b)
    {Na Nb : ℕ} (hNa : 1 ≤ Na) (hNb : 1 ≤ Nb)
    (hza : 2 * ‖criticalPoint a / 2‖ ≤ (Na : ℝ))
    (hzb : 2 * ‖criticalPoint b / 2‖ ≤ (Nb : ℝ))
    (ha : criticalGammaArgumentApprox a Na +
      (‖criticalPoint a / 2‖ + ‖criticalPoint a / 2‖ ^ 2) / Na < n * Real.pi)
    (hb : n * Real.pi < criticalGammaArgumentApprox b Nb -
      (‖criticalPoint b / 2‖ + ‖criticalPoint b / 2‖ ^ 2) / Nb) :
    ∃ t ∈ Set.Ioo a b, IsGramPoint n t := by
  have hea := abs_le.mp (criticalGammaArgument_error a hNa hza)
  have heb := abs_le.mp (criticalGammaArgument_error b hNb hzb)
  exact exists_gram_in_Ioo hab (by linarith [hea.2]) (by linarith [heb.1])

theorem goodGram_of_uniform_enclosure {n : ℤ} {a b t c e : ℝ}
    (ht : t ∈ Set.Icc a b) (hg : IsGramPoint n t)
    (he : ∀ u ∈ Set.Icc a b, |normalizedCriticalZeta u - c| ≤ e)
    (hc : e < (-1 : ℝ) ^ n * c) :
    IsGoodGramPoint n t := by
  have herr : |signedZ n t - (-1 : ℝ) ^ n * c| ≤ e := by
    rw [signedZ, ← mul_sub, abs_mul, abs_neg_one_zpow, one_mul]
    exact he t ht
  exact ⟨hg, by linarith [(abs_le.mp herr).1]⟩

theorem completed_sign_change_of_normalized {a b : ℝ}
    (hs : normalizedCriticalZeta a * normalizedCriticalZeta b < 0) :
    criticalCompletedZeta a * criticalCompletedZeta b < 0 := by
  rw [normalizedCriticalZeta, normalizedCriticalZeta, div_mul_div_comm,
    div_lt_iff₀ (mul_pos (criticalGammaNorm_pos a) (criticalGammaNorm_pos b)),
    zero_mul] at hs
  exact hs

theorem consecutive_goodGram_sign_change {n : ℤ} {a b : ℝ}
    (ha : IsGoodGramPoint n a) (hb : IsGoodGramPoint (n + 1) b) :
    criticalCompletedZeta a * criticalCompletedZeta b < 0 := by
  apply completed_sign_change_of_normalized
  have hp := mul_pos ha.2 hb.2
  have hs : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by
    rw [zpow_add₀ (by norm_num), zpow_one]
    ring
  dsimp [signedZ] at hp
  rw [hs] at hp
  have he : ((-1 : ℝ) ^ n * normalizedCriticalZeta a) *
      (-((-1 : ℝ) ^ n) * normalizedCriticalZeta b) =
      -(normalizedCriticalZeta a * normalizedCriticalZeta b) := by
    calc
      _ = -(((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        (normalizedCriticalZeta a * normalizedCriticalZeta b)) := by ring
      _ = _ := by rw [gram_sign_sq, one_mul]
  rw [he] at hp
  linarith

theorem turingS_at_gram {n : ℤ} {t : ℝ} (hg : IsGramPoint n t) :
    turingS t = (positiveCount t : ℝ) - 1 - n := by
  rw [turingS, hg, mul_div_cancel_right₀ _ Real.pi_ne_zero]

theorem turingSLeft_at_gram {n : ℤ} {t : ℝ} (hg : IsGramPoint n t) :
    turingSLeft t = (positiveCountLeft t : ℝ) - 1 - n := by
  rw [turingSLeft, hg, mul_div_cancel_right₀ _ Real.pi_ne_zero]

theorem gram_left_upper_iff {n : ℤ} {t : ℝ} (hg : IsGramPoint n t) :
    (positiveCountLeft t : ℝ) ≤ n + 1 ↔ turingSLeft t ≤ 0 := by
  rw [turingSLeft_at_gram hg]
  constructor <;> intro h <;> linarith

theorem gram_closed_upper_iff {n : ℤ} {t : ℝ} (hg : IsGramPoint n t) :
    (positiveCount t : ℝ) ≤ n + 1 ↔ turingS t ≤ 0 := by
  rw [turingS_at_gram hg]
  constructor <;> intro h <;> linarith

theorem gram_left_lower_iff {n : ℤ} {t : ℝ} (hg : IsGramPoint n t) :
    n + 1 ≤ (positiveCountLeft t : ℝ) ↔ 0 ≤ turingSLeft t := by
  rw [turingSLeft_at_gram hg]
  constructor <;> intro h <;> linarith

theorem gram_closed_lower_iff {n : ℤ} {t : ℝ} (hg : IsGramPoint n t) :
    n + 1 ≤ (positiveCount t : ℝ) ↔ 0 ≤ turingS t := by
  rw [turingS_at_gram hg]
  constructor <;> intro h <;> linarith

#print axioms exists_gram_of_phase_approximations
#print axioms goodGram_of_uniform_enclosure
#print axioms consecutive_goodGram_sign_change
#print axioms gram_left_upper_iff
#print axioms gram_closed_lower_iff

end LiuWang.Proof.Campaign20260915.ZetaGramBlocks
