import LiuWang.Proof.Campaign20260915.OriginalRegion.SignedCosts

/-! Exact rational phase models for the signed bad-prime contribution. -/

set_option autoImplicit false
noncomputable section

open Complex Finset
open scoped BigOperators Classical
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem levelEulerDifference_eq_sum {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    levelEulerDifference chi sigma t =
      ∑ p ∈ q.primeFactors,
        (logDeriv (levelCorrectionFactor chi p) ((sigma : ℂ) + I * t) -
          (stechkinK : ℂ) *
            logDeriv (levelCorrectionFactor chi p) ((stechkinSigma sigma : ℂ) + I * t)).re := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  rw [levelEulerDifference,
    logDeriv_levelCorrection_eq_sum chi hc (by simpa [mul_re] using hs.le),
    logDeriv_levelCorrection_eq_sum chi hc
      (by simpa [mul_re] using (hs.trans_le (stechkinSigma_ge hs)).le),
    Finset.mul_sum, ← Finset.sum_sub_distrib, Complex.re_sum]

theorem geometric_re_eq_rational (a : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    (((a : ℂ) * z) / (1 - (a : ℂ) * z)).re =
      (a * z.re - a ^ 2) / (1 - 2 * a * z.re + a ^ 2) := by
  have hs : z.re ^ 2 + z.im ^ 2 = 1 := by
    have hh := Complex.normSq_eq_norm_sq z
    rw [hz] at hh
    simpa only [Complex.normSq_apply, one_pow, sq, mul_one] using hh
  have ha := congrArg (fun r : ℝ => a ^ 2 * r) hs
  have hn : ((a : ℂ) * z).re * (1 - (a : ℂ) * z).re +
      ((a : ℂ) * z).im * (1 - (a : ℂ) * z).im = a * z.re - a ^ 2 := by
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero,
      sub_re, sub_im, one_re, one_im]
    nlinarith [ha]
  have hd : Complex.normSq (1 - (a : ℂ) * z) = 1 - 2 * a * z.re + a ^ 2 := by
    simp only [Complex.normSq_apply, mul_re, mul_im, ofReal_re, ofReal_im,
      zero_mul, sub_zero, sub_re, sub_im, one_re, one_im]
    nlinarith [ha]
  rw [Complex.div_re, ← add_div, hn, hd]

theorem factorEulerDifference_eq_rational {q p : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hp : p.Prime)
    (hu : IsUnit (p : ZMod chi.conductor)) (sigma t : ℝ) :
    let a := (p : ℝ) ^ (-sigma)
    let b := (p : ℝ) ^ (-stechkinSigma sigma)
    let z := phase chi.primitiveCharacter t p
    (logDeriv (levelCorrectionFactor chi p) ((sigma : ℂ) + I * t) -
      (stechkinK : ℂ) *
        logDeriv (levelCorrectionFactor chi p) ((stechkinSigma sigma : ℂ) + I * t)).re =
      Real.log p * ((a * z.re - a ^ 2) / (1 - 2 * a * z.re + a ^ 2) -
        stechkinK * ((b * z.re - b ^ 2) / (1 - 2 * b * z.re + b ^ 2))) := by
  dsimp only
  have hz := phase_norm chi.primitiveCharacter hp.ne_zero hu t
  have he (u : ℝ) :
      logDeriv (levelCorrectionFactor chi p) ((u : ℂ) + I * t) =
        (Real.log p : ℂ) *
          ((((p : ℝ) ^ (-u) : ℝ) : ℂ) * phase chi.primitiveCharacter t p /
            (1 - (((p : ℝ) ^ (-u) : ℝ) : ℂ) * phase chi.primitiveCharacter t p)) := by
    simp only [logDeriv_levelCorrectionFactor, levelCorrectionFactor,
      natCast_cpow_neg_add_I_mul hp.ne_zero]
    dsimp [phase]
    ring
  rw [he, he]
  have hm (u v : ℂ) : (Real.log p : ℂ) * u - (stechkinK : ℂ) * ((Real.log p : ℂ) * v) =
      (Real.log p : ℂ) * (u - (stechkinK : ℂ) * v) := by ring
  rw [hm]
  simp only [mul_re, sub_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [geometric_re_eq_rational _ hz, geometric_re_eq_rational _ hz]

theorem negative_phase_geometric_strict {a b k : ℝ}
    (hb : 0 < b) (hba : b ≤ a) (hk1 : k < 1) :
    -a / (1 + a) + k * b / (1 + b) < 0 := by
  have ha : 0 < a := hb.trans_le hba
  have hm : b / (1 + b) ≤ a / (1 + a) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hstrict : k * (b / (1 + b)) < b / (1 + b) :=
    (mul_lt_mul_of_pos_right hk1 (by positivity)).trans_eq (one_mul _)
  simpa only [neg_div, mul_div_assoc, sub_eq_neg_add] using
    sub_neg.mpr (hstrict.trans_le hm)

theorem factorEulerDifference_negative_phase {q p : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hp : p.Prime)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ)
    (hphase : phase chi.primitiveCharacter t p = -1) :
    (logDeriv (levelCorrectionFactor chi p) ((sigma : ℂ) + I * t) -
      (stechkinK : ℂ) *
        logDeriv (levelCorrectionFactor chi p) ((stechkinSigma sigma : ℂ) + I * t)).re < 0 := by
  have he (u : ℝ) :
      logDeriv (levelCorrectionFactor chi p) ((u : ℂ) + I * t) =
        (Real.log p : ℂ) * (-(((p : ℝ) ^ (-u) : ℝ) : ℂ) /
          (1 + (((p : ℝ) ^ (-u) : ℝ) : ℂ))) := by
    simp only [logDeriv_levelCorrectionFactor, levelCorrectionFactor,
      natCast_cpow_neg_add_I_mul hp.ne_zero]
    have hh : chi.primitiveCharacter p * (p : ℂ) ^ (-(I * (t : ℂ))) = -1 := hphase
    calc
      _ = (Real.log p : ℂ) *
          ((((p : ℝ) ^ (-u) : ℝ) : ℂ) *
            (chi.primitiveCharacter p * (p : ℂ) ^ (-(I * (t : ℂ)))) /
          (1 - (((p : ℝ) ^ (-u) : ℝ) : ℂ) *
            (chi.primitiveCharacter p * (p : ℂ) ^ (-(I * (t : ℂ)))))) := by ring
      _ = _ := by rw [hh]; ring
  rw [he, he]
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hneg := negative_phase_geometric_strict
    (Real.rpow_pos_of_pos hpos (-stechkinSigma sigma))
    (primePower_parameters hp hs).2.1
    (lt_of_le_of_lt stechkinK_le (by norm_num))
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hm := mul_neg_of_pos_of_neg hlog hneg
  simp only [← ofReal_neg, ← ofReal_one, ← ofReal_add, ← ofReal_div,
    ← ofReal_mul, ← ofReal_sub, ofReal_re]
  ring_nf at hm ⊢
  exact hm

end LiuWang.Proof.Campaign20260915.OriginalRegion
