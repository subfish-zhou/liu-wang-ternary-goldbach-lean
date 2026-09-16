import LiuWang.Proof.Campaign20260915.ZetaGramBlocks.GramPoints
import LiuWang.Proof.Campaign20260915.ZetaWinding.LehmanGammaBudget

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaGramBlocks

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding

def gramSlope (t : ℝ) : ℝ :=
  ((digamma (criticalPoint t / 2)).re - Real.log Real.pi) / 2

theorem criticalGammaArgument_hasDerivAt (t : ℝ) :
    HasDerivAt criticalGammaArgument (gramSlope t) t := by
  have hp : HasDerivAt (fun u : ℝ => criticalPoint u / 2) (I / 2) t := by
    convert! (((hasDerivAt_const t (1 / 2 : ℂ)).add
      (Complex.ofRealCLM.hasDerivAt.mul_const I)).div_const (2 : ℂ)) using 1
    · funext u
      congr 1
      apply Complex.ext <;> simp [criticalPoint]
    · simp
  have hg := (LiuWang.Proof.DirichletZeroCount.Remainder.logGamma_hasDerivAt
    (z := criticalPoint t / 2) (by norm_num [criticalPoint])).scomp t hp
  have hd := hg.sub (hp.mul_const (Real.log Real.pi : ℂ))
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd
  convert! hi using 1
  simp [gramSlope, smul_eq_mul, mul_im]
  ring

theorem gramSlope_lower {t : ℝ} (ht : 16 ≤ t) : 1 / 8 < gramSlope t := by
  have ht0 : 0 < t := by linarith
  have he := digamma_re_log_im_error (z := criticalPoint t / 2)
    (by norm_num [criticalPoint]) (by norm_num [criticalPoint])
    (by simp [criticalPoint]; linarith)
  have he' : |(digamma (criticalPoint t / 2)).re - Real.log (t / 2)| ≤
      129 / (8 * t ^ 2) := by
    convert! he using 1 <;> simp [criticalPoint]
    congr 1
    ring
  have hsmall : 129 / (8 * t ^ 2) < (1 / 4 : ℝ) := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg (t - 16)]
  have hlog := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
    (show 2 * Real.pi ≤ t / 2 by linarith [Real.pi_lt_four])
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero] at hlog
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  dsimp [gramSlope]
  linarith [(abs_le.mp he').1]

theorem criticalGammaArgument_strictMono :
    StrictMonoOn criticalGammaArgument (Set.Ici 16) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 16)
    criticalGammaArgument_continuous.continuousOn
    (fun t _ => (criticalGammaArgument_hasDerivAt t).hasDerivWithinAt)
  intro t ht
  have ht' : 16 ≤ t := interior_subset ht
  linarith [gramSlope_lower ht']

theorem criticalGammaArgument_growth {t : ℝ} (ht : 16 ≤ t) :
    criticalGammaArgument 16 + (t - 16) / 8 ≤ criticalGammaArgument t := by
  have hm : StrictMonoOn (fun u => criticalGammaArgument u - u / 8) (Set.Ici 16) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 16)
      (criticalGammaArgument_continuous.sub (continuous_id.div_const 8)).continuousOn
      (fun u _ => ((criticalGammaArgument_hasDerivAt u).sub
        ((hasDerivAt_id u).div_const 8)).hasDerivWithinAt)
    intro u hu
    have hu' : 16 ≤ u := interior_subset hu
    simpa using sub_pos.mpr (gramSlope_lower hu')
  have h := hm.monotoneOn (by norm_num : (16 : ℝ) ∈ Set.Ici 16) ht ht
  linarith

theorem exists_unique_gram_above_sixteen (n : ℕ) :
    ∃! t : ℝ, 16 < t ∧ IsGramPoint (n : ℤ) t := by
  let b : ℝ := 16 + 8 * ((n : ℝ) * Real.pi + 2)
  have hn : 0 ≤ (n : ℝ) * Real.pi := by positivity
  have hb : 16 < b := by dsimp [b]; linarith
  have hgrowth := criticalGammaArgument_growth hb.le
  obtain ⟨t, ht, hg⟩ := exists_gram_in_Ioo (n := (n : ℤ)) hb
    (by push_cast; linarith [gamma16_argument_rational_enclosure.2])
    (by push_cast; dsimp [b] at hgrowth; linarith [gamma16_argument_rational_enclosure.1])
  refine ⟨t, ⟨ht.1, hg⟩, ?_⟩
  intro u hu
  apply criticalGammaArgument_strictMono.injOn hu.1.le ht.1.le
  exact hu.2.trans hg.symm

def gramPoint (n : ℕ) : ℝ :=
  (exists_unique_gram_above_sixteen n).exists.choose

theorem gramPoint_gt_sixteen (n : ℕ) : 16 < gramPoint n :=
  (exists_unique_gram_above_sixteen n).exists.choose_spec.1

theorem gramPoint_phase (n : ℕ) : IsGramPoint (n : ℤ) (gramPoint n) :=
  (exists_unique_gram_above_sixteen n).exists.choose_spec.2

theorem gramPoint_strictMono : StrictMono gramPoint := by
  intro n m hnm
  by_contra hn
  have hle : gramPoint m ≤ gramPoint n := not_lt.mp hn
  have hp := criticalGammaArgument_strictMono.monotoneOn
    (gramPoint_gt_sixteen m).le (gramPoint_gt_sixteen n).le hle
  rw [gramPoint_phase m, gramPoint_phase n] at hp
  have hnm' : (n : ℝ) < m := by exact_mod_cast hnm
  push_cast at hp
  nlinarith [Real.pi_pos]

theorem gramPoint_mem_of_phase_bracket {n : ℕ} {a b : ℝ} (ha16 : 16 ≤ a)
    (hab : a < b) (ha : criticalGammaArgument a < (n : ℝ) * Real.pi)
    (hb : (n : ℝ) * Real.pi < criticalGammaArgument b) :
    gramPoint n ∈ Set.Ioo a b := by
  obtain ⟨t, ht, hg⟩ := exists_gram_in_Ioo (n := (n : ℤ)) hab
    (by simpa using ha) (by simpa using hb)
  have he : t = gramPoint n := criticalGammaArgument_strictMono.injOn
    (ha16.trans ht.1.le) (gramPoint_gt_sixteen n).le (hg.trans (gramPoint_phase n).symm)
  rwa [he] at ht

#print axioms criticalGammaArgument_hasDerivAt
#print axioms criticalGammaArgument_strictMono
#print axioms exists_unique_gram_above_sixteen
#print axioms gramPoint_strictMono
#print axioms gramPoint_mem_of_phase_bracket

end LiuWang.Proof.Campaign20260915.ZetaGramBlocks
