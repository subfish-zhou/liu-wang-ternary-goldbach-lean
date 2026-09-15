import LiuWang.Proof.DirichletZeroCount.Argument.GammaVertical

/-! # The Euler-limit logarithm of Gamma and the actual archimedean integral -/

set_option autoImplicit false
noncomputable section
open Complex Filter MeasureTheory
open scoped Topology ComplexConjugate

namespace LiuWang.Proof.DirichletZeroCount.Remainder

def logGamma (z : ℂ) : ℂ := limUnder atTop (logGammaSeq z)

theorem logGamma_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (logGammaSeq z) atTop (𝓝 (logGamma z)) :=
  (cauchySeq_logGammaSeq hz).tendsto_limUnder

theorem exp_logGamma {z : ℂ} (hz : 0 < z.re) : exp (logGamma z) = Gamma z := by
  have ht := (continuous_exp.tendsto _).comp (logGamma_tendsto hz)
  have he : Tendsto (GammaSeq z) atTop (𝓝 (exp (logGamma z))) := by
    apply ht.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact exp_logGammaSeq hz hn
  exact tendsto_nhds_unique he (GammaSeq_tendsto_Gamma z)

theorem logGammaSeq_hasDerivAt {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    HasDerivAt (fun w => logGammaSeq w n)
      ((Real.log n : ℂ) - ∑ m ∈ Finset.range (n + 1), (z + m)⁻¹) z := by
  have h1 : HasDerivAt (fun w : ℂ => w * (Real.log n : ℂ) + (Real.log n.factorial : ℂ))
      (Real.log n : ℂ) z := (hasDerivAt_mul_const _).add_const _
  have h2 : HasDerivAt (fun w : ℂ => ∑ m ∈ Finset.range (n + 1), log (w + m))
      (∑ m ∈ Finset.range (n + 1), (z + m)⁻¹) z := by
    apply HasDerivAt.fun_sum
      (A := fun (m : ℕ) (w : ℂ) => log (w + m)) (A' := fun m : ℕ => (z + m)⁻¹)
    intro m _
    have hs : z + (m : ℂ) ∈ slitPlane := by
      apply mem_slitPlane_iff.mpr
      left
      simp only [add_re, natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) m]
    simpa using! (hasDerivAt_log hs).comp z ((hasDerivAt_id z).add_const (m : ℂ))
  simpa only [logGammaSeq] using! h1.sub h2

theorem logGamma_hasDerivAt {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt logGamma (digamma z) z := by
  let a : ℝ := min (z.re / 2) 1
  let R : ℝ := ‖z‖ + 1
  let U : Set ℂ := {w | a < w.re} ∩ {w | ‖w‖ < R}
  have ha : 0 < a := lt_min (by linarith) one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have haz : a < z.re := (min_le_left (z.re / 2) 1).trans_lt (by linarith)
  have hzU : z ∈ U := ⟨haz, by dsimp [R]; linarith⟩
  have hpos (w : ℂ) (hw : w ∈ U) : 0 < w.re := ha.trans hw.1
  have hmajor : Summable (fun m : ℕ => (R + 1) / (a * ((m : ℝ) + 1) ^ 2)) := by
    refine (summable_one_div_natCast_add_one_sq.mul_left ((R + 1) / a)).congr fun m => ?_
    rw [mul_one_div, div_div]
  have hM : TendstoUniformlyOn
      (fun (N : ℕ) (w : ℂ) => ∑ m ∈ Finset.range N, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹))
      (fun (w : ℂ) => ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹)) atTop U :=
    tendstoUniformlyOn_tsum_nat hmajor fun m w hw =>
      norm_inv_add_one_sub_inv_le ha ha1 hw.1.le hw.2.le m
  have hM1 : TendstoUniformlyOn
      (fun (n : ℕ) (w : ℂ) => ∑ m ∈ Finset.range (n + 1), (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹))
      (fun (w : ℂ) => ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹)) atTop U := by
    intro u hu
    exact (tendsto_add_atTop_nat 1).eventually (hM u hu)
  have hcR : Tendsto (fun n : ℕ => Real.log n - (harmonic n : ℝ) - ((n : ℝ) + 1)⁻¹)
      atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h1 : Tendsto (fun n : ℕ => Real.log n - (harmonic n : ℝ)) atTop
        (𝓝 (-Real.eulerMascheroniConstant)) :=
      Real.tendsto_harmonic_sub_log.neg.congr fun n => by ring
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      Tendsto.inv_tendsto_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa using h1.sub h2
  have hcC : Tendsto (fun n : ℕ => ((Real.log n - (harmonic n : ℝ) - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ))
      atTop (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
    simpa only [ofReal_neg, Function.comp_def] using (continuous_ofReal.tendsto _).comp hcR
  have hF : TendstoUniformlyOn
      (fun (n : ℕ) (w : ℂ) => (Real.log n : ℂ) - ∑ m ∈ Finset.range (n + 1), (w + m)⁻¹)
      (fun w : ℂ => -(Real.eulerMascheroniConstant : ℂ) +
        ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹)) atTop U := by
    refine ((hcC.tendstoUniformlyOn_const U).add hM1).congr ?_
    filter_upwards with n
    intro w _
    simp only [Pi.add_apply]
    rw [Finset.sum_sub_distrib, sum_inv_natCast_add_one (n + 1)]
    push_cast [harmonic_succ]
    ring
  have hd := hasDerivAt_of_tendstoUniformlyOn hU hF
    (Eventually.of_forall fun n w hw => logGammaSeq_hasDerivAt (hpos w hw) n)
    (fun w hw => logGamma_tendsto (hpos w hw)) hzU
  have hs := (hasSum_digamma_of_re_pos hz).tsum_eq
  convert! hd using 1
  linear_combination -hs

theorem logGamma_conjugate {z : ℂ} (hz : 0 < z.re) :
    logGamma (conj z) = conj (logGamma z) := by
  have he (n : ℕ) : logGammaSeq (conj z) n = conj (logGammaSeq z n) := by
    simp only [logGammaSeq, map_sub, map_add, map_mul, conj_ofReal, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    have hp : 0 < (z + (m : ℂ)).re := by
      simp only [add_re, natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have harg : (z + (m : ℂ)).arg ≠ Real.pi := by
      intro h
      have hh := (arg_eq_pi_iff.mp h).1
      linarith
    simpa only [map_add, conj_natCast] using log_conj (z + m) harg
  exact tendsto_nhds_unique (logGamma_tendsto (by simpa using hz))
    (((continuous_conj.tendsto _).comp (logGamma_tendsto hz)).congr (fun n => (he n).symm))

theorem digammaVertical_eq_logGamma {a H : ℝ} (ha : 0 < a) :
    Argument.digammaVertical a H = 2 * (logGamma (((a : ℂ) + (H : ℂ) * I) / 2)).im := by
  have hd (t : ℝ) :
      HasDerivAt (fun x : ℝ => logGamma (((a : ℂ) + (x : ℂ) * I) / 2))
        ((I / 2) * digamma (((a : ℂ) + (t : ℂ) * I) / 2)) t := by
    have hp : 0 < (((a : ℂ) + (t : ℂ) * I) / 2).re := by
      simpa using half_pos ha
    have hline : HasDerivAt (fun x : ℝ => ((a : ℂ) + (x : ℂ) * I) / 2) (I / 2) t := by
      convert! ((hasDerivAt_const t (a : ℂ)).add
        ((Complex.ofRealCLM.hasDerivAt).mul_const I)).div_const (2 : ℂ) using 1
      simp
    simpa only [smul_eq_mul, Function.comp_def] using (logGamma_hasDerivAt hp).scomp t hline
  have hre (t : ℝ) : HasDerivAt (fun x : ℝ => (logGamma (((a : ℂ) + (x : ℂ) * I) / 2)).im)
      ((1 / 2) * (digamma (((a : ℂ) + (t : ℂ) * I) / 2)).re) t := by
    simpa using! Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hd t)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hre t) ((Argument.digammaVertical_integrable ha H).const_mul (1 / 2))
  have hz : (((a : ℂ) + (-H : ℝ) * I) / 2) = conj (((a : ℂ) + (H : ℂ) * I) / 2) := by
    simp only [map_div₀, map_add, map_mul, conj_ofReal, conj_I, map_ofNat, ofReal_neg]
    ring
  rw [intervalIntegral.integral_const_mul, hz,
    logGamma_conjugate (by simpa using half_pos ha), conj_im] at he
  dsimp [Argument.digammaVertical]
  linarith

end LiuWang.Proof.DirichletZeroCount.Remainder
