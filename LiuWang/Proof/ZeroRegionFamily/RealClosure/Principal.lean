import LiuWang.Proof.ZeroRegionFamily.RealClosure.Quadratic

/-! # ζ实际选中反射对给R20主分支；普通主字符极点明确排除 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.ZeroRegionFamily.RealClosure

theorem xi_selected_pair_le (p : RiemannXiDivisorZeroIndex)
    (hr : 1/2 < (riemannXiDivisorZeroValue p).re)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    dampedZeroKernel sigma t (riemannXiDivisorZeroValue p)+
      dampedZeroKernel sigma t (1-(starRingEnd ℂ) (riemannXiDivisorZeroValue p)) ≤
        zetaZeroSum sigma t := by
  classical
  let f := fun j : RiemannXiDivisorZeroIndex =>
    dampedZeroKernel sigma t (riemannXiDivisorZeroValue j)
  let e := xiReflection
  let g := fun j => f j+f (e j)
  have h0 : 1 ≤ ((sigma : ℂ)+I*t).re := by simpa [Complex.mul_re] using hs.le
  have h1 : 1 ≤ ((stechkinSigma sigma : ℂ)+I*t).re := by
    simpa [Complex.mul_re] using (hs.trans_le (stechkinSigma_ge hs)).le
  have hsum : Summable f := (xi_raw_summable h0).sub ((xi_raw_summable h1).mul_left stechkinK)
  have hcomp : Summable (fun j => f (e j)) := e.summable_iff.mpr hsum
  have hnon : ∀ j, 0 ≤ g j := by
    intro j
    exact dampedZeroKernel_pair_nonneg hs t
      ⟨(riemannXiDivisorZeroValue_re_mem_Ioo j).1.le,
        (riemannXiDivisorZeroValue_re_mem_Ioo j).2.le⟩
  have hne : p ≠ e p := by
    intro he
    have hh := congrArg (fun j => (riemannXiDivisorZeroValue j).re) he
    change (riemannXiDivisorZeroValue p).re =
      (1-(starRingEnd ℂ) (riemannXiDivisorZeroValue p)).re at hh
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hh
    linarith
  have hge : g (e p)=g p := by
    have hee : e (e p)=p := xiReflect_involutive p
    dsimp [g]
    rw [hee]
    ring
  have hselected := (hsum.add hcomp).sum_le_tsum {p, e p} (fun j _ => hnon j)
  change ∑ j ∈ ({p, e p} : Finset _), g j ≤ ∑' j, g j at hselected
  rw [Finset.sum_pair hne, hge] at hselected
  have htotal : (∑' j, g j)=2*∑' j, f j := by
    dsimp [g]
    rw [hsum.tsum_add hcomp, e.tsum_eq f]
    ring
  rw [htotal] at hselected
  change g p ≤ ∑' j, f j
  linarith

theorem zeta_selected_high (p : RiemannXiDivisorZeroIndex)
    (hr : 1/2 < (riemannXiDivisorZeroValue p).re)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    zetaDamped sigma (riemannXiDivisorZeroValue p).im+
      1/(sigma-(riemannXiDivisorZeroValue p).re) ≤
      stechkinConductorCoeff*(Real.log |(riemannXiDivisorZeroValue p).im|-Real.log Real.pi)+
        23/40-11*stechkinK/30 := by
  have ht := (xi_zero_height_gt_one p).le
  have hsel := xi_selected_pair_le p hr hs (riemannXiDivisorZeroValue p).im
  have hpair := selected_pair_dominates hs (riemannXiDivisorZeroValue_re_mem_Ioo p)
  have hid := zeta_full_zero_sum_identity hs (riemannXiDivisorZeroValue p).im
  have hg := shiftedGamma_all_height hs hs1 (riemannXiDivisorZeroValue p).im
  rw [max_eq_right ht] at hg
  linarith [poleDifference_high_nonpos hs hs1 ht]

theorem zeta_high {sigma t : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20)
    (ht : 1 ≤ |t|) :
    zetaDamped sigma t ≤ stechkinConductorCoeff*(Real.log |t|-Real.log Real.pi)+
      23/40-11*stechkinK/30 := by
  have hh := zeta_damped_pole_bound hs t
  have hg := shiftedGamma_all_height hs hs1 t
  rw [max_eq_right ht] at hg
  linarith [poleDifference_high_nonpos hs hs1 ht]

theorem zeta_core (p : RiemannXiDivisorZeroIndex)
    (hr : 1/2 < (riemannXiDivisorZeroValue p).re)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    4/(sigma-(riemannXiDivisorZeroValue p).re) ≤ 3/(sigma-1)+
      5*stechkinConductorCoeff*Real.log |(riemannXiDivisorZeroValue p).im| := by
  let t := (riemannXiDivisorZeroValue p).im
  have ht : 1 ≤ |t| := (xi_zero_height_gt_one p).le
  have hpos := stechkin_combination_nonneg (1 : DirichletCharacter ℂ 1) hs t
  simp only [one_pow, dampedLogDeriv, DirichletCharacter.LFunction_modOne_eq] at hpos
  change 0 ≤ 3*zetaDamped sigma 0+4*zetaDamped sigma t+zetaDamped sigma (2*t) at hpos
  have hmain := zeta_selected_high p hr hs hs1
  have hreal := zeta_real_strong hs hs1
  have ht2 : 1 ≤ |2*t| := by rw [abs_mul]; norm_num; linarith
  have hhigh := zeta_high hs hs1 ht2
  have hlog := log_max_double_le t
  rw [max_eq_right ht, max_eq_right ht2] at hlog
  have hlog' := mul_le_mul_of_nonneg_left hlog conductorCoeff_bounds.1
  have hc : stechkinConductorCoeff*(Real.log 2-5*Real.log Real.pi) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos conductorCoeff_bounds.1
      (by linarith [Real.log_two_lt_d9, log_pi_ge_one])
  have hk := stechkinK_ge
  change zetaDamped sigma t+_ ≤ _ at hmain
  change 4/(sigma-(riemannXiDivisorZeroValue p).re) ≤
    3/(sigma-1)+5*stechkinConductorCoeff*Real.log |t|
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem zeta_no_zero_twenty {x : ℝ} (hx : 10 ≤ x) {rho : ℂ}
    (hr : 1-1/(20*Real.log x) < rho.re) (ht : |rho.im| ≤ x) : riemannZeta rho ≠ 0 := by
  have hL := log_scale_ge hx
  have hw : 1/(20*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  intro hz
  obtain ⟨p, hv⟩ := exists_xi_index_of_zeta_zero (by linarith) hz
  have hb := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
  rw [hv] at hb
  have hh := finite_gap_of_log_core hx hb (fun sigma hs hs1 => ?_)
  · linarith
  · have hc := zeta_core p (by simpa only [hv] using (show 1/2 < rho.re by linarith)) hs hs1
    rw [hv] at hc
    have hh := xi_zero_height_gt_one p
    rw [hv] at hh
    have hl := Real.log_le_log (by linarith) ht
    have hm := mul_le_mul_of_nonneg_left hl
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) conductorCoeff_bounds.1)
    linarith

theorem principal_no_zero_twenty {x : ℝ} {q : ℕ} [NeZero q] (hx : 10 ≤ x)
    {rho : ℂ} (hr : 1-1/(20*Real.log x) < rho.re)
    (ht : |rho.im| ≤ x/(q : ℝ)) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction rho ≠ 0 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hheight : |rho.im| ≤ x := ht.trans
    ((div_le_self (by linarith) hq))
  have hL := log_scale_ge hx
  have hw : 1/(20*Real.log x) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  exact fun hz => zeta_no_zero_twenty hx hr hheight
    ((PrincipalPsi.principal_zero_iff_zeta_zero (by linarith) hpole).mp hz)

end LiuWang.Proof.ZeroRegionFamily.RealClosure
