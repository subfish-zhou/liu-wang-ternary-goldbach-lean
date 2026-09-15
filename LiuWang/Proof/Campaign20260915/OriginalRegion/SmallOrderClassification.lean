import LiuWang.Proof.Campaign20260915.OriginalRegion.FourthOrderLow

/-! Source-free classification only for the stated low-height order-three/order-four subfamily. -/

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem small_order_low_classification {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    (horder : chi ^ 3 = 1 ∨ chi ^ 4 = 1) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) < rho.re) (hr1 : rho.re < 1)
    (ht : Real.log x * |rho.im| ≤ 1 / 8) (hz : chi.LFunction rho = 0) :
    chi ≠ 1 ∧ chi ^ 2 = 1 ∧ rho.im = 0 ∧ analyticOrderNatAt chi.LFunction rho = 1 := by
  have hlog := log_scale_ge_34_15 hx
  have hL : 0 < Real.log x := by linarith
  have hw : 1 / (9.645908801 * Real.log x) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hc : chi ≠ 1 := by
    intro he
    subst chi
    have hne : rho ≠ 1 := by intro hh; simp [hh] at hr1
    have hzeta := (PrincipalPsi.principal_zero_iff_zeta_zero (by linarith) hne).mp hz
    obtain ⟨p, hp⟩ := exists_xi_index_of_zeta_zero (by linarith) hzeta
    have hheight := xi_zero_height_gt_one p
    rw [hp] at hheight
    nlinarith [abs_nonneg rho.im]
  have h2 : chi ^ 2 = 1 := by
    rcases horder with h3 | h4
    · exact False.elim (ordinary_low_height_original hx hq chi hc hr
        (Or.inl ⟨h3, by linarith⟩) hz)
    · by_contra hn
      exact ordinary_fourth_order_low_original hx hq chi h4 hn hr ht hz
  have him : rho.im = 0 := by
    by_contra hi
    exact ordinary_low_height_original hx hq chi hc hr
      (Or.inr ⟨h2, hi, by linarith⟩) hz
  have he : (rho.re : ℂ) = rho := by
    apply Complex.ext <;> simp [him]
  have hg : 1 - rho.re < 1 / (8 * Real.log x) := by
    have hh : 1 / (9.645908801 * Real.log x) ≤ 1 / (8 * Real.log x) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hm := ordinary_real_zero_simple_eight hx hq chi hc hg (by simpa only [he] using hz)
  rw [he] at hm
  exact ⟨hc, h2, him, hm⟩

theorem small_order_low_zeros_equal {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi psi : DirichletCharacter ℂ q)
    (hc : chi ^ 3 = 1 ∨ chi ^ 4 = 1) (hp : psi ^ 3 = 1 ∨ psi ^ 4 = 1)
    {rho tau : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) < rho.re) (hr1 : rho.re < 1)
    (hs : 1 - 1 / (9.645908801 * Real.log x) < tau.re) (hs1 : tau.re < 1)
    (ht : Real.log x * |rho.im| ≤ 1 / 8) (hu : Real.log x * |tau.im| ≤ 1 / 8)
    (hz : chi.LFunction rho = 0) (hw : psi.LFunction tau = 0) :
    chi = psi ∧ rho = tau := by
  obtain ⟨hc0, hc2, hi, _⟩ := small_order_low_classification hx hq chi hc hr hr1 ht hz
  obtain ⟨hp0, hp2, hj, _⟩ := small_order_low_classification hx hq psi hp hs hs1 hu hw
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  have hf : (tau.re : ℂ) = tau := by apply Complex.ext <;> simp [hj]
  obtain ⟨d, _, _, _, hd, _, _, hall⟩ :=
    real_family_fixed_source_original hx hq chi hc0 hc2 (beta := rho.re) (by linarith)
      (by simpa only [he] using hz)
  obtain ⟨heq, _, _, hd', _⟩ := hall q hq psi tau.re hp0 hp2 (by linarith)
    (by simpa only [hf] using hw)
  refine ⟨hd.symm.trans hd', ?_⟩
  rw [← he, ← hf, heq]

def SmallOrderLowZeros (x : ℝ) (q : ℕ) [NeZero q] :=
  Σ z : {z : DirichletCharacter ℂ q × ℂ //
    (z.1 ^ 3 = 1 ∨ z.1 ^ 4 = 1) ∧
    1 - 1 / (9.645908801 * Real.log x) < z.2.re ∧ z.2.re < 1 ∧
    Real.log x * |z.2.im| ≤ 1 / 8 ∧ z.1.LFunction z.2 = 0},
    Fin (analyticOrderNatAt z.val.1.LFunction z.val.2)

theorem smallOrderLowZeros_subsingleton {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) : Subsingleton (SmallOrderLowZeros x q) := by
  refine ⟨?_⟩
  rintro ⟨z, i⟩ ⟨w, j⟩
  have hc := z.property
  have hp := w.property
  have he := small_order_low_zeros_equal hx hq z.val.1 w.val.1 hc.1 hp.1
    hc.2.1 hc.2.2.1 hp.2.1 hp.2.2.1 hc.2.2.2.1 hp.2.2.2.1
    hc.2.2.2.2 hp.2.2.2.2
  have hzw : z = w := Subtype.ext (Prod.ext he.1 he.2)
  subst w
  have hm := (small_order_low_classification hx hq z.val.1 hc.1 hc.2.1 hc.2.2.1
    hc.2.2.2.1 hc.2.2.2.2).2.2.2
  have hij : i = j := by
    apply Fin.ext
    have hi : i.val < 1 := lt_of_lt_of_le i.isLt hm.le
    have hj : j.val < 1 := lt_of_lt_of_le j.isLt hm.le
    omega
  subst j
  rfl

end LiuWang.Proof.Campaign20260915.OriginalRegion
