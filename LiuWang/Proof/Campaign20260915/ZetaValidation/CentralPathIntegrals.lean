import LiuWang.Proof.Campaign20260915.ZetaValidation.CentralPathMembership

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory
open scoped Interval

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsCentralPrimitive (s : ℂ) (m : ℕ) : ℂ → ℂ :=
  Classical.choose (rsCentralDomain_exact s m)

theorem rsCentralPrimitive_deriv (s : ℂ) (m : ℕ) {z : ℂ} (hz : z ∈ rsCentralDomain m) :
    HasDerivAt (rsCentralPrimitive s m) (rsHankelKernel s m z) z :=
  Classical.choose_spec (rsCentralDomain_exact s m) z hz

theorem rsCentral_path_integral (s : ℂ) (m : ℕ) {a b : ℝ} {γ δ : ℝ → ℂ}
    (hγ : ∀ t ∈ uIcc a b, γ t ∈ rsCentralDomain m)
    (hd : ∀ t ∈ uIcc a b, HasDerivAt γ (δ t) t) (hc : ContinuousOn δ (uIcc a b)) :
    (∫ t : ℝ in a..b, δ t * rsHankelKernel s m (γ t)) =
      rsCentralPrimitive s m (γ b) - rsCentralPrimitive s m (γ a) := by
  have hf : ContinuousOn (fun t => rsHankelKernel s m (γ t)) (uIcc a b) := by
    intro t ht
    exact ((rsCentralDomain_kernel_analytic s m (hγ t ht)).continuousAt.comp
      (hd t ht).continuousAt).continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => rsCentralPrimitive s m (γ t))
    (f' := fun t : ℝ => δ t * rsHankelKernel s m (γ t)) _ (hc.mul hf).intervalIntegrable
  intro t ht
  simpa only [Function.comp_def, smul_eq_mul] using
    (rsCentralPrimitive_deriv s m (hγ t ht)).scomp t (hd t ht)

theorem rsCentral_line_integral (s : ℂ) (m : ℕ) (q v : ℂ) {a b : ℝ}
    (hγ : ∀ t ∈ uIcc a b, q + t * v ∈ rsCentralDomain m) :
    (∫ t : ℝ in a..b, v * rsHankelKernel s m (q + t * v)) =
      rsCentralPrimitive s m (q + b * v) - rsCentralPrimitive s m (q + a * v) := by
  apply rsCentral_path_integral s m hγ _ continuousOn_const
  intro t _
  simpa using! ((ofRealCLM.hasDerivAt (x := t)).mul_const v).const_add q

theorem rsCentral_ray_integral (s : ℂ) (m : ℕ) (u v : ℝ) {θ : ℝ}
    (hlo : -(Real.pi / 2) < θ) (hhi : θ < 3 * Real.pi / 2) (hsin : Real.sin θ < 0) :
    (∫ x : ℝ in u..v, rsHankelLift s m (x + θ * I)) =
      rsCentralPrimitive s m (exp ((v : ℂ) + θ * I)) -
        rsCentralPrimitive s m (exp ((u : ℂ) + θ * I)) := by
  have he : (fun x : ℝ => rsHankelLift s m (x + θ * I)) =
      fun x : ℝ => exp ((x : ℂ) + θ * I) * rsHankelKernel s m (exp ((x : ℂ) + θ * I)) := by
    funext x
    exact rsHankelLift_actual s m (by simpa using hlo) (by simpa using hhi)
  rw [he]
  apply rsCentral_path_integral s m (fun x _ => rsCentral_ray_mem m x hlo hhi hsin) _ (by fun_prop)
  intro x _
  simpa using! ((ofRealCLM.hasDerivAt (x := x)).add_const (θ * I)).cexp

theorem rsCentral_arc_integral (s : ℂ) (m : ℕ) {R : ℝ}
    (hR : (m : ℝ) < R) (hR' : R < m + 1) :
    rsHankelArcBetween s m (Real.log R) (-(Real.pi / 4)) (5 * Real.pi / 4) =
      rsCentralPrimitive s m (exp ((Real.log R : ℂ) + (5 * Real.pi / 4 : ℝ) * I)) -
        rsCentralPrimitive s m (exp ((Real.log R : ℂ) + (-(Real.pi / 4) : ℝ) * I)) := by
  have he : rsHankelArcBetween s m (Real.log R) (-(Real.pi / 4)) (5 * Real.pi / 4) =
      ∫ θ : ℝ in -(Real.pi / 4)..5 * Real.pi / 4,
        (I * exp ((Real.log R : ℂ) + θ * I)) *
          rsHankelKernel s m (exp ((Real.log R : ℂ) + θ * I)) := by
    rw [rsHankelArcBetween, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le (by linarith [Real.pi_pos] : -(Real.pi / 4) ≤ 5 * Real.pi / 4)] at hθ
    dsimp only
    rw [rsHankelLift_actual s m (by simp; linarith [hθ.1, Real.pi_pos])
      (by simp; linarith [hθ.2, Real.pi_pos])]
    ring
  rw [he]
  apply rsCentral_path_integral s m (fun θ hθ => rsCentral_arc_mem hR hR' hθ) _ (by fun_prop)
  intro θ _
  simpa [mul_comm] using!
    (((ofRealCLM.hasDerivAt (x := θ)).mul_const I).const_add (Real.log R : ℂ)).cexp

theorem rsCentral_right_integral (s : ℂ) {m : ℕ} {eta b : ℝ}
    (hlo : (m : ℝ) < eta) (hhi : eta < m + 1) (hb : -eta / 2 ≤ b) :
    (∫ y : ℝ in (-eta / 2)..b, rsC2RightIntegrand s eta m y) =
      rsCentralPrimitive s m (rsDescentPoint eta b) - rsCentralPrimitive s m (rsC2Corner eta) := by
  have h := rsCentral_line_integral s m (eta : ℂ) rsDescentDirection
    (a := -eta / 2) (b := b) (fun y hy => by
      rw [uIcc_of_le hb] at hy
      simpa only [rsDescentPoint, mul_comm] using rsCentral_right_mem hlo hhi hy.1)
  simpa only [rsC2RightIntegrand, rsC2Corner, rsDescentPoint, mul_comm] using h

theorem rsCentral_left_integral (s : ℂ) {eta : ℝ} (he : 0 < eta) (m : ℕ) (b : ℝ) :
    (∫ r : ℝ in 0..b, rsC2LeftIntegrand s eta m r) =
      rsCentralPrimitive s m (rsC2LeftPoint eta m b) - rsCentralPrimitive s m (rsC2Corner eta) := by
  simpa only [rsC2LeftIntegrand, rsC2LeftPoint, ofReal_zero, zero_mul, add_zero] using
    rsCentral_line_integral s m (rsC2Corner eta) (rsC2LeftDirection eta m)
      (a := 0) (b := b) (fun r _ => rsCentral_left_mem he m r)

end LiuWang.Proof.Campaign20260915.ZetaValidation
