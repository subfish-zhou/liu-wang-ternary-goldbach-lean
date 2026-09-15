import LiuWang.Proof.Campaign20260915.ZetaValidation.CentralPrimitiveDomain

set_option autoImplicit false
noncomputable section
open Complex Set
open scoped Interval

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rsCentralDomain_mem_iff (m : ℕ) (z : ℂ) :
    z ∈ rsCentralDomain m ↔ 0 < z.im ∨ (z.im < 0 ∧ z.re ≠ 0) ∨
      ((m : ℝ) < z.re ∧ z.re < m + 1) ∨ (-(m : ℝ) - 1 < z.re ∧ z.re < -(m : ℝ)) := by
  simp only [rsCentralDomain, rsCentralUpper, rsCentralRightWindow, rsCentralLeftWindow,
    rsCentralRightLower, rsCentralLeftLower, mem_union, mem_ofPred_eq]
  grind

theorem rsCentralDomain_mem_of_cut {m : ℕ} {z : ℂ}
    (hc : 0 < z.im ∨ z.re ≠ 0)
    (hr : z.im = 0 → ((m : ℝ) < z.re ∧ z.re < m + 1) ∨
      (-(m : ℝ) - 1 < z.re ∧ z.re < -(m : ℝ))) :
    z ∈ rsCentralDomain m := by
  rw [rsCentralDomain_mem_iff]
  rcases lt_trichotomy z.im 0 with h | h | h
  · exact Or.inr (Or.inl ⟨h, hc.resolve_left (not_lt_of_ge h.le)⟩)
  · exact Or.inr (Or.inr (hr h))
  · exact Or.inl h

theorem rsHankel_exp_avoids_cut {w : ℂ}
    (hlo : -(Real.pi / 2) < w.im) (hhi : w.im < 3 * Real.pi / 2) :
    0 < (exp w).im ∨ (exp w).re ≠ 0 := by
  have he : -I * exp w = exp (w - Real.pi / 2 * I) := by
    rw [exp_sub, exp_pi_div_two_mul_I, div_I]
    ring
  have hlo' : -Real.pi < (w - Real.pi / 2 * I).im := by simp; linarith
  have hhi' : (w - Real.pi / 2 * I).im < Real.pi := by simp; linarith
  have hp : -I * exp w ∈ slitPlane := by
    rw [he, exp_mem_slitPlane, (toIocMod_eq_self Real.two_pi_pos).mpr
      ⟨hlo', by linarith⟩]
    exact hhi'.ne
  simpa [mem_slitPlane_iff] using hp

theorem rsCentral_arc_mem {m : ℕ} {R θ : ℝ} (hR : (m : ℝ) < R)
    (hR' : R < m + 1) (hθ : θ ∈ uIcc (-(Real.pi / 4)) (5 * Real.pi / 4)) :
    exp ((Real.log R : ℂ) + θ * I) ∈ rsCentralDomain m := by
  have hR0 : 0 < R := lt_of_le_of_lt (Nat.cast_nonneg m) hR
  rw [uIcc_of_le (by linarith [Real.pi_pos] : -(Real.pi / 4) ≤ 5 * Real.pi / 4)] at hθ
  apply rsCentralDomain_mem_of_cut (rsHankel_exp_avoids_cut
    (by simp; linarith [hθ.1, Real.pi_pos]) (by simp; linarith [hθ.2, Real.pi_pos]))
  intro hi
  have hn : ‖exp ((Real.log R : ℂ) + θ * I)‖ = R := by simp [norm_exp, Real.exp_log hR0]
  have hz : exp ((Real.log R : ℂ) + θ * I) =
      ((exp ((Real.log R : ℂ) + θ * I)).re : ℂ) := by
    apply Complex.ext <;> simp [hi]
  rw [hz, norm_real, Real.norm_eq_abs] at hn
  rcases (abs_eq hR0.le).mp hn with hr | hr
  · exact Or.inl (by rw [hr]; exact ⟨hR, hR'⟩)
  · exact Or.inr (by rw [hr]; constructor <;> linarith)

theorem rsCentral_ray_mem (m : ℕ) (x : ℝ) {θ : ℝ}
    (hlo : -(Real.pi / 2) < θ) (hhi : θ < 3 * Real.pi / 2)
    (hsin : Real.sin θ < 0) :
    exp ((x : ℂ) + θ * I) ∈ rsCentralDomain m := by
  have hc := rsHankel_exp_avoids_cut
    (w := (x : ℂ) + θ * I) (by simpa using hlo) (by simpa using hhi)
  have hi : (exp ((x : ℂ) + θ * I)).im < 0 := by
    simpa [exp_im] using mul_neg_of_pos_of_neg (Real.exp_pos x) hsin
  rw [rsCentralDomain_mem_iff]
  exact Or.inr (Or.inl ⟨hi, hc.resolve_left (not_lt_of_ge hi.le)⟩)

theorem rsCentral_right_mem {m : ℕ} {eta y : ℝ} (hlo : (m : ℝ) < eta)
    (hhi : eta < m + 1) (hy : -eta / 2 ≤ y) :
    rsDescentPoint eta y ∈ rsCentralDomain m := by
  have he : 0 < eta := lt_of_le_of_lt (Nat.cast_nonneg m) hlo
  have hs : 0 < Real.sqrt 2 := by positivity
  have hre : (rsDescentPoint eta y).re = eta + y / Real.sqrt 2 := by
    simp [rsDescentPoint, rsDescentDirection]
    field_simp
  have him : (rsDescentPoint eta y).im = -y / Real.sqrt 2 := by
    simp [rsDescentPoint, rsDescentDirection]
    ring
  have hcr := (rsC2Corner_upper he).1
  rw [(rsC2Corner_coordinates eta).1] at hcr
  have hdiv := div_le_div_of_nonneg_right hy hs.le
  rw [div_div, neg_div] at hdiv
  apply rsCentralDomain_mem_of_cut (Or.inr (by rw [hre]; linarith))
  intro hi
  rw [him] at hi
  have hy0 : y = 0 := by simpa using (div_eq_zero_iff.mp hi).resolve_right hs.ne'
  left
  simpa [hy0, rsDescentPoint] using And.intro hlo hhi

theorem rsCentral_left_mem {eta : ℝ} (he : 0 < eta) (m : ℕ) (r : ℝ) :
    rsC2LeftPoint eta m r ∈ rsCentralDomain m := by
  apply rsCentralDomain_mem_of_cut (rsC2Left_avoids_cut he m r)
  intro hi
  rw [(rsC2LeftPoint_coordinates eta r m).2] at hi
  have hr : r = 1 := by
    have h := (mul_eq_zero.mp hi).resolve_right (rsC2Corner_upper he).2.ne'
    linarith
  right
  rw [hr, (rsC2LeftPoint_endpoints eta m).2]
  simp
  norm_num
  linarith

theorem rsCentral_horizontal_mem {m : ℕ} {x T : ℝ} (hx : x ≠ 0) (hT : 0 < T) :
    (x : ℂ) - T * I ∈ rsCentralDomain m := by
  rw [rsCentralDomain_mem_iff]
  apply Or.inr ∘ Or.inl
  simpa using And.intro (neg_neg_of_pos hT) hx

end LiuWang.Proof.Campaign20260915.ZetaValidation
