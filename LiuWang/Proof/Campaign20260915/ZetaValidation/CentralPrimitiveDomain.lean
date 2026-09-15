import LiuWang.Proof.Campaign20260915.ZetaValidation.CentralPrimitiveGlue

set_option autoImplicit false
noncomputable section
open Complex Set

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsCentralUpper : Set ℂ := {z | 0 < z.im}
def rsCentralRightWindow (m : ℕ) : Set ℂ := {z | (m : ℝ) < z.re ∧ z.re < m + 1}
def rsCentralLeftWindow (m : ℕ) : Set ℂ := {z | -(m : ℝ) - 1 < z.re ∧ z.re < -(m : ℝ)}
def rsCentralRightLower : Set ℂ := {z | 0 < z.re ∧ z.im < 0}
def rsCentralLeftLower : Set ℂ := {z | z.re < 0 ∧ z.im < 0}
def rsCentralDomain (m : ℕ) : Set ℂ :=
  ((rsCentralUpper ∪ rsCentralRightWindow m) ∪ rsCentralLeftWindow m) ∪
    rsCentralRightLower ∪ rsCentralLeftLower

theorem rsCentral_patches_open (m : ℕ) :
    IsOpen rsCentralUpper ∧ IsOpen (rsCentralRightWindow m) ∧
      IsOpen (rsCentralLeftWindow m) ∧ IsOpen rsCentralRightLower ∧ IsOpen rsCentralLeftLower := by
  exact ⟨isOpen_lt continuous_const continuous_im,
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const),
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const),
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_im continuous_const),
    (isOpen_lt continuous_re continuous_const).inter (isOpen_lt continuous_im continuous_const)⟩

theorem rsCentral_patches_convex (m : ℕ) :
    Convex ℝ rsCentralUpper ∧ Convex ℝ (rsCentralRightWindow m) ∧
      Convex ℝ (rsCentralLeftWindow m) ∧ Convex ℝ rsCentralRightLower ∧ Convex ℝ rsCentralLeftLower := by
  exact ⟨(convex_Ioi (0 : ℝ)).linear_preimage imLm,
    ((convex_Ioi (m : ℝ)).linear_preimage reLm).inter
      ((convex_Iio ((m : ℝ) + 1)).linear_preimage reLm),
    ((convex_Ioi (-(m : ℝ) - 1)).linear_preimage reLm).inter
      ((convex_Iio (-(m : ℝ))).linear_preimage reLm),
    ((convex_Ioi (0 : ℝ)).linear_preimage reLm).inter ((convex_Iio (0 : ℝ)).linear_preimage imLm),
    ((convex_Iio (0 : ℝ)).linear_preimage reLm).inter ((convex_Iio (0 : ℝ)).linear_preimage imLm)⟩

theorem rsCentralDomain_open (m : ℕ) : IsOpen (rsCentralDomain m) := by
  obtain ⟨hU, hR, hL, hB, hC⟩ := rsCentral_patches_open m
  exact (((hU.union hR).union hL).union hB).union hC

theorem rsCentralDomain_kernel_analytic (s : ℂ) (m : ℕ) {z : ℂ}
    (hz : z ∈ rsCentralDomain m) : AnalyticAt ℂ (rsHankelKernel s m) z := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hcut : 0 < z.im ∨ z.re ≠ 0 := by
    simp only [rsCentralDomain, rsCentralUpper, rsCentralRightWindow, rsCentralLeftWindow,
      rsCentralRightLower, rsCentralLeftLower, mem_union, mem_ofPred_eq] at hz
    grind
  apply rsHankelKernel_analytic_slit s m hcut
  rintro ⟨n, rfl⟩
  simp only [rsCentralDomain, rsCentralUpper, rsCentralRightWindow, rsCentralLeftWindow,
    rsCentralRightLower, rsCentralLeftLower, mem_union, mem_ofPred_eq, intCast_im, intCast_re,
    lt_self_iff_false, and_false, false_or, or_false] at hz
  rcases hz with hz | hz
  · have h : (m : ℤ) < n ∧ n < (m : ℤ) + 1 := by exact_mod_cast hz
    omega
  · have h : -(m : ℤ) - 1 < n ∧ n < -(m : ℤ) := by exact_mod_cast hz
    omega

theorem rsCentralDomain_exact (s : ℂ) (m : ℕ) :
    IsExactOn (rsHankelKernel s m) (rsCentralDomain m) := by
  obtain ⟨hU, hR, hL, hB, hC⟩ := rsCentral_patches_open m
  obtain ⟨cU, cR, cL, cB, cC⟩ := rsCentral_patches_convex m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hd (S : Set ℂ) (z : ℂ) (hz : z ∈ rsCentralDomain m) :
      DifferentiableWithinAt ℂ (rsHankelKernel s m) S z :=
    (rsCentralDomain_kernel_analytic s m hz).differentiableAt.differentiableWithinAt
  have eU := central_exact_convex hU cU (show DifferentiableOn ℂ (rsHankelKernel s m) rsCentralUpper by
    intro z hz; exact hd _ z (Or.inl (Or.inl (Or.inl (Or.inl hz)))))
  have eR := central_exact_convex hR cR (show DifferentiableOn ℂ (rsHankelKernel s m) (rsCentralRightWindow m) by
    intro z hz; exact hd _ z (Or.inl (Or.inl (Or.inl (Or.inr hz)))))
  have eL := central_exact_convex hL cL (show DifferentiableOn ℂ (rsHankelKernel s m) (rsCentralLeftWindow m) by
    intro z hz; exact hd _ z (Or.inl (Or.inl (Or.inr hz))))
  have eB := central_exact_convex hB cB (show DifferentiableOn ℂ (rsHankelKernel s m) rsCentralRightLower by
    intro z hz; exact hd _ z (Or.inl (Or.inr hz)))
  have eC := central_exact_convex hC cC (show DifferentiableOn ℂ (rsHankelKernel s m) rsCentralLeftLower by
    intro z hz; exact hd _ z (Or.inr hz))
  have nUR : (rsCentralUpper ∩ rsCentralRightWindow m).Nonempty := by
    refine ⟨((m : ℝ) + 1 / 2 : ℝ) + I, ?_⟩
    norm_num [rsCentralUpper, rsCentralRightWindow]
  have nUL : (rsCentralUpper ∩ rsCentralLeftWindow m).Nonempty := by
    refine ⟨(-((m : ℝ) + 1 / 2) : ℝ) + I, ?_⟩
    simp [rsCentralUpper, rsCentralLeftWindow]
    norm_num
    linarith
  have nRB : (rsCentralRightWindow m ∩ rsCentralRightLower).Nonempty := by
    refine ⟨((m : ℝ) + 1 / 2 : ℝ) - I, ?_⟩
    norm_num [rsCentralRightWindow, rsCentralRightLower]
    linarith
  have nLC : (rsCentralLeftWindow m ∩ rsCentralLeftLower).Nonempty := by
    refine ⟨(-((m : ℝ) + 1 / 2) : ℝ) - I, ?_⟩
    simp [rsCentralLeftWindow, rsCentralLeftLower]
    constructor <;> norm_num <;> linarith
  have hUL : (rsCentralUpper ∪ rsCentralRightWindow m) ∩ rsCentralLeftWindow m =
      rsCentralUpper ∩ rsCentralLeftWindow m := by
    ext z
    simp only [rsCentralUpper, rsCentralRightWindow, rsCentralLeftWindow,
      mem_union, mem_inter_iff, mem_ofPred_eq]
    grind
  have hRB : ((rsCentralUpper ∪ rsCentralRightWindow m) ∪ rsCentralLeftWindow m) ∩
      rsCentralRightLower = rsCentralRightWindow m ∩ rsCentralRightLower := by
    ext z
    simp only [rsCentralUpper, rsCentralRightWindow, rsCentralLeftWindow, rsCentralRightLower,
      mem_union, mem_inter_iff, mem_ofPred_eq]
    grind
  have hLC : (((rsCentralUpper ∪ rsCentralRightWindow m) ∪ rsCentralLeftWindow m) ∪
      rsCentralRightLower) ∩ rsCentralLeftLower = rsCentralLeftWindow m ∩ rsCentralLeftLower := by
    ext z
    simp only [rsCentralUpper, rsCentralRightWindow, rsCentralLeftWindow, rsCentralRightLower,
      rsCentralLeftLower, mem_union, mem_inter_iff, mem_ofPred_eq]
    grind
  have eUR := central_exact_union hU hR (cU.inter cR).isPreconnected nUR eU eR
  have eURL := central_exact_union (hU.union hR) hL
    (hUL ▸ (cU.inter cL).isPreconnected) (hUL ▸ nUL) eUR eL
  have eURLB := central_exact_union ((hU.union hR).union hL) hB
    (hRB ▸ (cR.inter cB).isPreconnected) (hRB ▸ nRB) eURL eB
  exact central_exact_union (((hU.union hR).union hL).union hB) hC
    (hLC ▸ (cL.inter cC).isPreconnected) (hLC ▸ nLC) eURLB eC

end LiuWang.Proof.Campaign20260915.ZetaValidation
