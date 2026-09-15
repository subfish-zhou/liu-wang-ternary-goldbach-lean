import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelKernel
import BombieriVinogradov.Helpers.ComplexAnalysis.SumResiduesFinset

set_option autoImplicit false
noncomputable section
open Complex Set Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem rsHankelKernel_order_int (s : ℂ) (m : ℕ) {n : ℤ} (hn : n ≠ 0) :
    meromorphicOrderAt (rsHankelKernel s m) n = (-1 : ℤ) := by
  have hnR : (n : ℂ).re ≠ 0 := by exact_mod_cast hn
  have hf := rsHankelNumerator_analytic s m hnR
  have hg := rsHankelDenominator_analytic (n : ℂ)
  have hp : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hnum : analyticOrderAt (rsHankelNumerator s m) n = 0 :=
    hf.analyticOrderAt_eq_zero.mpr (exp_ne_zero _)
  have hden : analyticOrderAt rsHankelDenominator n = 1 :=
    hg.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      ((rsHankelDenominator_zero_iff _).mpr ⟨n, rfl⟩)
      (by rw [(rsHankelDenominator_deriv_int n).deriv]; exact hp)
  change meromorphicOrderAt (rsHankelNumerator s m / rsHankelDenominator) n = _
  rw [meromorphicOrderAt_div hf.meromorphicAt hg.meromorphicAt,
    hf.meromorphicOrderAt_eq, hg.meromorphicOrderAt_eq, hnum, hden]
  rw [ENat.map_zero, ENat.map_one]
  rfl

theorem rsHankelKernel_pole_iff (s : ℂ) (m : ℕ) {z : ℂ} (hz : z.re ≠ 0) :
    meromorphicOrderAt (rsHankelKernel s m) z < 0 ↔ ∃ n : ℤ, z = n := by
  constructor
  · intro hp
    by_contra hn
    exact not_lt_of_ge (rsHankelKernel_analytic s m hz hn).meromorphicOrderAt_nonneg hp
  · rintro ⟨n, rfl⟩
    rw [rsHankelKernel_order_int s m (by exact_mod_cast hz)]
    exact_mod_cast (by norm_num : (-1 : ℤ) < 0)

theorem rsHankelKernel_simple (s : ℂ) (m : ℕ) {z : ℂ} (hz : z.re ≠ 0) :
    (-1 : ℤ) ≤ meromorphicOrderAt (rsHankelKernel s m) z := by
  by_cases hn : ∃ n : ℤ, z = n
  · obtain ⟨n, rfl⟩ := hn
    rw [rsHankelKernel_order_int s m (by exact_mod_cast hz)]
  · exact le_trans (show ((-1 : ℤ) : WithTop ℤ) ≤ 0 by
      exact_mod_cast (by norm_num : (-1 : ℤ) ≤ 0))
      (rsHankelKernel_analytic s m hz hn).meromorphicOrderAt_nonneg

def rsRectanglePoles (a b : ℝ) : Finset ℂ :=
  (Finset.Icc ⌈a⌉ ⌊b⌋).image (fun n : ℤ => (n : ℂ))

theorem mem_rsRectanglePoles (a b : ℝ) (z : ℂ) :
    z ∈ rsRectanglePoles a b ↔ ∃ n : ℤ, z = n ∧ a ≤ n ∧ (n : ℝ) ≤ b := by
  simp only [rsRectanglePoles, Finset.mem_image, Finset.mem_Icc,
    Int.ceil_le, Int.le_floor]
  constructor
  · rintro ⟨n, ⟨ha, hb⟩, rfl⟩
    exact ⟨n, rfl, ha, hb⟩
  · rintro ⟨n, rfl, ha, hb⟩
    exact ⟨n, ⟨ha, hb⟩, rfl⟩

theorem rsHankelKernel_rectangle (s : ℂ) (m : ℕ) {a b H : ℝ}
    (hab : a ≤ b) (hside : 0 < a ∨ b < 0) (hH : 0 < H)
    (ha : ∀ n : ℤ, a ≠ n) (hb : ∀ n : ℤ, b ≠ n) :
    RectangleIntegral' (rsHankelKernel s m) (a - H * I) (b + H * I) =
      ∑ n ∈ Finset.Icc ⌈a⌉ ⌊b⌋, rsHankelNumerator s m n / (2 * Real.pi * I) := by
  classical
  let u : ℂ := a - H * I
  let v : ℂ := b + H * I
  have huvR : u.re ≤ v.re := by simpa [u, v] using hab
  have huvI : u.im ≤ v.im := by simp [u, v]; linarith
  have hmem (z : ℂ) : z ∈ Rectangle u v ↔
      a ≤ z.re ∧ z.re ≤ b ∧ -H ≤ z.im ∧ z.im ≤ H := by
    simpa [u, v] using mem_Rect huvR huvI z
  have hnonzero {z : ℂ} (hz : z ∈ Rectangle u v) : z.re ≠ 0 := by
    have h := (hmem z).mp hz
    rcases hside with hside | hside
    · linarith
    · linarith
  have hmero : MeromorphicOn (rsHankelKernel s m) (Rectangle u v) :=
    fun z hz => rsHankelKernel_meromorphic s m (hnonzero hz)
  have hset : Rectangle u v ∩ {z | meromorphicOrderAt (rsHankelKernel s m) z < 0} =
      (rsRectanglePoles a b : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨hz, hp⟩
      obtain ⟨n, rfl⟩ := (rsHankelKernel_pole_iff s m (hnonzero hz)).mp hp
      have h := (hmem _).mp hz
      exact (mem_rsRectanglePoles _ _ _).mpr ⟨n, rfl, by simpa using h.1, by simpa using h.2.1⟩
    · intro hz
      obtain ⟨n, rfl, han, hnb⟩ := (mem_rsRectanglePoles _ _ _).mp hz
      have hnrect : (n : ℂ) ∈ Rectangle u v := (hmem _).mpr
        (by simpa using And.intro han (And.intro hnb (And.intro (by linarith : -H ≤ 0) hH.le)))
      exact ⟨hnrect, (rsHankelKernel_pole_iff s m (hnonzero hnrect)).mpr ⟨n, rfl⟩⟩
  have hdisj : Disjoint (RectangleBorder u v)
      {z | meromorphicOrderAt (rsHankelKernel s m) z < 0} := by
    rw [Set.disjoint_left]
    intro z hz hp
    have hzrect : z ∈ Rectangle u v := rectangleBorder_subset_rectangle u v hz
    obtain ⟨n, rfl⟩ := (rsHankelKernel_pole_iff s m (hnonzero hzrect)).mp hp
    have hni : (n : ℂ).im = 0 := by simp
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
      u, v, sub_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im,
      mul_zero, sub_zero, add_zero, sub_im, add_im, mul_im, mul_one, zero_sub,
      intCast_re, intCast_im] at hz
    rcases hz with ((hz | hz) | hz) | hz
    · linarith [hz.2]
    · exact ha n hz.1.symm
    · linarith [hz.2]
    · exact hb n hz.1.symm
  rw [RectangleIntegral'_eq_sumResiduesIn huvR huvI hmero hdisj
    (by rw [hset]; exact (rsRectanglePoles a b).finite_toSet)
    (fun z hz => rsHankelKernel_simple s m (hnonzero hz)), hset,
    BombieriVinogradov.ComplexAnalysis.sumResiduesIn_finset, rsRectanglePoles,
    Finset.sum_image (by
      intro i _ j _ hij
      change (i : ℂ) = (j : ℂ) at hij
      exact_mod_cast hij)]
  apply Finset.sum_congr rfl
  intro n hn
  apply rsHankelKernel_residue
  have hnrect : (n : ℂ) ∈ Rectangle u v := by
    apply (hmem _).mpr
    have hn' := Finset.mem_Icc.mp hn
    exact ⟨by simpa using Int.ceil_le.mp hn'.1, by simpa using Int.le_floor.mp hn'.2,
      by simp; linarith, by simpa using hH.le⟩
  exact_mod_cast hnonzero hnrect

end LiuWang.Proof.Campaign20260915.ZetaValidation
