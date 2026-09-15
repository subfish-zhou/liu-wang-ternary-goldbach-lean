import LiuWang.Proof.Campaign20260915.RSSection8Scalar.EndpointM

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Set

namespace LiuWang.Proof.Campaign20260915.RSSection8Scalar

/-- RS1962 (8.4), leaving the value of the separately owned spectral kernel explicit. -/
def LValue (x k : ℝ) : ℝ :=
  (2 + Real.log x) / Real.log x * (k + 1.84 / x + 0.31 / x ^ 3) +
    2.04 / x ^ (1 / 2 : ℝ) + 4.5 * x ^ (-2 / 3 : ℝ) + 1.02 / (x - 1)

theorem LValue_mono_kernel {x k l : ℝ} (hx : 1 < x) (hkl : k ≤ l) :
    LValue x k ≤ LValue x l := by
  have hl : 0 ≤ Real.log x := (Real.log_pos hx).le
  unfold LValue
  gcongr

theorem LValue_antitone_base {x y k : ℝ} (hx : 1 < x) (hxy : x ≤ y) (hk : 0 ≤ k) :
    LValue y k ≤ LValue x k := by
  have hx0 : 0 < x := by linarith
  have hy : 1 < y := hx.trans_le hxy
  have hlx := Real.log_pos hx
  have hly := Real.log_pos hy
  have hlog := Real.log_le_log hx0 hxy
  have hfac : (2 + Real.log y) / Real.log y ≤ (2 + Real.log x) / Real.log x := by
    rw [add_div, add_div, div_self hly.ne', div_self hlx.ne']
    gcongr
  have hrest : k + 1.84 / y + 0.31 / y ^ 3 ≤ k + 1.84 / x + 0.31 / x ^ 3 := by
    gcongr
  have hprod := mul_le_mul hfac hrest (by positivity : 0 ≤ k + 1.84 / y + 0.31 / y ^ 3)
    (by positivity : 0 ≤ (2 + Real.log x) / Real.log x)
  have hhalf : (2.04 : ℝ) / y ^ (1 / 2 : ℝ) ≤ 2.04 / x ^ (1 / 2 : ℝ) := by
    gcongr
  have hthird := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hx0 hxy (by norm_num : (-2 / 3 : ℝ) ≤ 0))
    (by norm_num : (0 : ℝ) ≤ 4.5)
  have hlast : (1.02 : ℝ) / (y - 1) ≤ 1.02 / (x - 1) := by
    gcongr
  unfold LValue
  linarith

theorem LValue_antitoneOn {K : ℝ → ℝ} {A : ℝ} (hA : 1 < A)
    (hK0 : ∀ x ∈ Ici A, 0 ≤ K x) (hK : AntitoneOn K (Ici A)) :
    AntitoneOn (fun x => LValue x (K x)) (Ici A) := by
  intro x hx y hy hxy
  exact (LValue_mono_kernel (hA.trans_le hy) (hK hx hy hxy)).trans
    (LValue_antitone_base (hA.trans_le hx) hxy (hK0 x hx))

/-- The scalar content of Lemma 10; the actual `K(1,x)` is not redefined here. -/
theorem lemma10_scalar {K : ℝ → ℝ} {A B a x : ℝ}
    (hA : 1 < A) (ha : a < 1 / 2)
    (hdom : Real.sqrt ((1 / 2) * (1 + 2 * a) / (1 - 2 * a)) ≤ Real.log A)
    (hK0 : ∀ y ∈ Ici A, 0 ≤ K y) (hK : AntitoneOn K (Ici A))
    (hendpoint : LValue A (K A) < M B a) (hx : x ∈ Icc A B) :
    LValue x (K x) < M x a :=
  ((LValue_antitoneOn hA hK0 hK self_mem_Ici hx.1 hx.1).trans_lt hendpoint).trans_le
    (M_endpoint_le hA ha hdom hx)

#print axioms LValue_antitoneOn
#print axioms lemma10_scalar

end LiuWang.Proof.Campaign20260915.RSSection8Scalar
