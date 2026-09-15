import LiuWang.Proof.LocalAnalyticBounds.LeftVertical.Main
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-! # 任意独立上下端点的矩形方向与归一化 -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.NonSymmetricContour

def lowerLeft (Hminus : Real) : Complex :=
  (-1 / 2 : Complex) + (Hminus : Complex) * Complex.I

def upperRight (b Hplus : Real) : Complex :=
  (b : Complex) + (Hplus : Complex) * Complex.I

@[simp] theorem lowerLeft_re (Hminus : Real) : (lowerLeft Hminus).re = -1 / 2 := by
  simp [lowerLeft]
@[simp] theorem lowerLeft_im (Hminus : Real) : (lowerLeft Hminus).im = Hminus := by
  simp [lowerLeft]
@[simp] theorem upperRight_re (b Hplus : Real) : (upperRight b Hplus).re = b := by
  simp [upperRight]
@[simp] theorem upperRight_im (b Hplus : Real) : (upperRight b Hplus).im = Hplus := by
  simp [upperRight]

theorem mem_rectangle {b Hplus Hminus : Real} (hb : 1 ≤ b) (hH : Hminus ≤ Hplus)
    (s : Complex) :
    s ∈ Complex.Rectangle (lowerLeft Hminus) (upperRight b Hplus) ↔
      (-1 / 2 ≤ s.re ∧ s.re ≤ b) ∧ (Hminus ≤ s.im ∧ s.im ≤ Hplus) := by
  simp [Complex.Rectangle, Complex.mem_reProdIm, Set.uIcc_of_le (by linarith : -(1 : Real) / 2 ≤ b),
    Set.uIcc_of_le hH]

theorem mem_border {b Hplus Hminus : Real} (hb : 1 ≤ b) (hH : Hminus ≤ Hplus)
    (s : Complex) :
    s ∈ RectangleBorder (lowerLeft Hminus) (upperRight b Hplus) ↔
      (((-1 / 2 ≤ s.re ∧ s.re ≤ b) ∧ s.im = Hminus) ∨
        (s.re = -1 / 2 ∧ Hminus ≤ s.im ∧ s.im ≤ Hplus)) ∨
      ((-1 / 2 ≤ s.re ∧ s.re ≤ b) ∧ s.im = Hplus) ∨
        (s.re = b ∧ Hminus ≤ s.im ∧ s.im ≤ Hplus) := by
  simp [RectangleBorder, Complex.mem_reProdIm, Set.uIcc_of_le (by linarith : -(1 : Real) / 2 ≤ b),
    Set.uIcc_of_le hH, or_assoc]

theorem zero_not_mem_border {b Hplus Hminus : Real} (hb : 1 ≤ b)
    (hp : 0 < Hplus) (hm : Hminus < 0) :
    (0 : Complex) ∉ RectangleBorder (lowerLeft Hminus) (upperRight b Hplus) := by
  rw [mem_border hb (by linarith)]
  simp only [Complex.zero_re, Complex.zero_im]
  rintro ((⟨_, h⟩ | ⟨h, _⟩) | ⟨_, h⟩ | ⟨h, _⟩) <;> norm_num at h <;> linarith

theorem LFunction_ne_zero_border {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : chi ≠ 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {b Hplus Hminus : Real} (hb : 1 ≤ b) (hH : Hminus ≤ Hplus)
    (hhor : ∀ H ∈ ({Hplus, Hminus} : Set Real), ∀ σ ∈ Set.Icc (-1 / 2 : Real) b,
      chi.LFunction ((σ : Complex) + (H : Complex) * Complex.I) ≠ 0) :
    ∀ s ∈ RectangleBorder (lowerLeft Hminus) (upperRight b Hplus), chi.LFunction s ≠ 0 := by
  intro s hs
  rcases (mem_border hb hH s).mp hs with ((hs | hs) | hs | hs)
  · have h := hhor Hminus (by simp) s.re hs.1
    simpa [← hs.2, Complex.re_add_im] using h
  · exact LFunction_ne_zero_of_re_eq_neg_one_half hchi hPrimitive hs.1
  · have h := hhor Hplus (by simp) s.re hs.1
    simpa [← hs.2, Complex.re_add_im] using h
  · exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hchi) (by linarith [hs.1])

def verticalIntegral (F : Complex → Complex) (σ Hplus Hminus : Real) : Complex :=
  (1 / (2 * (Real.pi : Complex))) *
    ∫ u in Hminus..Hplus, F ((σ : Complex) + (u : Complex) * Complex.I)

def horizontalIntegral (F : Complex → Complex) (b H : Real) : Complex :=
  (1 / (2 * (Real.pi : Complex) * Complex.I)) *
    ∫ σ in (-1 / 2 : Real)..b, F ((σ : Complex) + (H : Complex) * Complex.I)

def threeSides (F : Complex → Complex) (b Hplus Hminus : Real) : Complex :=
  verticalIntegral F (-1 / 2) Hplus Hminus +
    horizontalIntegral F b Hplus - horizontalIntegral F b Hminus

theorem rectangle_orientation (F : Complex → Complex) (b Hplus Hminus : Real) :
    verticalIntegral F b Hplus Hminus =
      RectangleIntegral' F (lowerLeft Hminus) (upperRight b Hplus) +
        threeSides F b Hplus Hminus := by
  have hi : Complex.I ≠ 0 := Complex.I_ne_zero
  simp only [RectangleIntegral', RectangleIntegral, lowerLeft_re, lowerLeft_im,
    upperRight_re, upperRight_im, HIntegral, VIntegral, smul_eq_mul,
    threeSides, verticalIntegral, horizontalIntegral]
  field_simp
  ring

theorem norm_verticalIntegral (F : Complex → Complex) (σ Hplus Hminus : Real) :
    ‖verticalIntegral F σ Hplus Hminus‖ =
      ‖∫ u in Hminus..Hplus, F ((σ : Complex) + (u : Complex) * Complex.I)‖ /
        (2 * Real.pi) := by
  simp [verticalIntegral, Complex.norm_real, abs_of_pos Real.pi_pos,
    div_eq_mul_inv, mul_comm]

theorem norm_horizontalIntegral (F : Complex → Complex) (b H : Real) :
    ‖horizontalIntegral F b H‖ =
      ‖∫ σ in (-1 / 2 : Real)..b, F ((σ : Complex) + (H : Complex) * Complex.I)‖ /
        (2 * Real.pi) := by
  simp [horizontalIntegral, Complex.norm_real,
    abs_of_pos Real.pi_pos, div_eq_mul_inv, mul_comm]

end LiuWang.Proof.NonSymmetricContour
