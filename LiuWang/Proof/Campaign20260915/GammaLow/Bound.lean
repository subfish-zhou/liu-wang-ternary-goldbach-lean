import LiuWang.Proof.Campaign20260915.GammaLow.Rectangle
import LiuWang.Proof.ZeroRegionFamily.Sharp.Principal

set_option autoImplicit false

noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.Campaign20260915.GammaLow

theorem shifted_digamma_low {sigma t : ℝ} (hs : 1 < sigma)
    (hs1 : sigma ≤ 23 / 20) (ht : |t| ≤ 1) :
    ((digamma (((sigma : ℂ) + I * t) / 2 + 1)).re -
      stechkinK * (digamma (((stechkinSigma sigma : ℂ) + I * t) / 2 + 1)).re) / 2 ≤
        153 / 2500 := by
  have hb := stechkinSigma_bounds hs hs1
  have hhalf : |t / 2| ≤ (1 / 2 : ℝ) := by
    rw [abs_div]
    norm_num
    linarith
  have hu := digamma_upper_rectangle (a := sigma / 2 + 1)
    (by linarith) (by linarith) hhalf
  have hl := digamma_lower_rectangle (b := stechkinSigma sigma / 2 + 1)
    (y := t / 2) (by linarith [hb.1])
  have hkl := mul_le_mul_of_nonneg_left hl stechkinK_mem.1
  have hgamma := mul_le_mul_of_nonneg_left euler_lower
    (sub_nonneg.mpr stechkinK_mem.2)
  have hcast (u : ℝ) : ((u : ℂ) + I * t) / 2 + 1 =
      (((u / 2 + 1 : ℝ) : ℂ) + I * (t / 2 : ℝ)) := by
    push_cast
    ring
  rw [hcast, hcast]
  nlinarith [stechkinK_ge]

theorem shifted_digamma_low_strict {sigma t : ℝ}
    (hs : sigma ∈ Set.Ioo (1 : ℝ) 1.15) (ht : |t| < 1) :
    ((digamma (((sigma : ℂ) + I * t) / 2 + 1)).re -
      stechkinK * (digamma (((stechkinSigma sigma : ℂ) + I * t) / 2 + 1)).re) / 2 <
        0.0615 := by
  have hh := shifted_digamma_low hs.1 (by linarith [hs.2]) ht.le
  linarith

#print axioms shifted_digamma_low_strict

end LiuWang.Proof.Campaign20260915.GammaLow
