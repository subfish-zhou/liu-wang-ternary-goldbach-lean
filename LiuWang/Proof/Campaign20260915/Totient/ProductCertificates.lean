import LiuWang.Proof.Campaign20260915.Totient.ProductCore
import LiuWang.Proof.Campaign20260915.Totient.ProductLookup
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LiuWang.Proof.Campaign20260915.Totient
noncomputable section

theorem productLower_le_envelope {x : ℝ} {u : ℤ} (hu : 0 < u)
    (hl : (u : ℝ) / 10000000000 ≤ Real.log x)
    (hh : Real.log x ≤ (u + 61 : ℝ) / 10000000000) :
    (productLower u : ℝ) ≤ productEnvelope x := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hlog : 0 < Real.log x := lt_of_lt_of_le (by positivity) hl
  have hrec := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
    (show 0 < 2 * Real.log x by positivity)
    (show 2 * Real.log x ≤ 2 * ((u + 61 : ℝ) / 10000000000) by linarith)
  have hg :=
    LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.gammaFactor_interval.1
  change (1.78107239 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant at hg
  unfold productLower productEnvelope
  push_cast
  have hm := mul_le_mul hg (add_le_add hl hrec) (by positivity)
    (Real.exp_pos Real.eulerMascheroniConstant).le
  calc
    _ = (1.78107239 : ℝ) *
        ((u : ℝ) / 10000000000 + 1 / (2 * ((u + 61 : ℝ) / 10000000000))) := by
      field_simp
      ring
    _ ≤ _ := hm

theorem product_endpoint_286 :
    (prefixEuler 286 : ℝ) < productEnvelope 286 := by
  have hs : logScale (286 : ℚ) = 8 := by decide +kernel
  have hu : ⌊logCenter (286 : ℚ) * 10000000000⌋ = 56559918087 := by
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]
  have hb := rational_log_bounds (x := (286 : ℚ)) (by norm_num)
  simp only [logHi, logLo] at hb
  rw [hu, hs] at hb
  norm_num at hb
  have hnum : (102257527751 : ℚ) / 10000000000 < productLower 56559918087 := by
    norm_num [productLower]
  have h := productLower_le_envelope (x := 286) (u := 56559918087)
    (by norm_num) (by norm_num; linarith [hb.1]) (by norm_num; linarith [hb.2])
  have hunit := prefixEuler_le_units 286
  rw [eulerUnits_286] at hunit
  have hnumR : (102257527751 : ℝ) / 10000000000 < (productLower 56559918087 : ℝ) := by
    have hcast := Rat.cast_lt (K := ℝ) |>.mpr hnum
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcast
  exact hunit.trans_lt (hnumR.trans_le h)

#print axioms prefixEuler_le_units
#print axioms product_endpoint_286

end
end LiuWang.Proof.Campaign20260915.Totient
