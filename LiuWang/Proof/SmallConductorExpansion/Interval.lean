import LiuWang.Proof.SmallConductorExpansion.Truncation
import LiuWang.Proof.SmallConductorExclusion.Consumer

/-!
# Rational envelope and the original exceptional real interval

The closed interval starting at `19/20` contains the paper's real region for
every `x >= 10`. For a cutoff at most 32, the rational envelope `6/5` is paid
by `(6/5)^20 >= 32`. Values at and to the right of one use ordinary L
nonvanishing, so no upper bound on the claimed real interval is hidden.
-/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.SmallConductorExpansion

theorem rpow_envelope_of_pow {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n)
    {C sigma : ℝ} (hC : 0 ≤ C) (hpow : (m : ℝ) ≤ C ^ n)
    (hs : 1 - 1 / (n : ℝ) ≤ sigma) :
    (m : ℝ) ^ (1 - sigma) ≤ C := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    _ ≤ (m : ℝ) ^ ((n : ℝ)⁻¹) :=
      Real.rpow_le_rpow_of_exponent_le hmR (by rw [one_div] at hs; linarith)
    _ ≤ (C ^ n) ^ ((n : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) hpow (inv_nonneg.mpr hnR.le)
    _ = C := Real.pow_rpow_inv_natCast hC (by omega)

theorem cutoff_thirtytwo_envelope {m : ℕ} (hm : 1 ≤ m) (hm32 : m ≤ 32)
    {sigma : ℝ} (hs : 19 / 20 ≤ sigma) : (m : ℝ) ^ (1 - sigma) ≤ 6 / 5 := by
  apply rpow_envelope_of_pow (n := 20) hm (by decide) (by norm_num)
  · have : (m : ℝ) ≤ 32 := by exact_mod_cast hm32
    exact this.trans (by norm_num)
  · norm_num
    exact hs

theorem original_region_ge_nineteen_twentieths {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) : 19 / 20 ≤ beta := by
  have hlog := Sharp.log_scale_ge hx
  have hd : 0 < 9.645908801 * Real.log x := by nlinarith
  have hw : 1 / (9.645908801 * Real.log x) ≤ 1 / 20 :=
    (div_le_iff₀ hd).mpr (by nlinarith)
  linarith

theorem signedCertificate_ne_zero_on_interval {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 < n) {P C : ℝ}
    (hcert : SignedCertificate chi m P C) (hC : 0 ≤ C)
    (hpow : (m : ℝ) ≤ C ^ n) {beta : ℝ}
    (hb : 1 - 1 / (n : ℝ) ≤ beta) : chi.LFunction (beta : ℂ) ≠ 0 := by
  by_cases hb1 : 1 ≤ beta
  · exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) hb1
  · apply LFunction_ne_zero_of_signedCertificate chi hc hm hcert
    · have hnR : (1 : ℝ) < n := by exact_mod_cast hn
      have hi : 1 / (n : ℝ) < 1 := (div_lt_one (by linarith : (0 : ℝ) < n)).mpr hnR
      linarith
    · exact (lt_of_not_ge hb1).le
    · exact rpow_envelope_of_pow hm (by omega) hC hpow hb

theorem signedCertificate_ne_zero_original_region {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) {m : ℕ}
    (hm : 1 ≤ m) (hm32 : m ≤ 32) {P : ℝ}
    (hcert : SignedCertificate chi m P (6 / 5))
    {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply signedCertificate_ne_zero_on_interval chi hc hm (n := 20) (by decide)
    hcert (by norm_num)
  · have hmR : (m : ℝ) ≤ 32 := by exact_mod_cast hm32
    exact hmR.trans (by norm_num)
  · have := original_region_ge_nineteen_twentieths hx hb
    norm_num
    exact this

end LiuWang.Proof.SmallConductorExpansion
