import LiuWang.Proof.CompleteExpansion.Consumer
import LiuWang.Proof.MajorArcApproximation.Error
import LiuWang.Proof.OscillatoryBounds.Consumer
import LiuWang.Proof.SingularSeries.Convergence

/-!
# Payments on the literal M2 witness

The lower bound is the complement of the whole M1, not a second rational
approximation. The principal payment uses only the elementary totient bound;
the sharper Gauss-energy estimate is retained in the Perron payment.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment

open Interfaces Parameters ArcGeometry CompleteExpansion CharacterExpansion

theorem total_gauss_mass_le {q a : ℕ} [NeZero q] (hi : sourceIndex a q) :
    principalMass q + nonprincipalMass q a ≤ Real.sqrt (q : ℝ) := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hg : ‖G a (1 : Character q)‖ = |(ArithmeticFunction.moebius q : ℝ)| := by
    rw [NonprincipalPacket.G_one_eq_moebius hi.2.2]
    simp only [Complex.norm_intCast]
  have he : principalMass q + nonprincipalMass q a =
      (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Character q)), hg]
    unfold principalMass nonprincipalMass
    ring
  rw [he]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * (Real.sqrt (q.totient : ℝ) * (q.totient : ℝ)) :=
      mul_le_mul_of_nonneg_left (NonprincipalPacket.sum_norm_G_le a) (by positivity)
    _ = Real.sqrt (q.totient : ℝ) := by field_simp
    _ ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le q)

theorem errorBound_le_gauss {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q) (eta : ℝ) :
    errorBound q N a eta ≤
      Real.sqrt (q : ℝ) * (0.963362 + 3.02347 * (N : ℝ) * |eta|) *
        (N : ℝ) / sourceT N * sourceL N ^ 2 +
      Real.log q * sourceL N / Real.log 2 := by
  have hT := sourceT_pos hN
  have hx : 0 ≤ (N : ℝ) * |eta| := by positivity
  apply (errorBound_le_decimal hN a eta).trans
  have hc :
      principalMass q * (0.963362 + 3.02347 * (N : ℝ) * |eta|) +
        nonprincipalMass q a * (0.96258 + 3.02102 * (N : ℝ) * |eta|) ≤
      Real.sqrt (q : ℝ) * (0.963362 + 3.02347 * (N : ℝ) * |eta|) := by
    calc
      _ ≤ (principalMass q + nonprincipalMass q a) *
          (0.963362 + 3.02347 * (N : ℝ) * |eta|) := by
        have hh := mul_le_mul_of_nonneg_left
          (show (0.96258 : ℝ) + 3.02102 * (N : ℝ) * |eta| ≤
            0.963362 + 3.02347 * (N : ℝ) * |eta| by nlinarith)
          (nonprincipalMass_nonneg q a)
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (total_gauss_mass_le hi) (by positivity)
  gcongr

theorem perron_payment {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP N) {eta : ℝ}
    (heta : |eta| ≤ 1 / ((q : ℝ) * sourceQ N)) :
    errorBound q N a eta ≤ 3.025 * (N : ℝ) / sourceL N ^ 6 := by
  have hq0 := sourceIndex_den_pos hi
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hn := natCast_pos_of_exp_le hN
  have hL := sourceL_pos hN
  have hL1 := one_le_sourceL hN
  have hT := sourceT_pos hN
  have hqx : (q : ℝ) * ((N : ℝ) * |eta|) ≤ sourceL N ^ 7 := by
    rw [approximationRadius_eq hN hq0] at heta
    have hh := (le_div_iff₀ (mul_pos hqr hn)).mp heta
    nlinarith
  have hs : Real.sqrt (q : ℝ) ≤ (q : ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨hqr.le, by nlinarith⟩
  have hpow : (10000 : ℝ) ≤ sourceL N ^ 4 :=
    (by norm_num : (10000 : ℝ) ≤ 2000 ^ 4).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_2000 hN) 4)
  have hsmall : 10000 * sourceL N ^ 3 ≤ sourceL N ^ 7 := by
    have hh := mul_le_mul_of_nonneg_right hpow (pow_nonneg hL.le 3)
    simpa only [← pow_add] using hh
  have hc : Real.sqrt (q : ℝ) *
      (0.963362 + 3.02347 * (N : ℝ) * |eta|) ≤ 3.024 * sourceL N ^ 7 := by
    calc
      _ ≤ (q : ℝ) * (0.963362 + 3.02347 * (N : ℝ) * |eta|) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ ≤ _ := by
        change (q : ℝ) ≤ sourceL N ^ 3 at hq
        nlinarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogq : Real.log q ≤ sourceL N ^ 3 := by
    change (q : ℝ) ≤ sourceL N ^ 3 at hq
    linarith [Real.log_le_sub_one_of_pos hqr]
  have hcorr : Real.log q * sourceL N / Real.log 2 ≤
      0.001 * (N : ℝ) / sourceL N ^ 6 := by
    calc
      _ ≤ 2 * sourceL N ^ 4 := by
        apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
        have hh := mul_le_mul_of_nonneg_right hlogq hL.le
        nlinarith [mul_nonneg (pow_nonneg hL.le 4)
          (show 0 ≤ Real.log 2 - 1 / 2 by linarith)]
      _ ≤ _ := by
        apply (le_div_iff₀ (pow_pos hL 6)).mpr
        have hh := (mul_sourceL_pow_lt (c := 1) (k := 11) hN
          (by norm_num) (by norm_num)).le
        have hh' := mul_le_mul_of_nonneg_right (sourceL_ge_2000 hN)
          (pow_nonneg hL.le 10)
        nlinarith [show sourceL N * sourceL N ^ 10 = sourceL N ^ 11 by ring]
  apply (errorBound_le_gauss hN hi eta).trans
  calc
    _ ≤ 3.024 * sourceL N ^ 7 * (N : ℝ) / sourceT N * sourceL N ^ 2 +
        0.001 * (N : ℝ) / sourceL N ^ 6 := by gcongr
    _ = _ := by unfold sourceT; field_simp; ring

def principalPayment (N q : ℕ) : ℝ :=
  (10 / 3.36) * (principalMass q * (q : ℝ)) * (N : ℝ) / sourceP N

theorem principal_payment {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q) {eta : ℝ}
    (heta : deltaRadius N q < |eta|) :
    ‖principalCoefficient q * J N eta‖ ≤ principalPayment N q := by
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hn := natCast_pos_of_exp_le hN
  have hP := sourceP_pos hN
  have hd := deltaRadius_pos hN hq
  have he : eta ≠ 0 := abs_pos.mp (hd.trans heta)
  rw [norm_mul, norm_principalCoefficient]
  calc
    _ ≤ principalMass q * (1 / (Real.pi * |eta|)) :=
      mul_le_mul_of_nonneg_left (OscillatoryBounds.J_reciprocal N he)
        (principalMass_nonneg q)
    _ ≤ principalMass q * (1 / (Real.pi * deltaRadius N q)) :=
      mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (mul_pos Real.pi_pos hd)
          (mul_le_mul_of_nonneg_left heta.le Real.pi_pos.le)) (principalMass_nonneg q)
    _ = principalPayment N q := by
      unfold principalPayment deltaRadius
      field_simp

theorem totient_ratio_le {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq0 : 0 < q)
    (hq : (q : ℝ) ≤ sourceP N) :
    (q : ℝ) / (q.totient : ℝ) ≤ 0.026 * sourceL N ^ 2 := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq0)
  have ht : (q : ℝ) ≤ 2 * (q.totient : ℝ) ^ 2 := by
    exact_mod_cast SingularSeries.le_two_mul_totient_sq q
  have hr : ((q : ℝ) / (q.totient : ℝ)) ^ 2 ≤ 2 * (q : ℝ) := by
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos hp 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (α := ℝ) q)]
  have hh : 2 * (q : ℝ) ≤ (0.026 * sourceL N ^ 2) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right
      (show (2 : ℝ) ≤ 0.026 ^ 2 * sourceL N by linarith [sourceL_ge_3100 hN])
      (pow_nonneg hL.le 3)
    change (q : ℝ) ≤ sourceL N ^ 3 at hq
    nlinarith
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp (hr.trans hh)

theorem principalPayment_le {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq0 : 0 < q)
    (hq : (q : ℝ) ≤ sourceP N) :
    principalPayment N q ≤ 0.078 * (N : ℝ) / sourceL N := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  have hm : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  have hmass : principalMass q * (q : ℝ) ≤ 0.026 * sourceL N ^ 2 := by
    calc
      _ = |(ArithmeticFunction.moebius q : ℝ)| * ((q : ℝ) / (q.totient : ℝ)) := by
        unfold principalMass; ring
      _ ≤ (q : ℝ) / (q.totient : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right hm
          (by positivity : 0 ≤ (q : ℝ) / (q.totient : ℝ))
      _ ≤ _ := totient_ratio_le hN hq0 hq
  unfold principalPayment
  calc
    _ ≤ (10 / 3.36) * (0.026 * sourceL N ^ 2) * (N : ℝ) / sourceP N := by gcongr
    _ = (13 / 168) * (N : ℝ) / sourceL N := by
      unfold sourceP; field_simp; ring
    _ ≤ _ := by gcongr; norm_num

theorem paid_terms_le {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq0 : 0 < q)
    (hq : (q : ℝ) ≤ sourceP N) :
    principalPayment N q + 3.025 * (N : ℝ) / sourceL N ^ 6 ≤
      0.0781 * (N : ℝ) / sourceL N := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hp : (30250 : ℝ) ≤ sourceL N ^ 5 :=
    (by norm_num : (30250 : ℝ) ≤ 3100 ^ 5).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 5)
  have he : 3.025 * (N : ℝ) / sourceL N ^ 6 ≤ 0.0001 * (N : ℝ) / sourceL N := by
    rw [show sourceL N ^ 6 = sourceL N ^ 5 * sourceL N by ring, div_mul_eq_div_div]
    apply div_le_div_of_nonneg_right _ hL.le
    apply (div_le_iff₀ (pow_pos hL 5)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) N)]
  have hm := principalPayment_le hN hq0 hq
  calc
    _ ≤ 0.078 * (N : ℝ) / sourceL N + 0.0001 * (N : ℝ) / sourceL N :=
      add_le_add hm he
    _ = _ := by ring

end LiuWang.Proof.NearArcPayment
