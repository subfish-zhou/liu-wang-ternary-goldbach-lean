import LiuWang.Proof.NearArcPayment.Integral
import LiuWang.Proof.DirichletZeroCount.Applications.CompleteValues

/-!
# A fixed left-strip payment without a density estimate

Only the frozen full-height count is used. Every actual zero with real part
at most 3/4, including real zeros, is paid uniformly in eta. The right-strip
packet is retained with its original signs and multiplicities.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation

open Interfaces Parameters CompleteExpansion CharacterExpansion

theorem count_complete_le {q : ℕ} [NeZero q] (chi : Character q)
    {y : ℝ} (hy : 10000 ≤ y) :
    (∑ rho ∈ zeroValues chi y, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      10 * y * Real.log ((q : ℝ) * y) := by
  rw [← Nat.cast_sum, ← DirichletZeroCount.Applications.count_half_eq_complete]
  by_cases hc : chi = 1
  · subst chi
    exact (DirichletZeroCount.count_principal_le q (1 / 2) (by linarith)).trans
      (DirichletZeroCount.Applications.principalBound_le_ten (q := q) hy)
  · exact (DirichletZeroCount.count_le_modulus hc (1 / 2) (by linarith)).trans
      (DirichletZeroCount.Applications.nonprincipalBound_le_ten hy)

theorem Jrho_left_strip {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {rho : ℂ} (hb : 1 / 2 ≤ rho.re) (hu : rho.re ≤ 3 / 4) (eta : ℝ) :
    ‖Jrho N rho eta‖ ≤ 2 * (N : ℝ) ^ ((3 : ℝ) / 4) := by
  have hn := natCast_pos_of_exp_le hN
  have hn1 : (1 : ℝ) ≤ N := by
    exact_mod_cast nat_pos_of_exp_le hN
  have hc : (1 - (0.001 : ℝ) ^ rho.re) / rho.re ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < rho.re)).mpr
    linarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0.001) rho.re]
  calc
    _ ≤ (1 - (0.001 : ℝ) ^ rho.re) / rho.re * (N : ℝ) ^ rho.re :=
      OscillatoryBounds.Jrho_weight (nat_pos_of_exp_le hN) (by linarith) eta
    _ ≤ 2 * (N : ℝ) ^ rho.re :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 hu) (by norm_num)

def leftValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) : Finset ℂ :=
  (zeroValues chi (sourceT N)).filter (fun rho => rho.re ≤ 3 / 4)

def rightValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) : Finset ℂ :=
  (zeroValues chi (sourceT N)).filter (fun rho => 3 / 4 < rho.re)

def leftPacket (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ leftValues chi N,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

def rightPacket (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ rightValues chi N,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem zeroPacket_eq_left_add_right {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ)
    (hi : sourceIndex a q) :
    zeroPacket q N a eta = leftPacket q N a eta + rightPacket q N a eta := by
  rw [zeroPacket_eq_all_values N a eta hi.2.2]
  unfold leftPacket rightPacket zeroValueSum leftValues rightValues
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hb : rho.re ≤ 3 / 4 <;> simp [hb]

theorem norm_leftPacket_le_count {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (eta : ℝ) :
    ‖leftPacket q N a eta‖ ≤
      Real.sqrt (q : ℝ) * (2 * (N : ℝ) ^ ((3 : ℝ) / 4)) *
        (10 * sourceT N * Real.log ((q : ℝ) * sourceT N)) := by
  have hT : 10000 ≤ sourceT N :=
    (by norm_num : (10000 : ℝ) ≤ 2000 ^ 15).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_2000 hN) 15)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hlog : 0 ≤ Real.log ((q : ℝ) * sourceT N) :=
    Real.log_nonneg (by nlinarith)
  have hphi : (0 : ℝ) < q.totient :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hsum (chi : Character q) :
      ‖∑ rho ∈ leftValues chi N,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      (2 * (N : ℝ) ^ ((3 : ℝ) / 4)) *
        (10 * sourceT N * Real.log ((q : ℝ) * sourceT N)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ rho ∈ leftValues chi N,
          (analyticOrderNatAt chi.LFunction rho : ℝ) *
            (2 * (N : ℝ) ^ ((3 : ℝ) / 4)) := by
        apply Finset.sum_le_sum
        intro rho hr
        obtain ⟨hr, hb⟩ := Finset.mem_filter.mp hr
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left
          (Jrho_left_strip hN (mem_zeroValues.mp hr).2.2.2.2 hb eta) (Nat.cast_nonneg _)
      _ ≤ (∑ rho ∈ zeroValues chi (sourceT N),
          (analyticOrderNatAt chi.LFunction rho : ℝ)) *
            (2 * (N : ℝ) ^ ((3 : ℝ) / 4)) := by
        rw [← Finset.sum_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ _ := by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_right (count_complete_le chi hT)
            (by positivity : 0 ≤ 2 * (N : ℝ) ^ ((3 : ℝ) / 4))
  unfold leftPacket
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q,
        ‖G a chi‖ * ((2 * (N : ℝ) ^ ((3 : ℝ) / 4)) *
          (10 * sourceT N * Real.log ((q : ℝ) * sourceT N))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro chi _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hsum chi) (norm_nonneg _)
    _ = ((q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖) *
        ((2 * (N : ℝ) ^ ((3 : ℝ) / 4)) *
          (10 * sourceT N * Real.log ((q : ℝ) * sourceT N))) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ Real.sqrt (q.totient : ℝ) *
        ((2 * (N : ℝ) ^ ((3 : ℝ) / 4)) *
          (10 * sourceT N * Real.log ((q : ℝ) * sourceT N))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        _ ≤ (q.totient : ℝ)⁻¹ * (Real.sqrt (q.totient : ℝ) * (q.totient : ℝ)) :=
          mul_le_mul_of_nonneg_left (NonprincipalPacket.sum_norm_G_le a) (by positivity)
        _ = _ := by field_simp
    _ ≤ _ := by
      simp only [mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le q)

theorem norm_leftPacket_le_polynomial {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (eta : ℝ) :
    ‖leftPacket q N a eta‖ ≤
      360 * sourceL N ^ 19 * (N : ℝ) ^ ((3 : ℝ) / 4) := by
  have hL := sourceL_pos hN
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hT := sourceT_pos hN
  have hs : Real.sqrt (q : ℝ) ≤ sourceL N ^ 3 :=
    ((Real.sqrt_le_iff).mpr ⟨hq0.le, by nlinarith⟩).trans hq
  have hh : Real.log ((q : ℝ) * sourceT N) ≤ 18 * sourceL N := by
    calc
      _ ≤ Real.log (sourceL N ^ 18) := by
        apply Real.log_le_log (mul_pos hq0 hT)
        have hp := mul_le_mul_of_nonneg_right hq hT.le
        simpa only [sourceP, sourceT, ← pow_add] using hp
      _ = 18 * Real.log (sourceL N) := by rw [Real.log_pow]; norm_num
      _ ≤ _ := by
        have hl := Real.log_le_sub_one_of_pos hL
        linarith
  have hlog : 0 ≤ Real.log ((q : ℝ) * sourceT N) := by
    apply Real.log_nonneg
    have ht : 1 ≤ sourceT N := one_le_pow₀ (one_le_sourceL hN)
    nlinarith
  apply (norm_leftPacket_le_count hN eta).trans
  calc
    _ ≤ sourceL N ^ 3 * (2 * (N : ℝ) ^ ((3 : ℝ) / 4)) *
        (10 * sourceT N * (18 * sourceL N)) := by gcongr
    _ = _ := by unfold sourceT; ring

theorem polynomial_le_exp_quarter {x : ℝ} (hx : 3100 ≤ x) :
    3600000 * x ^ 20 ≤ Real.exp (x / 4) := by
  have hx0 : 0 ≤ x := by linarith
  have he := Real.quadratic_le_exp_of_nonneg (x := x / 192) (by positivity)
  have hquad : x ^ 2 / (2 * 192 ^ 2) ≤ Real.exp (x / 192) := by nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ x ^ 2 / (2 * 192 ^ 2)) hquad 2
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat] at hp
  have hc : (4 * 192 ^ 4 : ℝ) ≤ x ^ 3 :=
    (by norm_num : (4 * 192 ^ 4 : ℝ) ≤ 3100 ^ 3).trans
      (pow_le_pow_left₀ (by norm_num) hx 3)
  have hsmall : x ≤ Real.exp (x / 96) := by
    have hh := mul_le_mul_of_nonneg_right hc hx0
    rw [show (2 : ℝ) * (x / 192) = x / 96 by ring] at hp
    nlinarith
  have h24 := pow_le_pow_left₀ hx0 hsmall 24
  rw [← Real.exp_nat_mul] at h24
  norm_num only [Nat.cast_ofNat] at h24
  rw [show (24 : ℝ) * (x / 96) = x / 4 by ring] at h24
  have h4 : (3600000 : ℝ) ≤ x ^ 4 :=
    (by norm_num : (3600000 : ℝ) ≤ 3100 ^ 4).trans
      (pow_le_pow_left₀ (by norm_num) hx 4)
  calc
    _ ≤ x ^ 4 * x ^ 20 := mul_le_mul_of_nonneg_right h4 (pow_nonneg hx0 20)
    _ = x ^ 24 := by ring
    _ ≤ _ := h24

theorem norm_leftPacket_le_paid {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (eta : ℝ) :
    ‖leftPacket q N a eta‖ ≤ 0.0001 * (N : ℝ) / sourceL N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hn := natCast_pos_of_exp_le hN
  have hL := sourceL_pos hN0
  have he : Real.exp (sourceL N / 4) = (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [Real.rpow_def_of_pos hn]
    congr 1
    unfold sourceL
    ring
  have hp := polynomial_le_exp_quarter (sourceL_ge_3100 hN)
  rw [he] at hp
  have hm := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hn.le ((3 : ℝ) / 4))
  have hprod : (N : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((3 : ℝ) / 4) = N := by
    rw [← Real.rpow_add hn]
    norm_num
  rw [hprod] at hm
  apply (norm_leftPacket_le_polynomial hN0 hq eta).trans
  apply (le_div_iff₀ hL).mpr
  nlinarith [show sourceL N ^ 19 * sourceL N = sourceL N ^ 20 by ring]

end LiuWang.Proof.NearArcPayment.Continuation
