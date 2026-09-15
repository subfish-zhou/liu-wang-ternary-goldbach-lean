import LiuWang.Proof.CompleteExpansion.Consumer
import LiuWang.Proof.OscillatoryBounds.Consumer
import LiuWang.Proof.CharacterExpansion.GaussInduction

/-! The three original height bands in (5.20), on actual ordinary-L zeros. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion

namespace LiuWang.Proof.SourceRoute.ThirdArc

def lowHeight : ℝ := 10000 * Real.pi

def middleHeight (N q : ℕ) : ℝ :=
  10 * Real.pi * sourceL N ^ 7 / q

def lowKernel (N : ℕ) (rho : ℂ) : ℝ :=
  (1 - (0.001 : ℝ) ^ rho.re) / rho.re * (N : ℝ) ^ rho.re

def middleKernel (N : ℕ) (rho : ℂ) : ℝ :=
  16 * (0.001 : ℝ) ^ (rho.re - 1) * (N : ℝ) ^ rho.re / Real.sqrt |rho.im|

def highKernel (N : ℕ) (rho : ℂ) : ℝ :=
  5 * (N : ℝ) ^ rho.re / |rho.im|

def bandMass {q : ℕ} [NeZero q] (T u v : ℝ) (f : ℂ → ℝ) : ℝ :=
  ∑ chi : Character q,
    ∑ rho ∈ (zeroValues chi T).filter (fun rho => u ≤ |rho.im| ∧ |rho.im| ≤ v),
      (analyticOrderNatAt chi.LFunction rho : ℝ) * f rho

def sigma4 (N q : ℕ) [NeZero q] : ℝ :=
  Real.sqrt q / q.totient * bandMass (q := q) (sourceT N) 0 lowHeight (lowKernel N)

def sigma5 (N q : ℕ) [NeZero q] : ℝ :=
  Real.sqrt q / q.totient *
    bandMass (q := q) (sourceT N) lowHeight (middleHeight N q) (middleKernel N)

def sigma6 (N q : ℕ) [NeZero q] : ℝ :=
  Real.sqrt q / q.totient *
    bandMass (q := q) (sourceT N) (middleHeight N q) (sourceT N) (highKernel N)

theorem lowHeight_pos : 0 < lowHeight := by
  unfold lowHeight
  positivity

theorem middleHeight_pos {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) : 0 < middleHeight N q := by
  unfold middleHeight
  have := sourceL_pos hN
  have : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  positivity

theorem near_condition {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {eta gamma : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N))
    (hgamma : middleHeight N q ≤ |gamma|) :
    |eta| ≤ |gamma| / (10 * Real.pi * N) := by
  have hn := natCast_pos_of_exp_le hN
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  apply heta.trans
  apply (div_le_div_iff₀ (mul_pos hq hn) (by positivity)).mpr
  have hh := (div_le_iff₀ hq).mp hgamma
  nlinarith

theorem lowKernel_nonneg {N : ℕ} {rho : ℂ} (hb : 0 < rho.re) :
    0 ≤ lowKernel N rho := by
  have hp : (0.001 : ℝ) ^ rho.re ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) hb.le
  exact mul_nonneg (div_nonneg (sub_nonneg.mpr hp) hb.le)
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)

theorem three_kernel_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N))
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ zeroValues chi (sourceT N)) :
    ‖Jrho N rho eta‖ ≤
      (if 0 ≤ |rho.im| ∧ |rho.im| ≤ lowHeight then lowKernel N rho else 0) +
      (if lowHeight ≤ |rho.im| ∧ |rho.im| ≤ middleHeight N q then
        middleKernel N rho else 0) +
      (if middleHeight N q ≤ |rho.im| ∧ |rho.im| ≤ sourceT N then
        highKernel N rho else 0) := by
  obtain ⟨_, hb, hb1, ht, _⟩ := mem_zeroValues.mp hrho
  have hm : 0 ≤ middleKernel N rho := by unfold middleKernel; positivity
  have hh : 0 ≤ highKernel N rho := by unfold highKernel; positivity
  have hl := lowKernel_nonneg (N := N) hb
  have hn := nat_pos_of_exp_le hN
  have hmi : 0 ≤ (if lowHeight ≤ |rho.im| ∧ |rho.im| ≤ middleHeight N q then
      middleKernel N rho else 0) := by split_ifs <;> positivity
  have hhi : 0 ≤ (if middleHeight N q ≤ |rho.im| ∧ |rho.im| ≤ sourceT N then
      highKernel N rho else 0) := by split_ifs <;> positivity
  by_cases hlow : |rho.im| ≤ lowHeight
  · have hj := OscillatoryBounds.Jrho_weight hn hb eta
    change ‖Jrho N rho eta‖ ≤ lowKernel N rho at hj
    rw [if_pos ⟨abs_nonneg _, hlow⟩]
    linarith
  · have hg : rho.im ≠ 0 := by
      intro hz
      simp only [hz, abs_zero] at hlow
      exact hlow lowHeight_pos.le
    by_cases hmid : |rho.im| ≤ middleHeight N q
    · have hj := OscillatoryBounds.Jrho_sqrt hn hb1.le hg eta
      change ‖Jrho N rho eta‖ ≤ middleKernel N rho at hj
      rw [if_neg (by tauto : ¬(0 ≤ |rho.im| ∧ |rho.im| ≤ lowHeight)),
        if_pos ⟨(lt_of_not_ge hlow).le, hmid⟩]
      linarith
    · have hj := OscillatoryBounds.Jrho_near hn hb.le hg
        (near_condition hN heta (le_of_not_ge hmid))
      change ‖Jrho N rho eta‖ ≤ highKernel N rho at hj
      rw [if_neg (by tauto : ¬(0 ≤ |rho.im| ∧ |rho.im| ≤ lowHeight)),
        if_neg (by tauto : ¬(lowHeight ≤ |rho.im| ∧ |rho.im| ≤ middleHeight N q)),
        if_pos ⟨le_of_not_ge hmid, ht⟩]
      simpa only [zero_add] using hj

theorem family_three_bands {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    (∑ chi : Character q, ∑ rho ∈ zeroValues chi (sourceT N),
      (analyticOrderNatAt chi.LFunction rho : ℝ) * ‖Jrho N rho eta‖) ≤
      bandMass (q := q) (sourceT N) 0 lowHeight (lowKernel N) +
      bandMass (q := q) (sourceT N) lowHeight (middleHeight N q) (middleKernel N) +
      bandMass (q := q) (sourceT N) (middleHeight N q) (sourceT N) (highKernel N) := by
  simp only [bandMass, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro chi _
  apply Finset.sum_le_sum
  intro rho hrho
  have h := mul_le_mul_of_nonneg_left (three_kernel_bound hN heta hrho)
    (Nat.cast_nonneg (α := ℝ) (analyticOrderNatAt chi.LFunction rho))
  simpa only [mul_add, mul_ite, mul_zero] using h

theorem zeroPacket_three_bands {N q a : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (ha : Nat.Coprime a q) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    ‖zeroPacket q N a eta‖ ≤ sigma4 N q + sigma5 N q + sigma6 N q := by
  have hg (chi : Character q) : ‖G a chi‖ ≤ Real.sqrt q :=
    (norm_G_le_sqrt_conductor ha chi).trans
      (Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.le_of_dvd (NeZero.pos q)
        chi.conductor_dvd_level)))
  rw [zeroPacket_eq_all_values N a eta ha, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q,
        Real.sqrt q * ∑ rho ∈ zeroValues chi (sourceT N),
          (analyticOrderNatAt chi.LFunction rho : ℝ) * ‖Jrho N rho eta‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro chi _
      rw [norm_mul]
      apply mul_le_mul (hg chi) _ (norm_nonneg _) (by positivity)
      exact (norm_sum_le _ _).trans_eq (by
        simp only [norm_mul, Complex.norm_natCast])
    _ = (Real.sqrt q / q.totient) *
        ∑ chi : Character q, ∑ rho ∈ zeroValues chi (sourceT N),
          (analyticOrderNatAt chi.LFunction rho : ℝ) * ‖Jrho N rho eta‖ := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (family_three_bands hN heta)
        (show 0 ≤ Real.sqrt q / (q.totient : ℝ) by positivity)
      simpa only [sigma4, sigma5, sigma6, mul_add] using h

theorem S_three_bands {N q a : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      principalMass q * (0.999 * (N : ℝ)) + errorBound q N a eta +
        (sigma4 N q + sigma5 N q + sigma6 N q) := by
  have he := complete_error_function hN hi hq eta
  have hz := zeroPacket_three_bands hN hi.2.2 heta
  have hp : ‖principalCoefficient q * J N eta‖ ≤
      principalMass q * (0.999 * (N : ℝ)) := by
    rw [norm_mul, norm_principalCoefficient]
    exact mul_le_mul_of_nonneg_left (OscillatoryBounds.J_length N eta)
      (principalMass_nonneg q)
  calc
    _ = ‖principalCoefficient q * J N eta +
        (S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
          zeroPacket q N a eta) - zeroPacket q N a eta‖ := by congr 1; ring
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hp he)) hz)

end LiuWang.Proof.SourceRoute.ThirdArc
