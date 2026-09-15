import LiuWang.Proof.MiddleArcPayment.Scalar
import LiuWang.Proof.ZeroRegionFamily.RealClosure.Consumer

/-!
# Paying the actual rightmost packet using the frozen R24 family theorem

The finite sigma set contains ordinary L zero values, not surrogate points.
Its at-most-one bound is across the whole character family of a fixed q.
The possible exceptional real zero is paid, rather than removed.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.CompleteExpansion
open LiuWang.Proof.OscillatoryBounds

namespace LiuWang.Proof.MiddleArcPayment.Continuation

def rightmostPairs (q : ℕ) [NeZero q] (T x : ℝ) :
    Finset ((_ : Character q) × ℂ) :=
  Finset.univ.sigma (fun chi => (zeroValues chi T).filter
    (fun rho => ZeroRegionFamily.RealClosure.region x q rho))

theorem rightmostPairs_card_le_one {q : ℕ} [NeZero q] {T x : ℝ}
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) :
    (rightmostPairs q T x).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  rintro ⟨chi, rho⟩ hz ⟨psi, tau⟩ hw
  obtain ⟨hz, hr⟩ := Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2
  obtain ⟨hw, ht⟩ := Finset.mem_filter.mp (Finset.mem_sigma.mp hw).2
  have hzr := mem_zeroValues.mp hz
  have hzt := mem_zeroValues.mp hw
  have hr1 : rho ≠ 1 := by intro he; simp [he] at hzr
  have ht1 : tau ≠ 1 := by intro he; simp [he] at hzt
  obtain ⟨rfl, rfl⟩ := ZeroRegionFamily.RealClosure.single_modulus_unique hx hq
    chi psi hr ht (Or.inr hr1) (Or.inr ht1) hzr.1 hzt.1
  rfl

theorem rightmostPair_simple {q : ℕ} [NeZero q] {T x : ℝ}
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) {z : (_ : Character q) × ℂ}
    (hz : z ∈ rightmostPairs q T x) :
    z.1 ≠ 1 ∧ z.1 ^ 2 = 1 ∧ z.2.im = 0 ∧
      analyticOrderNatAt z.1.LFunction z.2 = 1 := by
  obtain ⟨hz, hr⟩ := Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2
  have hv := mem_zeroValues.mp hz
  have hp : z.2 ≠ 1 := by intro he; simp [he] at hv
  exact ZeroRegionFamily.RealClosure.zero_real_quadratic_simple hx hq z.1 hr (Or.inr hp) hv.1

theorem Jrho_le_window_length {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {rho : ℂ} (hb : rho.re ≤ 1) (eta : ℝ) :
    ‖Jrho N rho eta‖ ≤ 0.999 * (N : ℝ) := by
  have hlow : 1 ≤ sourceWindowLower N :=
    (one_le_pow₀ (one_le_sourceL hN) : 1 ≤ sourceT N).trans
      (sourceT_lt_windowLower hN).le
  have hlen : sourceWindowLower N ≤ (N : ℝ) := by
    unfold sourceWindowLower
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := sourceWindowLower N) (b := (N : ℝ)) (C := 1)
    (f := fun t : ℝ => (t : ℂ) ^ (rho - 1) *
      AnalyticNumberTheory.LargeSieve.charReal (eta * t)) (fun t ht => by
        rw [Set.uIoc_of_le hlen] at ht
        have ht1 : 1 ≤ t := hlow.trans ht.1.le
        rw [norm_cpow_charReal (by linarith) rho eta]
        exact Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith))
  have he : |(N : ℝ) - sourceWindowLower N| = 0.999 * N := by
    rw [abs_of_nonneg (sub_nonneg.mpr hlen), sourceWindowLower]
    ring
  simpa only [Jrho, one_mul, he] using h

def rightmostPacket (q N a : ℕ) [NeZero q] (eta x : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ z ∈ rightmostPairs q (sourceT N) x,
    G a z.1 * ((analyticOrderNatAt z.1.LFunction z.2 : ℂ) * Jrho N z.2 eta)

theorem norm_rightmostPacket_le {q N : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {x : ℝ} (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (a : ℕ) (ha : Nat.Coprime a q) (eta : ℝ) :
    ‖rightmostPacket q N a eta x‖ ≤
      (q.totient : ℝ)⁻¹ * (Real.sqrt q * (0.999 * (N : ℝ))) := by
  rw [rightmostPacket, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _z ∈ rightmostPairs q (sourceT N) x, Real.sqrt q * (0.999 * (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [(rightmostPair_simple hx hq hz).2.2.2, Nat.cast_one, one_mul, norm_mul]
      have hG := (norm_G_le_sqrt_conductor ha z.1).trans
        (Real.sqrt_le_sqrt (Nat.cast_le.mpr
          (BombieriVinogradov.DirichletCharacter.conductor_le_level z.1)))
      have hv := mem_zeroValues.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2).1
      exact mul_le_mul hG (Jrho_le_window_length hN hv.2.2.1.le eta)
        (norm_nonneg _) (by positivity)
    _ = ((rightmostPairs q (sourceT N) x).card : ℝ) *
        (Real.sqrt q * (0.999 * (N : ℝ))) := by simp
    _ ≤ _ := mul_le_of_le_one_left (by positivity)
      (by exact_mod_cast rightmostPairs_card_le_one (T := sourceT N) hx hq)

theorem upperPacket_eq_rightmost {q N : ℕ} [NeZero q] (a : ℕ) (eta x : ℝ)
    (hT : sourceT N ≤ x / (q : ℝ)) :
    upperPacket q N a eta (1 - 1 / (24 * Real.log x)) =
      rightmostPacket q N a eta x := by
  unfold upperPacket rightmostPacket rightmostPairs
  rw [Finset.sum_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  rw [upperRealSum, Finset.mul_sum]
  apply Finset.sum_congr
  · ext rho
    constructor
    · intro h
      obtain ⟨hz, hr⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨hz, hr, (mem_zeroValues.mp hz).2.2.2.1.trans hT⟩
    · intro h
      obtain ⟨hz, hr⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨hz, hr.1⟩
  · intro rho _
    rfl

theorem upperPacket_R24_paid {q N : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {x : ℝ} (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x)
    (hT : sourceT N ≤ x / (q : ℝ)) (a : ℕ) (ha : Nat.Coprime a q) (eta : ℝ) :
    ‖upperPacket q N a eta (1 - 1 / (24 * Real.log x))‖ ≤
      (q.totient : ℝ)⁻¹ * (Real.sqrt q * (0.999 * (N : ℝ))) := by
  rw [upperPacket_eq_rightmost a eta x hT]
  exact norm_rightmostPacket_le hN hx hq a ha eta

end LiuWang.Proof.MiddleArcPayment.Continuation
