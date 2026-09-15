import LiuWang.Proof.MiddleArcPayment.Dyadic

/-!
# Same-witness M3 consumer with all errors paid and actual residual zeros

The residual uses beta > b, not an exceptional-zero deletion. Taking b=1
removes it by the literal open upper boundary of the actual zero window.
The general b consumer retains cancellation between the principal term and
the complete high-real-part packet.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.CompleteExpansion

namespace LiuWang.Proof.MiddleArcPayment

def upperPacket (q N a : ℕ) [NeZero q] (eta b : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi * upperRealSum chi N eta b

def countPayment (q N a : ℕ) [NeZero q] (eta b : ℝ) : ℝ :=
  (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
    dyadicCountBound chi N eta b 1 2 (sourceDyadicHeight N)

theorem countPayment_eq_conductors (q N a : ℕ) [NeZero q] (eta b : ℝ) :
    countPayment q N a eta b =
      (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors, ∑ chi ∈ conductorCharacters q d,
        ‖G a chi‖ * dyadicCountBound chi N eta b 1 2 (sourceDyadicHeight N) := by
  rw [sum_conductorCharacters]
  rfl

theorem zeroPacket_sub_upper_le {q N : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (a : ℕ) (eta b : ℝ)
    (haq : Nat.Coprime a q) :
    ‖zeroPacket q N a eta - upperPacket q N a eta b‖ ≤ countPayment q N a eta b := by
  have he : zeroPacket q N a eta - upperPacket q N a eta b =
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q,
        G a chi * (zeroValueSum chi N (sourceT N) eta - upperRealSum chi N eta b) := by
    rw [zeroPacket_eq_all_values N a eta haq]
    simp only [upperPacket, mul_sub, Finset.sum_sub_distrib]
  rw [he, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro chi _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (zeroValueSum_sub_upper_le chi N eta b).trans
    (lowerRealMass_le_dyadic hN chi eta b (by norm_num) (by norm_num)
      (by simpa using sourceDyadicHeight_covers hN))

theorem complete_upper_error {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) (eta b : ℝ) :
    ‖S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
      upperPacket q N a eta b‖ ≤ errorBound q N a eta + countPayment q N a eta b := by
  have he := complete_error_function hN hi hq eta
  have hc := zeroPacket_sub_upper_le hN a eta b hi.2.2
  calc
    _ = ‖(S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
        zeroPacket q N a eta) - (zeroPacket q N a eta - upperPacket q N a eta b)‖ := by
      congr 1
      ring
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add he hc)

theorem S_le_countPayment {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) (eta b : ℝ) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      ‖principalCoefficient q * J N eta - upperPacket q N a eta b‖ +
        countPayment q N a eta b + errorBound q N a eta := by
  have he := complete_upper_error hN hi hq eta b
  calc
    _ = ‖(principalCoefficient q * J N eta - upperPacket q N a eta b) +
        (S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
          upperPacket q N a eta b)‖ := by congr 1; ring
    _ ≤ ‖principalCoefficient q * J N eta - upperPacket q N a eta b‖ +
        (errorBound q N a eta + countPayment q N a eta b) :=
      (norm_add_le _ _).trans (add_le_add le_rfl he)
    _ = _ := by ring

@[simp] theorem upperRealSum_one {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (eta : ℝ) : upperRealSum chi N eta 1 = 0 := by
  apply Finset.sum_eq_zero
  intro rho hrho
  obtain ⟨hz, hb⟩ := Finset.mem_filter.mp hrho
  have hr := (CompleteExpansion.mem_zeroValues.mp hz).2.2.1
  linarith

@[simp] theorem upperPacket_one (q N a : ℕ) [NeZero q] (eta : ℝ) :
    upperPacket q N a eta 1 = 0 := by simp [upperPacket]

theorem S_le_full_count {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      principalBound q N eta + countPayment q N a eta 1 + errorBound q N a eta := by
  have h := S_le_countPayment hN hi hq eta 1
  rw [upperPacket_one, sub_zero, norm_mul, norm_principalCoefficient] at h
  apply h.trans
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_left (OscillatoryBounds.J_bound N eta) (principalMass_nonneg q)

def middleBound (q N a : ℕ) [NeZero q] (eta b : ℝ) : ℝ :=
  min (principalBound q N eta + jointPacketBound q N a eta)
    (min (‖principalCoefficient q * J N eta - upperPacket q N a eta b‖ +
      countPayment q N a eta b) (principalBound q N eta + countPayment q N a eta 1)) +
    0.000000000001 * (N : ℝ) / sourceL N

theorem middleBound_valid {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq0 : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N)
    {eta : ℝ} (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) (b : ℝ) :
    ‖S N (rationalCenter a q + eta)‖ ≤ middleBound q N a eta b := by
  have he := middle_error_regression (a := a) hN hq0 hq1 heta
  have hj := M3_joint_bound hN hi hq0 hq1 heta
  have hc := (S_le_countPayment hN hi hq1 eta b).trans (add_le_add le_rfl he)
  have hf := (S_le_full_count hN hi hq1 eta).trans (add_le_add le_rfl he)
  unfold middleBound
  rw [← min_add_add_right, ← min_add_add_right]
  exact le_min hj (le_min hc hf)

theorem M3_payment {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (ha : alpha ∈ M3 N) (b : ℝ) :
    ∃ (q a : ℕ) (eta : ℝ) (hq : 0 < q),
      letI : NeZero q := ⟨hq.ne'⟩
      sourceL N ^ 3 < (q : ℝ) ∧ (q : ℝ) ≤ sourceL N ^ 6 ∧
      sourceIndex a q ∧ alpha = rationalCenter a q + eta ∧
      |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N) ∧
      ‖S N alpha‖ ≤ middleBound q N a eta b := by
  obtain ⟨q, a, eta, hq, hq0, hq1, hi, he, heta, _⟩ := M3_fixed_witness hN ha
  let : NeZero q := ⟨hq.ne'⟩
  refine ⟨q, a, eta, hq, hq0, hq1, hi, he, heta, ?_⟩
  rw [he]
  exact middleBound_valid hN hi hq0 hq1 heta b

end LiuWang.Proof.MiddleArcPayment
