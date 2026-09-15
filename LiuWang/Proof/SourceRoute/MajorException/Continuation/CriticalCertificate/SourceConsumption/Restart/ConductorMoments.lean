import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart.WeightedTotient

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart

def multipleMoment (P : ℝ) (r : ℕ) (s : ℝ) : ℝ :=
  ∑ q ∈ denominators P, if r ∣ q then (q:ℝ)^s/(q.totient:ℝ)^2 else 0

theorem multipleMoment_nonneg (P : ℝ) (r : ℕ) (s : ℝ) : 0 ≤ multipleMoment P r s := by
  apply sum_nonneg
  intro q _
  split_ifs <;> positivity

theorem multipleMoment_low (P : ℝ) {r : ℕ} (hr : 0 < r) {s : ℝ} (hs : s < 1) :
    multipleMoment P r s ≤ 22*(1+1/(1-s))*(r:ℝ)^s/(r.totient:ℝ)^2 := by
  have h := totientMoment_multiples ⌊P⌋₊ hr s
  have hb : totientMoment (⌊P⌋₊/r) s ≤ 22*(1+1/(1-s)) := by
    by_cases hx : (⌊P⌋₊/r : ℕ) = 0
    · simp only [hx, totientMoment, Icc_eq_empty_of_lt (by norm_num : (0:ℕ)<1), sum_empty]
      positivity
    · exact totientMoment_low (X := ⌊P⌋₊/r) (Nat.one_le_iff_ne_zero.mpr hx) hs
  exact h.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring))

theorem multipleMoment_power {P : ℝ} (hP : 0 ≤ P) {r : ℕ} (hr : 0 < r)
    {s C : ℝ} (hs : 1 < s) (hC : 0 ≤ C)
    (hb : ∀ X : ℕ, 1 ≤ X → totientMoment X s ≤ C*(X:ℝ)^(s-1)) :
    multipleMoment P r s ≤ C*(r:ℝ)/(r.totient:ℝ)^2*P^(s-1) := by
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast hr
  have h := totientMoment_multiples ⌊P⌋₊ hr s
  by_cases hx : (⌊P⌋₊/r : ℕ) = 0
  · have he : totientMoment (⌊P⌋₊/r) s = 0 := by simp [hx, totientMoment]
    exact (h.trans_eq (by rw [he, mul_zero])).trans (by positivity)
  · have hm : (r:ℝ)*(⌊P⌋₊/r:ℕ) ≤ P :=
      (show (r:ℝ)*(⌊P⌋₊/r:ℕ) ≤ (⌊P⌋₊:ℝ) by
        exact_mod_cast Nat.mul_div_le ⌊P⌋₊ r).trans (Nat.floor_le hP)
    have he : (r:ℝ)^s = (r:ℝ)*(r:ℝ)^(s-1) := by
      nth_rw 1 [show s = 1+(s-1) by ring]
      rw [Real.rpow_add hr0, Real.rpow_one]
    calc
      _ ≤ (r:ℝ)^s/(r.totient:ℝ)^2*totientMoment (⌊P⌋₊/r) s := h
      _ ≤ (r:ℝ)^s/(r.totient:ℝ)^2*(C*(⌊P⌋₊/r:ℕ)^(s-1)) :=
        mul_le_mul_of_nonneg_left (hb (⌊P⌋₊/r) (Nat.one_le_iff_ne_zero.mpr hx)) (by positivity)
      _ = C*(r:ℝ)/(r.totient:ℝ)^2*((r:ℝ)*(⌊P⌋₊/r:ℕ))^(s-1) := by
        rw [he, Real.mul_rpow hr0.le (Nat.cast_nonneg _)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hm (by linarith)) (by positivity)

theorem multipleMoment_high {P : ℝ} (hP : 0 ≤ P) {r : ℕ} (hr : 0 < r)
    {s : ℝ} (hs : 1 < s) (hs2 : s ≤ 2) :
    multipleMoment P r s ≤ (22/(s-1))*(r:ℝ)/(r.totient:ℝ)^2*P^(s-1) :=
  multipleMoment_power hP hr hs (by positivity)
    (fun _ hX => totientMoment_high hX hs hs2)

theorem multipleMoment_large {P : ℝ} (hP : 0 ≤ P) {r : ℕ} (hr : 0 < r)
    {s : ℝ} (hs : 2 ≤ s) :
    multipleMoment P r s ≤ 22*(r:ℝ)/(r.totient:ℝ)^2*P^(s-1) :=
  multipleMoment_power hP hr (by linarith) (by norm_num)
    (fun _ hX => totientMoment_large hX hs)

theorem original_five_moments {P : ℝ} (hP : 0 ≤ P) {r : ℕ} (hr : 0 < r) :
    multipleMoment P r (1/6) ≤ 48.4*(r:ℝ)^(1/6:ℝ)/(r.totient:ℝ)^2 ∧
    multipleMoment P r (7/6) ≤ 132*(r:ℝ)/(r.totient:ℝ)^2*P^(1/6:ℝ) ∧
    multipleMoment P r (1/3) ≤ 55*(r:ℝ)^(1/3:ℝ)/(r.totient:ℝ)^2 ∧
    multipleMoment P r (4/3) ≤ 66*(r:ℝ)/(r.totient:ℝ)^2*P^(1/3:ℝ) ∧
    multipleMoment P r (7/3) ≤ 22*(r:ℝ)/(r.totient:ℝ)^2*P^(4/3:ℝ) := by
  constructor
  · convert multipleMoment_low P hr (by norm_num : (1/6:ℝ)<1) using 1
    norm_num
  constructor
  · convert multipleMoment_high hP hr (by norm_num : (1:ℝ)<7/6) (by norm_num) using 1
    norm_num
  constructor
  · convert multipleMoment_low P hr (by norm_num : (1/3:ℝ)<1) using 1
    norm_num
  constructor
  · convert multipleMoment_high hP hr (by norm_num : (1:ℝ)<4/3) (by norm_num) using 1
    norm_num
  · convert multipleMoment_large hP hr (by norm_num : (2:ℝ)≤7/3) using 1
    norm_num

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.Restart
