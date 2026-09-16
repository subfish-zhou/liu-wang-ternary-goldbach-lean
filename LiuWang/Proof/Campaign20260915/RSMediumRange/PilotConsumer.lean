import LiuWang.Proof.Campaign20260915.RSMediumRange.KernelPilot

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

def pilotPrimes : Finset ℕ := (kernelPilotRows.map Prod.fst).toFinset

theorem pilot_prime_difference :
    Nat.primesLE 99615071 \ Nat.primesLE 99614736 = pilotPrimes := by
  ext p
  constructor
  · intro h
    simp only [Finset.mem_sdiff, Nat.mem_primesLE] at h
    have hlo : 99614737 ≤ p := by
      by_contra! hh
      exact h.2 ⟨by omega, h.1.2⟩
    exact List.mem_toFinset.mpr
      ((kernelPilot_complete p (Finset.mem_Icc.mpr ⟨hlo, h.1.1⟩)).mp h.1.2)
  · intro h
    have hm := List.mem_toFinset.mp h
    have hb : 99614737 ≤ p ∧ p ≤ 99615071 := by
      norm_num [pilotPrimes, kernelPilotRows] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hp := (kernelPilot_complete p (Finset.mem_Icc.mpr hb)).mpr hm
    simp only [Finset.mem_sdiff, Nat.mem_primesLE]
    exact ⟨⟨hb.2, hp⟩, fun h => by omega⟩

theorem pilot_prime_count :
    (Nat.primesLE 99615071 \ Nat.primesLE 99614736).card = 16 := by
  rw [pilot_prime_difference]
  decide +kernel

private theorem pilot_subset :
    Nat.primesLE 99614736 ⊆ Nat.primesLE 99615071 := by
  intro p hp
  obtain ⟨hb, hp⟩ := Nat.mem_primesLE.mp hp
  exact Nat.mem_primesLE.mpr ⟨by omega, hp⟩

theorem pilot_theta_difference :
    Chebyshev.theta 99615071 - Chebyshev.theta 99614736 =
      ∑ p ∈ pilotPrimes, Real.log p := by
  change Chebyshev.theta ((99615071 : ℕ) : ℝ) - Chebyshev.theta ((99614736 : ℕ) : ℝ) = _
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  rw [← pilot_prime_difference]
  exact (Finset.sum_sdiff_eq_sub pilot_subset).symm

theorem pilot_theta_bounds :
    (29466915417772204 : ℝ) / fixedScale ≤
      Chebyshev.theta 99615071 - Chebyshev.theta 99614736 ∧
      Chebyshev.theta 99615071 - Chebyshev.theta 99614736 ≤
        (29466915440172560 : ℝ) / fixedScale := by
  have hlo :
      ∑ r ∈ kernelPilotRows.toFinset, (r.2.2.1 : ℝ) / fixedScale ≤
        ∑ r ∈ kernelPilotRows.toFinset, Real.log r.1 :=
    Finset.sum_le_sum (fun r hr => (kernelPilot_log_bounds (List.mem_toFinset.mp hr)).1)
  have hhi :
      ∑ r ∈ kernelPilotRows.toFinset, Real.log r.1 ≤
        ∑ r ∈ kernelPilotRows.toFinset, (r.2.2.2 : ℝ) / fixedScale :=
    Finset.sum_le_sum (fun r hr => (kernelPilot_log_bounds (List.mem_toFinset.mp hr)).2)
  rw [pilot_theta_difference]
  norm_num [kernelPilotRows, pilotPrimes, fixedScale] at hlo hhi ⊢
  exact ⟨hlo, hhi⟩

theorem pilot_euler_increment :
    (Totient.prefixEuler 99615071 : ℝ) ≤
      (Totient.prefixEuler 99614736 : ℝ) *
        ((100000016061866 : ℝ) / fixedScale) := by
  have hid : Totient.prefixEuler 99615071 =
      (∏ p ∈ pilotPrimes, (p : ℚ) / (p - 1)) * Totient.prefixEuler 99614736 := by
    rw [← pilot_prime_difference]
    exact (Finset.prod_sdiff pilot_subset).symm
  have hbound : (∏ p ∈ pilotPrimes, (p : ℚ) / (p - 1)) ≤
      (100000016061866 : ℚ) / fixedScale := by
    norm_num [pilotPrimes, kernelPilotRows, fixedScale]
  have hpos : (0 : ℝ) ≤ (Totient.prefixEuler 99614736 : ℝ) := by
    unfold Totient.prefixEuler
    push_cast
    apply Finset.prod_nonneg
    intro p hp
    have h := (Nat.mem_primesLE.mp hp).2.two_le
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast h
    exact div_nonneg (Nat.cast_nonneg p) (by linarith)
  rw [hid]
  push_cast
  have hr := Rat.cast_le (K := ℝ) |>.mpr hbound
  push_cast at hr
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hr hpos

#print axioms pilot_prime_count
#print axioms pilot_theta_bounds
#print axioms pilot_euler_increment

end LiuWang.Proof.Campaign20260915.RSMediumRange
