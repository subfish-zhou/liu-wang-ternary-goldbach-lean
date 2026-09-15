import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1.EulerTransport

/-! Exact modulus/conductor prime support in LWD Lemmas 2.2--2.5. -/

set_option autoImplicit false
noncomputable section

open Finset
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1

theorem s_nonneg (q : ℕ) {sigma : ℝ} (hs : 1 < sigma) : 0 ≤ s q sigma := by
  rw [s_eq]
  exact sum_nonneg (fun p hp => primeCost_nonneg (Nat.prime_of_mem_primeFactors hp) hs)

theorem badS_add_s {q1 q : ℕ} (hq1 : q1 ≠ 0) (hq : q ≠ 0) (hd : q1 ∣ q)
    (sigma : ℝ) : badS q1 q sigma + s q1 sigma = s q sigma := by
  have he : q.primeFactors.filter (fun p => p ∣ q1) = q1.primeFactors := by
    ext p
    simp only [mem_filter, Nat.mem_primeFactors_of_ne_zero hq,
      Nat.mem_primeFactors_of_ne_zero hq1]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2.trans hd⟩, h.2⟩
  unfold badS s
  rw [← he, sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  by_cases hp : p ∣ q1 <;> simp [hp]

theorem badS_eq_sub {q1 q : ℕ} (hq1 : q1 ≠ 0) (hq : q ≠ 0) (hd : q1 ∣ q)
    (sigma : ℝ) : badS q1 q sigma = s q sigma - s q1 sigma := by
  linarith [badS_add_s hq1 hq hd sigma]

theorem badS_le_s {q1 q : ℕ} (hq1 : q1 ≠ 0) (hq : q ≠ 0) (hd : q1 ∣ q)
    {sigma : ℝ} (hs : 1 < sigma) : badS q1 q sigma ≤ s q sigma := by
  rw [badS_eq_sub hq1 hq hd]
  exact sub_le_self _ (s_nonneg q1 hs)

theorem primitive_badS_zero {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hp : chi.IsPrimitive) (sigma : ℝ) : badS chi.conductor q sigma = 0 := by
  rw [show chi.conductor = q from hp, badS_eq_sub (NeZero.ne q) (NeZero.ne q) dvd_rfl]
  exact sub_self _

end LiuWang.Proof.SourceRoute.Exception.Restart.OriginalV1
