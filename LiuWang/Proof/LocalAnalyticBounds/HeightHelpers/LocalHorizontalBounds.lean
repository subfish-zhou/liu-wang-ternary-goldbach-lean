import LiuWang.Proof.LocalAnalyticBounds.HeightSelection

/-!
# 所选水平边附近的本函数非零性与倒数核界

这里只运输已证的零点距离：在正实部半平面给出局部非零性，
并给出单个零点倒数核的范数界。不引入对数导数求和或积分余项预算。
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.LocalAnalyticBounds

theorem source_height_budget_pos {q : Nat} (hq : 3 ≤ q)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    0 < 1.7769 * Real.log ((q : Real) * T) := by
  have hqr : (3 : Real) ≤ q := by exact_mod_cast hq
  have hTr : (2 : Real) ≤ T :=
    (by norm_num : (2 : Real) ≤ 2000 ^ (15 : Nat)).trans hT
  have hprod : 1 < (q : Real) * T := by nlinarith
  exact mul_pos (by norm_num) (Real.log_pos hprod)

theorem LFunction_ne_zero_near_separated_height
    {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {H r : Real}
    (hsep : ∀ p : CompletedZeroIndex chi, r ≤ |(completedZeroValue p).im - H|)
    {s : Complex} (hs : 0 < s.re) (hnear : |s.im - H| < r) :
    chi.LFunction s ≠ 0 := by
  intro hz
  exact not_lt_of_ge (LFunction_zero_separated_of_index hchi hPrimitive hsep hs hz) hnear

theorem norm_inv_sub_le_of_separated_height
    {H B : Real} (hB : 0 < B) {rho s : Complex}
    (hsep : B⁻¹ ≤ |rho.im - H|) (hs : s.im = H) :
    ‖(s - rho)⁻¹‖ ≤ B := by
  have hnorm : B⁻¹ ≤ ‖s - rho‖ := by
    have hi := Complex.abs_im_le_norm (s - rho)
    simp only [Complex.sub_im, hs] at hi
    rw [abs_sub_comm H rho.im] at hi
    exact hsep.trans hi
  have hnpos : 0 < ‖s - rho‖ := lt_of_lt_of_le (inv_pos.mpr hB) hnorm
  rw [norm_inv, ← one_div]
  apply (div_le_iff₀ hnpos).mpr
  have hm := mul_le_mul_of_nonneg_right hnorm hB.le
  rw [inv_mul_cancel₀ hB.ne'] at hm
  simpa only [mul_comm] using hm

theorem norm_inv_sub_le_near_separated_height
    {H B : Real} (hB : 0 < B) {rho s : Complex}
    (hsep : B⁻¹ ≤ |rho.im - H|) (hs : |s.im - H| ≤ B⁻¹ / 2) :
    ‖(s - rho)⁻¹‖ ≤ 2 * B := by
  have htri := abs_sub_le rho.im s.im H
  rw [abs_sub_comm rho.im s.im] at htri
  have hi := Complex.abs_im_le_norm (s - rho)
  simp only [Complex.sub_im] at hi
  have hn : B⁻¹ / 2 ≤ ‖s - rho‖ := by linarith
  have hnpos : 0 < ‖s - rho‖ := lt_of_lt_of_le (by positivity) hn
  rw [norm_inv, ← one_div]
  apply (div_le_iff₀ hnpos).mpr
  have hm := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ 2 * B)
  have hcancel : B⁻¹ / 2 * (2 * B) = 1 := by field_simp
  rw [hcancel] at hm
  simpa only [mul_comm] using hm

theorem exists_source_rectangle_local_bounds
    {q : Nat} [NeZero q] (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {T : Real} (hT : (2000 : Real) ^ (15 : Nat) ≤ T) :
    ∃ Hplus Hminus : Real, |Hplus - T| ≤ 1 ∧ |Hminus + T| ≤ 1 ∧
      ∀ H ∈ ({Hplus, Hminus} : Set Real),
        (∀ s : Complex, 0 < s.re →
          |s.im - H| < (1.7769 * Real.log ((q : Real) * T))⁻¹ →
          chi.LFunction s ≠ 0) ∧
        (∀ rho : Complex, 0 < rho.re → rho.re < 1 → chi.LFunction rho = 0 →
          ∀ s : Complex, |s.im - H| ≤ (1.7769 * Real.log ((q : Real) * T))⁻¹ / 2 →
            ‖(s - rho)⁻¹‖ ≤ 2 * (1.7769 * Real.log ((q : Real) * T))) := by
  obtain ⟨Hp, Hm, hp, hm, hsep⟩ :=
    exists_source_rectangle_heights_index hq hchi hPrimitive hT
  have hB := source_height_budget_pos hq hT
  refine ⟨Hp, Hm, hp, hm, fun H hH => ?_⟩
  have hsepH : ∀ p : CompletedZeroIndex chi,
      (1.7769 * Real.log ((q : Real) * T))⁻¹ ≤ |(completedZeroValue p).im - H| := by
    rcases Set.mem_insert_iff.mp hH with h | h
    · subst H
      exact fun p => (hsep p).1
    · have heq := Set.mem_singleton_iff.mp h
      subst H
      exact fun p => (hsep p).2
  exact ⟨fun _ hs hn => LFunction_ne_zero_near_separated_height hchi hPrimitive hsepH hs hn,
    fun _ hre _ hz _ hs => norm_inv_sub_le_near_separated_height hB
      (LFunction_zero_separated_of_index hchi hPrimitive hsepH hre hz) hs⟩

end LiuWang.Proof.LocalAnalyticBounds
