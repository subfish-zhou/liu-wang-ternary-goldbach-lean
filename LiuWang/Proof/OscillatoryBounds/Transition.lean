import LiuWang.Proof.OscillatoryBounds.FirstDerivative
import Mathlib.Topology.Order.Compact

/-!
# 过渡段的平方根界

小导数集合由 `|gamma + k*t| ≤ m*t` 定义。其两端满足的精确差商恒等式
给出长度 `≤ 2*m*N^2/|gamma|`；两侧消费已证明的一阶积分界。
所得常数 `10` 强于原文的 `16`，并且不需要限制频率。
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Interval
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.OscillatoryBounds

theorem small_phase_diameter {u v N gamma k m : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hvN : v ≤ N) (hm : 0 ≤ m)
    (hg : gamma ≠ 0)
    (hsu : |gamma + k * u| ≤ m * u) (hsv : |gamma + k * v| ≤ m * v) :
    v - u ≤ 2 * m * N ^ 2 / |gamma| := by
  have hv : 0 < v := hu.trans_le huv
  have hN : 0 < N := hv.trans_le hvN
  have huN := huv.trans hvN
  have hcalc : |gamma| * (v - u) ≤ 2 * m * N ^ 2 := by
    calc
      _ = |v * (gamma + k * u) - u * (gamma + k * v)| := by
        rw [show v * (gamma + k * u) - u * (gamma + k * v) =
          gamma * (v - u) by ring, abs_mul, abs_of_nonneg (sub_nonneg.mpr huv)]
      _ ≤ |v * (gamma + k * u)| + |u * (gamma + k * v)| := abs_sub _ _
      _ = v * |gamma + k * u| + u * |gamma + k * v| := by
        rw [abs_mul, abs_mul, abs_of_pos hv, abs_of_pos hu]
      _ ≤ v * (m * u) + u * (m * v) :=
        add_le_add (mul_le_mul_of_nonneg_left hsu hv.le)
          (mul_le_mul_of_nonneg_left hsv hu.le)
      _ = 2 * m * (u * v) := by ring
      _ ≤ 2 * m * (N * N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul huN hvN hv.le hN.le) (by positivity)
      _ = 2 * m * N ^ 2 := by ring
  exact (le_div_iff₀ (abs_pos.mpr hg)).mpr (by simpa only [mul_comm] using hcalc)

theorem norm_integral_cpow_charReal_first_derivative_open {a b η m : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {rho : ℂ} (hr : rho ≠ 0)
    (hbeta : rho.re ≤ 1) (hm : 0 < m)
    (hsep : ∀ t ∈ Set.Ioo a b, m * t ≤ |rho.im + 2 * Real.pi * η * t|) :
    ‖∫ t in a..b, (t : ℂ) ^ (rho - 1) * charReal (η * t)‖ ≤
      4 * a ^ (rho.re - 1) / m := by
  by_cases he : a = b
  · subst b
    simp only [intervalIntegral.integral_same, norm_zero]
    positivity
  · apply norm_integral_cpow_charReal_first_derivative ha hab hr hbeta hm
    intro t ht
    apply le_on_closure hsep (by fun_prop) (by fun_prop)
    rwa [closure_Ioo he]

theorem norm_integral_cpow_charReal_sqrt_general {a N : ℝ}
    (ha : 0 < a) (haN : a ≤ N) {rho : ℂ}
    (hbeta : rho.re ≤ 1) (hgamma : rho.im ≠ 0) (η : ℝ) :
    ‖∫ t in a..N, (t : ℂ) ^ (rho - 1) * charReal (η * t)‖ ≤
      10 * a ^ (rho.re - 1) * N / Real.sqrt |rho.im| := by
  let G : ℝ := |rho.im|
  let s : ℝ := Real.sqrt G
  let m : ℝ := s / N
  let A : ℝ := a ^ (rho.re - 1)
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ (rho - 1) * charReal (η * t)
  let S : Set ℝ := Set.Icc a N ∩ {t | |rho.im + 2 * Real.pi * η * t| ≤ m * t}
  have hN : 0 < N := ha.trans_le haN
  have hG : 0 < G := abs_pos.mpr hgamma
  have hs : 0 < s := Real.sqrt_pos.mpr hG
  have hs2 : s ^ 2 = G := Real.sq_sqrt hG.le
  have hm : 0 < m := div_pos hs hN
  have hmN : m * N = s := div_mul_cancel₀ s hN.ne'
  have hA : 0 < A := Real.rpow_pos_of_pos ha _
  have hr : rho ≠ 0 := fun h => hgamma (by simp [h])
  have hnonstat : ∀ u v : ℝ, a ≤ u → u ≤ v →
      (∀ t ∈ Set.Ioo u v, m * t ≤ |rho.im + 2 * Real.pi * η * t|) →
      ‖∫ t in u..v, f t‖ ≤ 4 * A / m := by
    intro u v hau huv hsep
    have h := norm_integral_cpow_charReal_first_derivative_open (ha.trans_le hau)
      huv hr hbeta hm hsep
    apply h.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ha hau (sub_nonpos.mpr hbeta)) (by norm_num)) hm.le
  have hbound : ‖∫ t in a..N, f t‖ ≤ 10 * A / m := by
    by_cases hSne : S.Nonempty
    · have hSc : IsCompact S :=
        isCompact_Icc.inter_right (isClosed_le (by fun_prop) (by fun_prop))
      obtain ⟨u, hu, humin⟩ := hSc.exists_isMinOn hSne continuousOn_id
      obtain ⟨v, hv, hvmax⟩ := hSc.exists_isMaxOn hSne continuousOn_id
      have huI : u ∈ Set.Icc a N := hu.1
      have hvI : v ∈ Set.Icc a N := hv.1
      have huv : u ≤ v := humin hv
      have hleft : ‖∫ t in a..u, f t‖ ≤ 4 * A / m := by
        apply hnonstat a u le_rfl huI.1
        intro t ht
        by_contra h
        have htS : t ∈ S := ⟨⟨ht.1.le, ht.2.le.trans huI.2⟩, (lt_of_not_ge h).le⟩
        have hmin : u ≤ t := humin htS
        linarith [ht.2]
      have hright : ‖∫ t in v..N, f t‖ ≤ 4 * A / m := by
        apply hnonstat v N hvI.1 hvI.2
        intro t ht
        by_contra h
        have htS : t ∈ S := ⟨⟨hvI.1.trans ht.1.le, ht.2.le⟩, (lt_of_not_ge h).le⟩
        have hmax : t ≤ v := hvmax htS
        linarith [ht.1]
      have hdiam : v - u ≤ 2 / m := by
        have h := small_phase_diameter (ha.trans_le huI.1) huv hvI.2 hm.le hgamma hu.2 hv.2
        have heq : 2 * m * N ^ 2 / G = 2 / m := by
          apply (div_eq_div_iff hG.ne' hm.ne').mpr
          calc
            2 * m * N ^ 2 * m = 2 * (m * N) ^ 2 := by ring
            _ = 2 * G := by rw [hmN, hs2]
        exact h.trans_eq heq
      have hmid : ‖∫ t in u..v, f t‖ ≤ 2 * A / m := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := u) (b := v) (C := A) (f := f) (fun t ht => by
            rw [Set.uIoc_of_le huv] at ht
            have hat : a ≤ t := huI.1.trans ht.1.le
            rw [norm_cpow_charReal (ha.trans_le hat)]
            exact Real.rpow_le_rpow_of_nonpos ha hat (sub_nonpos.mpr hbeta))
        rw [abs_of_nonneg (sub_nonneg.mpr huv)] at h
        apply h.trans
        calc
          A * (v - u) ≤ A * (2 / m) := mul_le_mul_of_nonneg_left hdiam hA.le
          _ = 2 * A / m := by ring
      have hi1 := intervalIntegrable_cpow_charReal ha huI.1 rho η
      have hi2 := intervalIntegrable_cpow_charReal (ha.trans_le huI.1) huv rho η
      have hi3 := intervalIntegrable_cpow_charReal (ha.trans_le hvI.1) hvI.2 rho η
      have hi23 := intervalIntegrable_cpow_charReal (ha.trans_le huI.1) huI.2 rho η
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi23,
        ← intervalIntegral.integral_add_adjacent_intervals hi2 hi3]
      calc
        _ ≤ ‖∫ t in a..u, f t‖ + ‖(∫ t in u..v, f t) + ∫ t in v..N, f t‖ :=
          norm_add_le _ _
        _ ≤ ‖∫ t in a..u, f t‖ + (‖∫ t in u..v, f t‖ + ‖∫ t in v..N, f t‖) :=
          add_le_add le_rfl (norm_add_le _ _)
        _ ≤ 4 * A / m + (2 * A / m + 4 * A / m) :=
          add_le_add hleft (add_le_add hmid hright)
        _ = 10 * A / m := by ring
    · have hsep : ∀ t ∈ Set.Ioo a N, m * t ≤ |rho.im + 2 * Real.pi * η * t| := by
        intro t ht
        by_contra h
        exact hSne ⟨t, ⟨⟨ht.1.le, ht.2.le⟩, (lt_of_not_ge h).le⟩⟩
      apply (hnonstat a N le_rfl haN hsep).trans
      exact div_le_div_of_nonneg_right (by nlinarith) hm.le
  apply hbound.trans_eq
  dsimp [m, s, A, G]
  field_simp

theorem norm_integral_cpow_charReal_sqrt {N : ℝ} (hN : 0 < N)
    {rho : ℂ} (hbeta : rho.re ≤ 1) (hgamma : rho.im ≠ 0) (η : ℝ) :
    ‖∫ t in N / 1000..N, (t : ℂ) ^ (rho - 1) * charReal (η * t)‖ ≤
      16 * (0.001 : ℝ) ^ (rho.re - 1) * N ^ rho.re / Real.sqrt |rho.im| := by
  have h := norm_integral_cpow_charReal_sqrt_general (by positivity : 0 < N / 1000)
    (by linarith : N / 1000 ≤ N) hbeta hgamma η
  have heq : (N / 1000) ^ (rho.re - 1) * N =
      (0.001 : ℝ) ^ (rho.re - 1) * N ^ rho.re := by
    rw [show N / 1000 = (0.001 : ℝ) * N by ring,
      Real.mul_rpow (by norm_num) hN.le, Real.rpow_sub_one hN.ne']
    field_simp
  apply h.trans
  rw [mul_assoc 10, heq]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hp : 0 < (0.001 : ℝ) ^ (rho.re - 1) * N ^ rho.re := by positivity
  nlinarith

end LiuWang.Proof.OscillatoryBounds
