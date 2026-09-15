import LiuWang.Proof.SourceRoute.Density.HorizontalArgument

/-! Jensen with the actual disk energy, retaining the source radii and exponential majorant. -/

set_option autoImplicit false

noncomputable section

open Complex Set Metric
open scoped ComplexConjugate
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.SourceRoute.Density

def diskEnergy {q : ℕ} [NeZero q] (chi : Character q) (X h R : ℝ) : ℝ :=
  sSup ((fun s : ℂ => ‖f chi X (s + h * I)‖ ^ 2) '' closedBall (2 : ℂ) R)

theorem le_diskEnergy {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X h R : ℝ) {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) R) :
    ‖f chi X (s + h * I)‖ ^ 2 ≤ diskEnergy chi X h R := by
  have hc : Continuous (fun s : ℂ => ‖f chi X (s + h * I)‖ ^ 2) :=
    (((differentiable_f hchi X).continuous.comp (continuous_id.add continuous_const)).norm).pow 2
  exact le_csSup ((isCompact_closedBall (2 : ℂ) R).bddAbove_image hc.continuousOn)
    (mem_image_of_mem _ hs)

theorem diskEnergy_nonneg {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X h : ℝ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ diskEnergy chi X h R :=
  (sq_nonneg _).trans (le_diskEnergy hchi X h R (mem_closedBall_self hR))

theorem norm_H_le_exp_square {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ) (s : ℂ) :
    ‖H chi X s‖ ≤ Real.exp (‖f chi X s‖ ^ 2) := by
  have hn := norm_sub_le (1 : ℂ) (f chi X s ^ 2)
  rw [norm_one, norm_pow] at hn
  exact hn.trans (by simpa only [add_comm] using Real.add_one_le_exp (‖f chi X s‖ ^ 2))

theorem reflected_disk_bound {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X h R : ℝ) {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) R) :
    ‖reflectedDetector chi X h s‖ ≤ 2 * Real.exp (diskEnergy chi X h R) := by
  have hcs : conj s ∈ closedBall (2 : ℂ) R := by
    rw [mem_closedBall_iff_norm]
    have he : conj s - 2 = conj (s - 2) := by rw [map_sub, map_ofNat]
    rw [he, norm_conj]
    exact mem_closedBall_iff_norm.mp hs
  have hp := (norm_H_le_exp_square chi X (s + h * I)).trans
    (Real.exp_le_exp.mpr (le_diskEnergy hchi X h R hs))
  have hm := (norm_H_le_exp_square chi X (conj s + h * I)).trans
    (Real.exp_le_exp.mpr (le_diskEnergy hchi X h R hcs))
  have hn := norm_add_le (H chi X (s + h * I)) (conj (H chi X (conj s + h * I)))
  rw [norm_conj] at hn
  exact hn.trans (by linarith)

theorem reflected_divisor_apply {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X h r : ℝ} (hX : 5 ≤ X)
    {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) r) :
    MeromorphicOn.divisor (reflectedDetector chi X h) (closedBall (2 : ℂ) r) s =
      (analyticOrderNatAt (reflectedDetector chi X h) s : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => (differentiable_reflectedDetector hchi X h).analyticAt z) hs,
    ← Nat.cast_analyticOrderNatAt (reflectedDetector_order_finite hchi hX h s)]
  simp

theorem reflected_card_le_divisor {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X : ℝ} (hX : 5 ≤ X) (h r : ℝ) :
    ((reflectedZeros chi X h r).card : ℝ) ≤
      ((∑ᶠ s, MeromorphicOn.divisor (reflectedDetector chi X h)
        (closedBall (2 : ℂ) r) s : ℤ) : ℝ) := by
  classical
  let D := MeromorphicOn.divisor (reflectedDetector chi X h) (closedBall (2 : ℂ) r)
  have hsum : (∑ᶠ s, D s) = ∑ s ∈ reflectedZeros chi X h r, D s :=
    finsum_eq_sum_of_support_subset _ (fun s hs =>
      (D.finiteSupport (isCompact_closedBall (2 : ℂ) r)).mem_toFinset.mpr hs)
  have hc : ((reflectedZeros chi X h r).card : ℤ) ≤ ∑ᶠ s, D s := by
    rw [hsum]
    calc
      ((reflectedZeros chi X h r).card : ℤ) =
          ∑ _s ∈ reflectedZeros chi X h r, (1 : ℤ) := by simp
      _ ≤ ∑ s ∈ reflectedZeros chi X h r, D s := by
        apply Finset.sum_le_sum
        intro s hs
        have hsm := (D.finiteSupport (isCompact_closedBall (2 : ℂ) r)).mem_toFinset.mp hs
        have he := reflected_divisor_apply hchi hX (h := h) (D.supportWithinDomain hsm)
        have hn : D s ≠ 0 := hsm
        change D s = _ at he
        rw [he] at hn ⊢
        have hp : (0 : ℤ) ≤ (analyticOrderNatAt (reflectedDetector chi X h) s : ℤ) :=
          Int.natCast_nonneg _
        omega
  exact_mod_cast hc

theorem reflected_jensen_energy {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X h r R : ℝ} (hX : 5 ≤ X) (hr : 0 < r) (hrR : r < R) :
    ((reflectedZeros chi X h r).card : ℝ) ≤
      (Real.log (2 / (2 - 8 / (X - 1) ^ 2)) + diskEnergy chi X h R) / Real.log (R / r) := by
  have hRp : 0 < R := hr.trans hrR
  have hA : AnalyticOnNhd ℂ (reflectedDetector chi X h) (closedBall (2 : ℂ) |R|) :=
    fun s _ => (differentiable_reflectedDetector hchi X h).analyticAt s
  have hM : 1 ≤ 2 * Real.exp (diskEnergy chi X h R) := by
    have hE := diskEnergy_nonneg hchi X h hRp.le
    have he := Real.add_one_le_exp (diskEnergy chi X h R)
    linarith
  have hJ := AnalyticOnNhd.sum_divisor_le (c := (2 : ℂ)) (f := reflectedDetector chi X h)
    (r := r) (R := R) (M := 2 * Real.exp (diskEnergy chi X h R))
    (by simpa only [abs_of_pos hr] using hr)
    (by simpa only [abs_of_pos hr, abs_of_pos hRp] using hrR)
    hM hA (reflectedDetector_two_ne_zero chi hX h)
    (fun s hs => reflected_disk_bound hchi X h R
      (sphere_subset_closedBall (by simpa only [abs_of_pos hRp] using hs)))
  rw [abs_of_pos hr] at hJ
  have hq : 8 / (X - 1) ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < X - 1))).mpr
    nlinarith
  have hfloor : 0 < 2 - 8 / (X - 1) ^ 2 := by linarith
  have hn := (reflectedDetector_two_lower chi (by linarith : 1 < X) h).trans
    (Complex.re_le_norm (reflectedDetector chi X h 2))
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  apply ((reflected_card_le_divisor hchi hX h r).trans hJ).trans
  apply div_le_div_of_nonneg_right _ hlog.le
  have he :
      Real.log (2 * Real.exp (diskEnergy chi X h R) / (2 - 8 / (X - 1) ^ 2)) =
        Real.log (2 / (2 - 8 / (X - 1) ^ 2)) + diskEnergy chi X h R := by
    rw [show 2 * Real.exp (diskEnergy chi X h R) / (2 - 8 / (X - 1) ^ 2) =
      (2 / (2 - 8 / (X - 1) ^ 2)) * Real.exp (diskEnergy chi X h R) by ring,
      Real.log_mul (ne_of_gt (div_pos (by norm_num) hfloor)) (Real.exp_ne_zero _),
      Real.log_exp]
  rw [← he]
  exact Real.log_le_log (div_pos (by positivity) (hfloor.trans_le hn))
    (div_le_div_of_nonneg_left (by positivity) hfloor hn)

theorem source_radii_log_lower {xi d : ℝ} (hd : 0 < d)
    (hxi : 1 / 2 + 2 * d ≤ xi) (hxi1 : xi < 1) :
    d / 3 ≤ Real.log ((2 - xi + 3 * d / 2) / (2 - xi + d)) := by
  have hr : 0 < 2 - xi + d := by linarith
  have hR : 0 < 2 - xi + 3 * d / 2 := by linarith
  have hRupper : 2 - xi + 3 * d / 2 ≤ 3 / 2 := by linarith
  have he : 1 - ((2 - xi + 3 * d / 2) / (2 - xi + d))⁻¹ =
      (d / 2) / (2 - xi + 3 * d / 2) := by
    rw [inv_div]
    calc
      _ = ((2 - xi + 3 * d / 2) - (2 - xi + d)) / (2 - xi + 3 * d / 2) := by
        rw [sub_div, div_self hR.ne']
      _ = _ := by congr 1; ring
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hR hr)
  rw [he] at hl
  apply le_trans _ hl
  apply (le_div_iff₀ hR).mpr
  nlinarith

theorem source_radii_reflected_count {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X h xi d : ℝ} (hX : 5 ≤ X) (hd : 0 < d)
    (hxi : 1 / 2 + 2 * d ≤ xi) (hxi1 : xi < 1) :
    ((reflectedZeros chi X h (2 - xi + d)).card : ℝ) ≤
      3 / d * (Real.log (2 / (2 - 8 / (X - 1) ^ 2)) +
        diskEnergy chi X h (2 - xi + 3 * d / 2)) := by
  have hr : 0 < 2 - xi + d := by linarith
  have hrR : 2 - xi + d < 2 - xi + 3 * d / 2 := by linarith
  have hlog := source_radii_log_lower hd hxi hxi1
  have hN : 0 ≤ Real.log (2 / (2 - 8 / (X - 1) ^ 2)) +
      diskEnergy chi X h (2 - xi + 3 * d / 2) := by
    have hj := reflected_jensen_energy hchi hX hr hrR (h := h)
    have hp : 0 < Real.log ((2 - xi + 3 * d / 2) / (2 - xi + d)) :=
      lt_of_lt_of_le (by positivity) hlog
    have hn := (Nat.cast_nonneg (α := ℝ) (reflectedZeros chi X h (2 - xi + d)).card).trans hj
    simpa only [zero_mul] using (le_div_iff₀ hp).mp hn
  apply (reflected_jensen_energy hchi hX hr hrR (h := h)).trans
  exact (div_le_div_of_nonneg_left hN (by positivity : 0 < d / 3) hlog).trans_eq (by field_simp)

end LiuWang.Proof.SourceRoute.Density
