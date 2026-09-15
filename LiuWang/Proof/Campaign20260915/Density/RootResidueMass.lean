import LiuWang.Proof.Campaign20260915.Density.BalancedGap
import LiuWang.Proof.Campaign20260915.Density.FamilyChen14
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.AuxiliaryDomain

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem sum_zmod_val (q : ℕ) [NeZero q] (f : ℕ → ℝ) :
    (∑ x : ZMod q, f x.val) = ∑ n ∈ range q, f n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
  calc
    _ = ∑ i : Fin k.succ, f i := by
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv k.succ).toEquiv
      intro i
      rfl
    _ = _ := Fin.sum_univ_eq_sum_range f k.succ

theorem residue_critical_mass_le {q N : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ (range N).erase 0) (x : ZMod q) :
    (∑ n ∈ fiber q S x, ‖criticalCoefficient n‖) ≤
      (Real.sqrt x.val)⁻¹ + 2 * Real.sqrt (N / q + 1 : ℕ) / Real.sqrt q := by
  let T := fiber q S x
  let A := T.filter (fun n => n < q)
  let B := T.filter (fun n => ¬ n < q)
  have hp (n : ℕ) (hn : n ∈ T) : 0 < n :=
    Nat.pos_of_ne_zero (mem_erase.mp (hS (mem_filter.mp hn).1)).1
  have hlo : (∑ n ∈ A, ‖criticalCoefficient n‖) ≤ (Real.sqrt x.val)⁻¹ := by
    have hs : A ⊆ {x.val} := by
      intro n hn
      have he := congrArg ZMod.val (mem_filter.mp (mem_filter.mp hn).1).2
      have hnq := (mem_filter.mp hn).2
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hnq] at he
      exact mem_singleton.mpr he
    calc
      _ ≤ ∑ n ∈ A, (Real.sqrt n)⁻¹ :=
        sum_le_sum (fun n hn => norm_criticalCoefficient_le (hp n (mem_filter.mp hn).1))
      _ ≤ ∑ n ∈ ({x.val} : Finset ℕ), (Real.sqrt n)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
      _ = _ := by simp
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hroot : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hpoint (n : ℕ) (hn : n ∈ B) :
      ‖criticalCoefficient n‖ ≤ (Real.sqrt q)⁻¹ * (Real.sqrt (n / q : ℕ))⁻¹ := by
    have hnq : q ≤ n := Nat.le_of_not_gt (mem_filter.mp hn).2
    have hk : 0 < n / q := Nat.div_pos hnq (NeZero.pos q)
    have hmul : (q : ℝ) * (n / q : ℕ) ≤ n := by exact_mod_cast Nat.mul_div_le n q
    have h := one_div_le_one_div_of_le
      (Real.sqrt_pos.mpr (mul_pos hq0 (Nat.cast_pos.mpr hk))) (Real.sqrt_le_sqrt hmul)
    rw [Real.sqrt_mul hq0.le] at h
    exact (norm_criticalCoefficient_le (hp n (mem_filter.mp hn).1)).trans
      (by simpa only [one_div, mul_inv_rev, mul_comm] using h)
  have hsub : B.image (fun n => n / q) ⊆ range (N / q + 1) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    have hnN := mem_range.mp (mem_erase.mp
      (hS (mem_filter.mp (mem_filter.mp hn).1).1)).2
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnN.le))
  have htail : (∑ n ∈ B, ‖criticalCoefficient n‖) ≤
      2 * Real.sqrt (N / q + 1 : ℕ) / Real.sqrt q := by
    have h := sum_le_sum hpoint
    rw [← mul_sum] at h
    have he : (∑ k ∈ B.image (fun n => n / q), (Real.sqrt k)⁻¹) =
        ∑ n ∈ B, (Real.sqrt (n / q : ℕ))⁻¹ := by
      rw [sum_image (show Set.InjOn (fun n : ℕ => n / q) B from
        (quotient_inj_on_fiber q S x).mono (filter_subset _ _))]
    rw [← he] at h
    have hs := sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => by positivity : ∀ k ∈ range (N / q + 1),
        k ∉ B.image (fun n => n / q) → 0 ≤ (Real.sqrt k)⁻¹)
    have hb := mul_le_mul_of_nonneg_left
      (hs.trans (GlobalZeroDensity.sum_inv_sqrt_le (N / q + 1))) (inv_nonneg.mpr hroot.le)
    exact h.trans (hb.trans_eq (by ring))
  have he := sum_filter_add_sum_filter_not T (fun n => n < q) (fun n => ‖criticalCoefficient n‖)
  change (∑ n ∈ A, _) + (∑ n ∈ B, _) = _ at he
  linarith

theorem residue_critical_mass_square {q N : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ (range N).erase 0) :
    (∑ x : ZMod q, (∑ n ∈ fiber q S x, ‖criticalCoefficient n‖) ^ 2) ≤
      harmonicRange q + 8 * Real.sqrt (N / q + 1 : ℕ) + 4 * (N / q + 1 : ℕ) := by
  let K : ℕ := N / q + 1
  let C : ℝ := 2 * Real.sqrt K / Real.sqrt q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hroot : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have h := sum_le_sum (s := (univ : Finset (ZMod q))) (fun x _ =>
    pow_le_pow_left₀ (sum_nonneg (fun _ _ => norm_nonneg _)) (residue_critical_mass_le hS x) 2)
  change _ ≤ ∑ x : ZMod q, ((Real.sqrt x.val)⁻¹ + C) ^ 2 at h
  have he : (∑ x : ZMod q, ((Real.sqrt x.val)⁻¹ + C) ^ 2) =
      harmonicRange q + 2 * C * (∑ n ∈ range q, (Real.sqrt n)⁻¹) + q * C ^ 2 := by
    simp_rw [add_sq]
    rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
    simp_rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [sum_zmod_val q (fun n => (n : ℝ)⁻¹), ← sum_mul, ← mul_sum,
      sum_zmod_val q (fun n => (Real.sqrt n)⁻¹)]
    simp only [card_univ, ZMod.card]
    unfold harmonicRange
    ring
  have hmass := mul_le_mul_of_nonneg_left (GlobalZeroDensity.sum_inv_sqrt_le q)
    (show 0 ≤ 2 * C by positivity)
  have hce : 2 * C * (2 * Real.sqrt q) = 8 * Real.sqrt K := by dsimp [C]; field_simp; ring
  have hcq : (q : ℝ) * C ^ 2 = 4 * K := by
    dsimp [C]
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg K), Real.sq_sqrt hq0.le]
    field_simp
    ring
  rw [he] at h
  rw [hce] at hmass
  rw [hcq] at h
  linarith

theorem source_residue_critical_mass_square (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (∑ x : ZMod q, (∑ n ∈ fiber q ((range ⌈(q : ℝ) * y⌉₊).erase 0) x,
      ‖criticalCoefficient n‖) ^ 2) ≤ 4.2 * y := by
  let N : ℕ := ⌈(q : ℝ) * y⌉₊
  let K : ℕ := N / q + 1
  have hy' : 10000 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hy0 : 0 ≤ y := by linarith
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by positivity
  have hN := (ceil_log_bounds (show 10000 ≤ (q : ℝ) * y by nlinarith)).1
  have hNq : (N : ℝ) / q ≤ 1.001 * y := by
    apply (div_le_iff₀ hq0).mpr
    dsimp [N]
    nlinarith only [hN]
  have hK : (K : ℝ) ≤ 1.01 * y := by
    have hd : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
    dsimp [K]
    push_cast
    linarith
  have hH : harmonicRange q ≤ 0.0002 * y := by
    have hlog := (max_le_iff.mp hy).2
    have h := inverse_range_le_log q
    unfold harmonicRange
    linarith
  have hs : 100 ≤ Real.sqrt y := by
    nlinarith [Real.sq_sqrt hy0, Real.sqrt_nonneg y]
  have hsqrt : Real.sqrt K ≤ 1.01 * Real.sqrt y := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hy0, Real.sq_sqrt (Nat.cast_nonneg K)]
    nlinarith
  have hsmall : 8 * Real.sqrt K ≤ 0.081 * y := by
    nlinarith [Real.sq_sqrt hy0]
  have h := residue_critical_mass_square
    (q := q) (N := N) (S := (range N).erase 0) (Subset.refl _)
  change _ ≤ harmonicRange q + 8 * Real.sqrt K + 4 * (K : ℝ) at h
  linarith

end LiuWang.Proof.Campaign20260915.Density
