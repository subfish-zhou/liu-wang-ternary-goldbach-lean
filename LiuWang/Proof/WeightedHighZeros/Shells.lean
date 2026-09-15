import LiuWang.Proof.WeightedHighZeros.Main

/-!
# A finite, endpoint-safe geometric mother bound

Closed adjacent bands may count their shared endpoint twice. The initial
band is not empty: this retains zeros exactly at the original lower cutoff.
There is no infinite-tail assertion here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedHighZeros

theorem bandSum_mono_height (N q : ℕ) [NeZero q] (u : ℝ)
    {y z : ℝ} (hyz : y ≤ z) :
    bandSum N q u y ≤ bandSum N q u z := by
  apply Finset.sum_le_sum
  intro chi _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hrho
    obtain ⟨hz, ⟨h0, h1, ht⟩, ha, hu⟩ := mem_bandValues.mp hrho
    exact mem_bandValues.mpr ⟨hz, ⟨h0, h1, ht.trans hyz⟩, ha, hu⟩
  · intro rho _ _
    positivity

theorem bandSum_split_le (N q : ℕ) [NeZero q] (u v y : ℝ) :
    bandSum N q u y ≤ bandSum N q u v + bandSum N q v y := by
  unfold bandSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro chi _
  rw [← Finset.sum_filter_add_sum_filter_not
    (bandValues chi (1 / 2) u y) (fun rho => |rho.im| ≤ v)]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro rho hrho
      obtain ⟨hrho, hv⟩ := Finset.mem_filter.mp hrho
      obtain ⟨hz, ⟨h0, h1, _⟩, ha, hu⟩ := mem_bandValues.mp hrho
      exact mem_bandValues.mpr ⟨hz, ⟨h0, h1, hv⟩, ha, hu⟩
    · intro rho _ _
      positivity
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro rho hrho
      obtain ⟨hrho, hv⟩ := Finset.mem_filter.mp hrho
      obtain ⟨hz, ⟨h0, h1, ht⟩, ha, _⟩ := mem_bandValues.mp hrho
      exact mem_bandValues.mpr ⟨hz, ⟨h0, h1, ht⟩, ha, (lt_of_not_ge hv).le⟩
    · intro rho _ _
      positivity

def geometricBound (N q : ℕ) (u r : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), shellBound N q (r ^ j * u) (r ^ (j + 1) * u)

theorem bandSum_le_geometricBound {N q : ℕ} [NeZero q] (hN : 1 ≤ N)
    {u r : ℝ} (hu : 1 ≤ u) (hr : 1 ≤ r) (k : ℕ) :
    bandSum N q u (r ^ (k + 1) * u) ≤ geometricBound N q u r k := by
  have hu0 : 0 < u := by linarith
  have hr0 : 0 < r := by linarith
  induction k with
  | zero =>
    simpa [geometricBound] using bandSum_le_shellBound hN hu (mul_pos hr0 hu0)
  | succ k ih =>
    have hlo : 1 ≤ r ^ (k + 1) * u :=
      hu.trans (le_mul_of_one_le_left hu0.le (one_le_pow₀ hr))
    have hh := bandSum_le_shellBound (q := q) hN hlo
      (mul_pos (pow_pos hr0 (k + 1 + 1)) hu0)
    have hs := (bandSum_split_le N q u (r ^ (k + 1) * u)
      (r ^ (k + 1 + 1) * u)).trans (add_le_add ih hh)
    simpa only [geometricBound, Finset.sum_range_succ] using hs

def coverIndex (u y r : ℝ) : ℕ :=
  ⌈Real.log (y / u) / Real.log r⌉₊

theorem height_le_cover {u y r : ℝ} (hu : 0 < u) (hy : 0 < y) (hr : 1 < r) :
    y ≤ r ^ (coverIndex u y r + 1) * u := by
  have hr0 : 0 < r := by linarith
  have hlr : 0 < Real.log r := Real.log_pos hr
  have hceil := Nat.le_ceil (Real.log (y / u) / Real.log r)
  have hlog : Real.log (y / u) ≤ (coverIndex u y r : ℝ) * Real.log r :=
    (div_le_iff₀ hlr).mp hceil
  have hle : y / u ≤ r ^ coverIndex u y r := by
    apply (Real.log_le_log_iff (div_pos hy hu) (pow_pos hr0 _)).mp
    simpa only [Real.log_pow] using hlog
  have hpow : r ^ coverIndex u y r ≤ r ^ (coverIndex u y r + 1) :=
    pow_le_pow_right₀ hr.le (Nat.le_succ _)
  exact (div_le_iff₀ hu).mp (hle.trans hpow)

def motherBound (N q : ℕ) (r : ℝ) : ℝ :=
  min (shellBound N q (omegaCutoff N q) (sourceT N))
    (geometricBound N q (omegaCutoff N q) r
      (coverIndex (omegaCutoff N q) (sourceT N) r))

theorem highSum_le_motherBound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {r : ℝ} (hr : 1 < r) : highSum N q ≤ motherBound N q r := by
  have hu : 1 ≤ omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have hy := Parameters.sourceT_pos (Parameters.exp_2000_le_of_exp_3100_le hN)
  refine le_min (highSum_le_single_shell hN hq) ?_
  exact (bandSum_mono_height N q (omegaCutoff N q)
    (height_le_cover (by linarith) hy hr)).trans
      (bandSum_le_geometricBound (Parameters.nat_pos_of_exp_le hN) hu hr.le _)

end LiuWang.Proof.WeightedHighZeros
