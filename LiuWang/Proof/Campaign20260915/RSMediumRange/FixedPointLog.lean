import LiuWang.Proof.Campaign20260915.RSMediumRange.ScalarTransport

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

def fixedScale : ℕ := 100000000000000

def divUp (n d : ℕ) : ℕ := n / d + if n % d = 0 then 0 else 1

structure FixedBracket where
  lo : ℕ
  hi : ℕ

namespace FixedBracket

def ratio (n d : ℕ) : FixedBracket :=
  ⟨n * fixedScale / d, divUp (n * fixedScale) d⟩

def mul (a b : FixedBracket) : FixedBracket :=
  ⟨a.lo * b.lo / fixedScale, divUp (a.hi * b.hi) fixedScale⟩

def divNat (a : FixedBracket) (d : ℕ) : FixedBracket :=
  ⟨a.lo / d, divUp a.hi d⟩

def oddPower (a : FixedBracket) : ℕ → FixedBracket
  | 0 => a
  | j + 1 => (oddPower a j).mul (a.mul a)

def series (a : FixedBracket) : FixedBracket :=
  ⟨∑ j ∈ Finset.range 10, ((a.oddPower j).divNat (2 * j + 1)).lo,
   ∑ j ∈ Finset.range 10, ((a.oddPower j).divNat (2 * j + 1)).hi⟩

def log (n k : ℕ) : FixedBracket :=
  let b := (ratio (n - 2 ^ k) (n + 2 ^ k)).series
  ⟨k * 6931471803 * 10000 + 2 * b.lo,
   k * 6931471808 * 10000 + 2 * b.hi + 100000⟩

noncomputable section

def Contains (a : FixedBracket) (x : ℝ) : Prop :=
  (a.lo : ℝ) / fixedScale ≤ x ∧ x ≤ (a.hi : ℝ) / fixedScale

private theorem division_bounds (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d ∧ (n : ℝ) / d ≤ divUp n d := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have hb : n ≤ divUp n d * d := by
    have hm := Nat.mod_add_div n d
    have hr := Nat.mod_lt n hd
    unfold divUp
    split_ifs with h <;> simp only [Nat.add_mul, Nat.zero_mul, Nat.one_mul] <;> nlinarith
  exact (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr (by exact_mod_cast hb)

theorem ratio_contains (n d : ℕ) (hd : 0 < d) :
    (ratio n d).Contains ((n : ℝ) / d) := by
  have h := division_bounds (n * fixedScale) d hd
  have hlo := div_le_div_of_nonneg_right h.1 (by norm_num [fixedScale] : (0 : ℝ) ≤ fixedScale)
  have hhi := div_le_div_of_nonneg_right h.2 (by norm_num [fixedScale] : (0 : ℝ) ≤ fixedScale)
  have he : ((n * fixedScale : ℕ) : ℝ) / d / fixedScale = (n : ℝ) / d := by
    push_cast
    norm_num [fixedScale]
    ring
  rw [he] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem mul_contains {a b : FixedBracket} {x y : ℝ}
    (ha : a.Contains x) (hb : b.Contains y) :
    (a.mul b).Contains (x * y) := by
  have hx : 0 ≤ x := (by positivity : (0 : ℝ) ≤ (a.lo : ℝ) / fixedScale).trans ha.1
  have hy : 0 ≤ y := (by positivity : (0 : ℝ) ≤ (b.lo : ℝ) / fixedScale).trans hb.1
  have hlo := (division_bounds (a.lo * b.lo) fixedScale (by norm_num [fixedScale])).1
  have hhi := (division_bounds (a.hi * b.hi) fixedScale (by norm_num [fixedScale])).2
  have hl := div_le_div_of_nonneg_right hlo (by norm_num [fixedScale] : (0 : ℝ) ≤ fixedScale)
  have hu := div_le_div_of_nonneg_right hhi (by norm_num [fixedScale] : (0 : ℝ) ≤ fixedScale)
  constructor
  · apply le_trans _ (mul_le_mul ha.1 hb.1 (by positivity) hx)
    convert hl using 1 <;> simp [mul, fixedScale]
    ring
  · apply le_trans (mul_le_mul ha.2 hb.2 hy (by positivity)) _
    convert hu using 1 <;> simp [mul, fixedScale]
    ring

theorem divNat_contains {a : FixedBracket} {x : ℝ}
    (ha : a.Contains x) {d : ℕ} (hd : 0 < d) :
    (a.divNat d).Contains (x / d) := by
  have hdR : (0 : ℝ) ≤ d := by positivity
  have hlo := (division_bounds a.lo d hd).1
  have hhi := (division_bounds a.hi d hd).2
  have hl := div_le_div_of_nonneg_right hlo (by norm_num [fixedScale] : (0 : ℝ) ≤ fixedScale)
  have hu := div_le_div_of_nonneg_right hhi (by norm_num [fixedScale] : (0 : ℝ) ≤ fixedScale)
  constructor
  · apply le_trans _ (div_le_div_of_nonneg_right ha.1 hdR)
    convert hl using 1 <;> simp [divNat, fixedScale]
    ring
  · apply le_trans (div_le_div_of_nonneg_right ha.2 hdR) _
    convert hu using 1 <;> simp [divNat, fixedScale]
    ring

theorem oddPower_contains {a : FixedBracket} {z : ℝ}
    (ha : a.Contains z) (j : ℕ) :
    (a.oddPower j).Contains (z ^ (2 * j + 1)) := by
  induction j with
  | zero => simpa [oddPower] using ha
  | succ j ih =>
    have h := mul_contains ih (mul_contains ha ha)
    have he : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
    simpa [oddPower, he, pow_add, pow_two] using h

theorem series_contains {a : FixedBracket} {z : ℝ}
    (ha : a.Contains z) :
    a.series.Contains (∑ j ∈ Finset.range 10, z ^ (2 * j + 1) / (2 * j + 1)) := by
  have h (j : ℕ) := divNat_contains (oddPower_contains ha j)
    (show 0 < 2 * j + 1 by omega)
  constructor
  · have hs := Finset.sum_le_sum (s := Finset.range 10) (fun j _ => (h j).1)
    simpa [Contains, series, Nat.cast_sum, Finset.sum_div] using hs
  · have hs := Finset.sum_le_sum (s := Finset.range 10) (fun j _ => (h j).2)
    simpa [Contains, series, Nat.cast_sum, Finset.sum_div] using hs

theorem log_contains {n k : ℕ} (hlo : 2 ^ k ≤ n) (hhi : n < 2 ^ (k + 1)) :
    (log n k).Contains (Real.log n) := by
  unfold log
  generalize hb : (ratio (n - 2 ^ k) (n + 2 ^ k)).series = b
  let q : ℝ := (2 : ℝ) ^ k
  let z : ℝ := ((n : ℝ) - q) / ((n : ℝ) + q)
  have hq : 0 < q := by dsimp [q]; positivity
  have hnl : q ≤ (n : ℝ) := by
    dsimp [q]
    exact_mod_cast hlo
  have hnu : (n : ℝ) < 2 * q := by
    have h : (n : ℝ) < (2 : ℝ) ^ (k + 1) := by exact_mod_cast hhi
    simpa [q, pow_succ, mul_comm] using h
  have hn : (0 : ℝ) < n := hq.trans_le hnl
  have hz : 0 ≤ z ∧ z ≤ 1 / 3 := by
    constructor
    · exact div_nonneg (by linarith) (by linarith)
    · apply (div_le_iff₀ (by linarith : 0 < (n : ℝ) + q)).mpr
      linarith
  have hr : (ratio (n - 2 ^ k) (n + 2 ^ k)).Contains z := by
    have h := ratio_contains (n - 2 ^ k) (n + 2 ^ k) (by positivity)
    simpa [z, q, Nat.cast_sub hlo, Nat.cast_add, Nat.cast_pow] using h
  have hs := series_contains hr
  rw [hb] at hs
  have heq : (1 + z) / (1 - z) = (n : ℝ) / q := by
    dsimp [z]
    field_simp [hq.ne']
    ring
  have hlog : Real.log ((1 + z) / (1 - z)) =
      Real.log n - k * Real.log 2 := by
    rw [heq, Real.log_div hn.ne' hq.ne']
    simp [q, Real.log_pow]
  have hl := Real.sum_range_le_log_div hz.1 (by linarith : z < 1) 10
  have hu := Real.log_div_le_sum_range_add hz.1 (by linarith : z < 1) 10
  rw [hlog] at hl hu
  have hrem : 2 * (z ^ (2 * 10 + 1) / (1 - z ^ 2)) ≤ (1 / 1000000000 : ℝ) := by
    have h2 := pow_le_pow_left₀ hz.1 hz.2 2
    have h21 := pow_le_pow_left₀ hz.1 hz.2 21
    have hd : (8 / 9 : ℝ) ≤ 1 - z ^ 2 := by norm_num at h2; linarith
    have h := div_le_div₀ (by positivity : (0 : ℝ) ≤ (1 / 3) ^ 21) h21
      (by norm_num : (0 : ℝ) < 8 / 9) hd
    norm_num at h
    norm_num
    linarith
  have hkl := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg k)
  have hku := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg k)
  dsimp only [Contains] at hs ⊢
  push_cast
  norm_num [fixedScale] at hs ⊢
  constructor <;> linarith [hs.1, hs.2]

end
end FixedBracket

#print axioms FixedBracket.log_contains

end LiuWang.Proof.Campaign20260915.RSMediumRange
