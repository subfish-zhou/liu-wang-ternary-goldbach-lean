import LiuWang.Proof.Interfaces.Main

/-!
# Logarithmic parameters on the Liu--Wang source domains

The definitions are consumed unchanged from `Proof.Interfaces.Main`.
The estimates below hold throughout the indicated domains, including the
endpoints. The exponential comparison uses its quadratic lower bound, not
numerical evaluation at the endpoint.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.Parameters

open LiuWang.Proof.Interfaces

theorem natCast_pos_of_exp_le {N : Nat} {b : Real}
    (hN : Real.exp b ≤ (N : Real)) : 0 < (N : Real) :=
  (Real.exp_pos b).trans_le hN

theorem nat_pos_of_exp_le {N : Nat} {b : Real}
    (hN : Real.exp b ≤ (N : Real)) : 0 < N := by
  exact_mod_cast natCast_pos_of_exp_le hN

theorem le_sourceL_of_exp_le {N : Nat} {b : Real}
    (hN : Real.exp b ≤ (N : Real)) : b ≤ sourceL N :=
  (Real.le_log_iff_exp_le (natCast_pos_of_exp_le hN)).2 hN

theorem sourceL_ge_2000 {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    2000 ≤ sourceL N :=
  le_sourceL_of_exp_le hN

theorem sourceL_ge_3100 {N : Nat} (hN : Real.exp 3100 ≤ (N : Real)) :
    3100 ≤ sourceL N :=
  le_sourceL_of_exp_le hN

theorem exp_2000_le_of_exp_3100_le {N : Nat}
    (hN : Real.exp 3100 ≤ (N : Real)) : Real.exp 2000 ≤ (N : Real) :=
  (Real.exp_le_exp.mpr (by norm_num)).trans hN

theorem exp_sourceL {N : Nat} (hN : 0 < N) :
    Real.exp (sourceL N) = (N : Real) :=
  Real.exp_log (by exact_mod_cast hN)

theorem sourceL_pos {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    0 < sourceL N :=
  lt_of_lt_of_le (by norm_num) (sourceL_ge_2000 hN)

theorem one_le_sourceL {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    1 ≤ sourceL N :=
  le_trans (by norm_num) (sourceL_ge_2000 hN)

/-- A uniform comparison obtained by taking the sixteenth power of the
quadratic lower bound for `exp (x / 16)`. -/
theorem pow_sixteen_lt_exp {x : Real} (hx : 2000 ≤ x) :
    x ^ (16 : Nat) < Real.exp x := by
  have hx0 : 0 ≤ x := by linarith
  have hquad := Real.quadratic_le_exp_of_nonneg (x := x / 16) (by positivity)
  have hsmall : x < Real.exp (x / 16) := by
    nlinarith [mul_nonneg hx0 (show 0 ≤ x - 2000 by linarith)]
  have hp := pow_lt_pow_left₀ hsmall hx0 (n := 16) (by norm_num)
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat] at hp
  rwa [show (16 : Real) * (x / 16) = x by ring] at hp

/-- The coefficient and power can vary over the entire stated ranges. -/
theorem mul_pow_lt_exp {x c : Real} {k : Nat} (hx : 2000 ≤ x)
    (hc : c ≤ 1000) (hk : k ≤ 15) : c * x ^ k < Real.exp x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  calc
    c * x ^ k ≤ 1000 * x ^ k := mul_le_mul_of_nonneg_right hc (pow_nonneg hx0 _)
    _ ≤ 1000 * x ^ 15 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 hk) (by norm_num)
    _ < x * x ^ 15 :=
      mul_lt_mul_of_pos_right (by linarith) (pow_pos (by linarith : 0 < x) _)
    _ = x ^ 16 := by ring
    _ < Real.exp x := pow_sixteen_lt_exp hx

theorem mul_sourceL_pow_lt {N k : Nat} {c : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hc : c ≤ 1000) (hk : k ≤ 15) :
    c * sourceL N ^ k < (N : Real) := by
  simpa only [exp_sourceL (nat_pos_of_exp_le hN)] using
    mul_pow_lt_exp (sourceL_ge_2000 hN) hc hk

theorem nat_mul_log_lt {x : Real} {k : Nat} (hx : 2000 ≤ x) (hk : k ≤ 16) :
    (k : Real) * Real.log x < x := by
  have hx0 : 0 < x := by linarith
  calc
    (k : Real) * Real.log x = Real.log (x ^ k) := (Real.log_pow x k).symm
    _ < Real.log (Real.exp x) :=
      Real.log_lt_log (pow_pos hx0 _)
        ((pow_le_pow_right₀ (by linarith : 1 ≤ x) hk).trans_lt (pow_sixteen_lt_exp hx))
    _ = x := Real.log_exp x

theorem sourceQ_eq_div (N : Nat) :
    sourceQ N = (N : Real) / sourceL N ^ (7 : Nat) := by
  simp [sourceQ, zpow_neg, div_eq_mul_inv]

theorem sourceP_pos {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    0 < sourceP N :=
  pow_pos (sourceL_pos hN) _

theorem sourceP1_pos {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    0 < sourceP1 N :=
  pow_pos (sourceL_pos hN) _

theorem sourceQ_pos {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    0 < sourceQ N := by
  rw [sourceQ_eq_div]
  exact div_pos (natCast_pos_of_exp_le hN) (pow_pos (sourceL_pos hN) _)

theorem sourceT_pos {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    0 < sourceT N :=
  pow_pos (sourceL_pos hN) _

theorem one_le_sourceP {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    1 ≤ sourceP N :=
  one_le_pow₀ (one_le_sourceL hN)

theorem sourceP_le_sourceP1 {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    sourceP N ≤ sourceP1 N :=
  pow_le_pow_right₀ (one_le_sourceL hN) (by norm_num)

theorem sourceP1_le_sourceT {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    sourceP1 N ≤ sourceT N :=
  pow_le_pow_right₀ (one_le_sourceL hN) (by norm_num)

theorem sourceT_lt_windowLower {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    sourceT N < sourceWindowLower N := by
  apply (lt_div_iff₀ (by norm_num : (0 : Real) < 1000)).2
  simpa [sourceT, mul_comm] using
    mul_sourceL_pow_lt (k := 15) (c := 1000) hN (by norm_num) (by norm_num)

theorem sourceT_lt_real_endpoint {N : Nat} {t : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (ht : sourceWindowLower N ≤ t) :
    sourceT N < t :=
  (sourceT_lt_windowLower hN).trans_le ht

theorem sourceT_lt_natCast {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    sourceT N < (N : Real) := by
  simpa [sourceT] using
    mul_sourceL_pow_lt (k := 15) (c := 1) hN (by norm_num) (by norm_num)

theorem sourceP1_lt_sourceQ_half {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    sourceP1 N < sourceQ N / 2 := by
  rw [sourceQ_eq_div, div_div]
  apply (lt_div_iff₀ (mul_pos (pow_pos (sourceL_pos hN) _) (by norm_num))).2
  calc
    sourceP1 N * (sourceL N ^ 7 * 2) = 2 * sourceL N ^ 13 := by
      unfold sourceP1
      ring
    _ < (N : Real) :=
      mul_sourceL_pow_lt (k := 13) (c := 2) hN (by norm_num) (by norm_num)

theorem sourceP1_lt_sourceQ_half_3100 {N : Nat}
    (hN : Real.exp 3100 ≤ (N : Real)) : sourceP1 N < sourceQ N / 2 :=
  sourceP1_lt_sourceQ_half (exp_2000_le_of_exp_3100_le hN)

theorem two_lt_sourceQ {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    2 < sourceQ N := by
  have hp := (one_le_sourceP hN).trans (sourceP_le_sourceP1 hN)
  have hq := sourceP1_lt_sourceQ_half hN
  linarith

theorem sourceQ_lt_natCast {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    sourceQ N < (N : Real) := by
  rw [sourceQ_eq_div]
  apply div_lt_self (natCast_pos_of_exp_le hN)
  exact one_lt_pow₀ (lt_of_lt_of_le (by norm_num) (sourceL_ge_2000 hN)) (by norm_num)

theorem approximationRadius_eq {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 0 < q) :
    1 / ((q : Real) * sourceQ N) =
      sourceL N ^ (7 : Nat) / ((q : Real) * (N : Real)) := by
  have hNr := (natCast_pos_of_exp_le hN).ne'
  have hqr : (q : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hL := (sourceL_pos hN).ne'
  rw [sourceQ_eq_div]
  field_simp

theorem omegaCutoff_pos {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 0 < q) :
    0 < omegaCutoff N q := by
  unfold omegaCutoff
  exact div_pos (mul_pos (by norm_num) (sourceP_pos hN)) (by exact_mod_cast hq)

theorem omegaCutoff_ge {N q : Nat}
    (hq : 0 < q) (hqP : (q : Real) ≤ sourceP N) :
    3.36 ≤ omegaCutoff N q := by
  apply (le_div_iff₀ (by exact_mod_cast hq : (0 : Real) < q)).2
  exact mul_le_mul_of_nonneg_left hqP (by norm_num)

theorem deltaRadius_pos {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 0 < q) :
    0 < deltaRadius N q := by
  unfold deltaRadius
  exact div_pos (mul_pos (by norm_num) (sourceP_pos hN))
    (mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (by exact_mod_cast hq)) (natCast_pos_of_exp_le hN))

theorem deltaRadius_eq_omega {N q : Nat} :
    deltaRadius N q = omegaCutoff N q / (10 * Real.pi * (N : Real)) := by
  unfold deltaRadius omegaCutoff
  rw [div_div]
  congr 1
  ring

theorem deltaRadius_le_approximationRadius {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hq : 0 < q) :
    deltaRadius N q ≤ 1 / ((q : Real) * sourceQ N) := by
  rw [approximationRadius_eq hN hq]
  have hqN : 0 < (q : Real) * (N : Real) :=
    mul_pos (by exact_mod_cast hq) (natCast_pos_of_exp_le hN)
  have hpi : 0 < 10 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hP7 : sourceP N ≤ sourceL N ^ (7 : Nat) :=
    pow_le_pow_right₀ (one_le_sourceL hN) (by norm_num)
  have hscale : 3.36 * sourceP N / (10 * Real.pi) ≤ sourceP N := by
    apply (div_le_iff₀ hpi).2
    have hconst : (3.36 : Real) ≤ 10 * Real.pi := by linarith [Real.two_le_pi]
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hconst (sourceP_pos hN).le
  calc
    deltaRadius N q = (3.36 * sourceP N / (10 * Real.pi)) /
        ((q : Real) * (N : Real)) := by
      unfold deltaRadius
      rw [div_div]
      congr 1
      ring
    _ ≤ sourceL N ^ (7 : Nat) / ((q : Real) * (N : Real)) :=
      div_le_div_of_nonneg_right (hscale.trans hP7) hqN.le

theorem deltaRadius_le_approximationRadius_3100 {N q : Nat}
    (hN : Real.exp 3100 ≤ (N : Real)) (hq : 0 < q) :
    deltaRadius N q ≤ 1 / ((q : Real) * sourceQ N) :=
  deltaRadius_le_approximationRadius (exp_2000_le_of_exp_3100_le hN) hq

theorem sourceWindowLower_le_natCast_iff (N n : Nat) :
    sourceWindowLower N ≤ (n : Real) ↔ N ≤ 1000 * n := by
  unfold sourceWindowLower
  rw [div_le_iff₀ (by norm_num : (0 : Real) < 1000)]
  norm_cast
  rw [Nat.mul_comm]

theorem mem_windowSet_iff_real (N n : Nat) :
    n ∈ windowSet N ↔ sourceWindowLower N ≤ (n : Real) ∧ (n : Real) ≤ N := by
  rw [mem_windowSet_iff, sourceWindowLower_le_natCast_iff]
  norm_cast
  exact and_comm

theorem sourceT_lt_window_member {N n : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hn : n ∈ windowSet N) :
    sourceT N < (n : Real) :=
  sourceT_lt_real_endpoint hN ((mem_windowSet_iff_real N n).1 hn).1

theorem nat_le_floor_sourceQ_iff {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    q ≤ ⌊sourceQ N⌋₊ ↔ (q : Real) ≤ sourceQ N :=
  Nat.le_floor_iff (sourceQ_pos hN).le

theorem floor_sourceQ_le_natCast {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    (⌊sourceQ N⌋₊ : Real) ≤ sourceQ N :=
  Nat.floor_le (sourceQ_pos hN).le

theorem sourceP1_lt_floor_sourceQ {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    sourceP1 N < (⌊sourceQ N⌋₊ : Real) := by
  have hp := (one_le_sourceP hN).trans (sourceP_le_sourceP1 hN)
  have hq := sourceP1_lt_sourceQ_half hN
  have hf := Nat.lt_floor_add_one (sourceQ N)
  linarith

theorem two_le_floor_sourceQ {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) : 2 ≤ ⌊sourceQ N⌋₊ :=
  (nat_le_floor_sourceQ_iff hN).2 (by simpa using (two_lt_sourceQ hN).le)

theorem nat_le_floor_sourceP_iff {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    q ≤ ⌊sourceP N⌋₊ ↔ (q : Real) ≤ sourceP N :=
  Nat.le_floor_iff (sourceP_pos hN).le

theorem nat_le_floor_sourceP1_iff {N q : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    q ≤ ⌊sourceP1 N⌋₊ ↔ (q : Real) ≤ sourceP1 N :=
  Nat.le_floor_iff (sourceP1_pos hN).le

theorem nat_le_floor_sourceT_iff {N t : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    t ≤ ⌊sourceT N⌋₊ ↔ (t : Real) ≤ sourceT N :=
  Nat.le_floor_iff (sourceT_pos hN).le

theorem ceil_windowLower_le_iff (N n : Nat) :
    ⌈sourceWindowLower N⌉₊ ≤ n ↔ N ≤ 1000 * n := by
  rw [Nat.ceil_le, sourceWindowLower_le_natCast_iff]

theorem parameters_2000 {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    2000 ≤ sourceL N ∧
    1 ≤ sourceP N ∧ sourceP N ≤ sourceP1 N ∧ sourceP1 N ≤ sourceT N ∧
    sourceT N < sourceWindowLower N ∧
    sourceP1 N < sourceQ N / 2 ∧ 2 < sourceQ N ∧ sourceQ N < (N : Real) :=
  ⟨sourceL_ge_2000 hN, one_le_sourceP hN, sourceP_le_sourceP1 hN,
    sourceP1_le_sourceT hN, sourceT_lt_windowLower hN, sourceP1_lt_sourceQ_half hN,
    two_lt_sourceQ hN, sourceQ_lt_natCast hN⟩

theorem parameters_3100 {N : Nat} (hN : Real.exp 3100 ≤ (N : Real)) :
    3100 ≤ sourceL N ∧
    1 ≤ sourceP N ∧ sourceP N ≤ sourceP1 N ∧ sourceP1 N ≤ sourceT N ∧
    sourceT N < sourceWindowLower N ∧
    sourceP1 N < sourceQ N / 2 ∧ 2 < sourceQ N ∧ sourceQ N < (N : Real) :=
  ⟨sourceL_ge_3100 hN, (parameters_2000 (exp_2000_le_of_exp_3100_le hN)).2⟩

theorem log_sourceP (N : Nat) :
    Real.log (sourceP N) = 3 * Real.log (sourceL N) := by
  simp [sourceP, Real.log_pow]

theorem log_sourceP1 (N : Nat) :
    Real.log (sourceP1 N) = 6 * Real.log (sourceL N) := by
  simp [sourceP1, Real.log_pow]

theorem log_sourceT (N : Nat) :
    Real.log (sourceT N) = 15 * Real.log (sourceL N) := by
  simp [sourceT, Real.log_pow]

theorem log_sourceQ {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    Real.log (sourceQ N) = sourceL N - 7 * Real.log (sourceL N) := by
  rw [sourceQ_eq_div, Real.log_div (natCast_pos_of_exp_le hN).ne'
    (pow_pos (sourceL_pos hN) 7).ne', Real.log_pow]
  rfl

theorem sourceL_half_lt_log_sourceQ {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    sourceL N / 2 < Real.log (sourceQ N) := by
  rw [log_sourceQ hN]
  have h := nat_mul_log_lt (k := 14) (sourceL_ge_2000 hN) (by norm_num)
  norm_num at h
  linarith

/-- Main paper (6.6); the powers are real, not rounded integer cutoffs. -/
def sourceVaughanU (N : Nat) : Real :=
  (N : Real) ^ ((2 : Real) / 5) * sourceL N ^ ((-4 : Real) / 5)

/-- Main paper (6.6), shared by the four Vaughan summands. -/
def sourceVaughanV (N : Nat) : Real :=
  (N : Real) ^ ((2 : Real) / 5) * sourceL N ^ ((1 : Real) / 5)

theorem sourceVaughanU_pos {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    0 < sourceVaughanU N :=
  mul_pos (Real.rpow_pos_of_pos (natCast_pos_of_exp_le hN) _)
    (Real.rpow_pos_of_pos (sourceL_pos hN) _)

theorem sourceVaughanV_pos {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    0 < sourceVaughanV N :=
  mul_pos (Real.rpow_pos_of_pos (natCast_pos_of_exp_le hN) _)
    (Real.rpow_pos_of_pos (sourceL_pos hN) _)

theorem log_sourceVaughanU {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    Real.log (sourceVaughanU N) =
      (2 * sourceL N - 4 * Real.log (sourceL N)) / 5 := by
  rw [sourceVaughanU, Real.log_mul
    (Real.rpow_pos_of_pos (natCast_pos_of_exp_le hN) _).ne'
    (Real.rpow_pos_of_pos (sourceL_pos hN) _).ne',
    Real.log_rpow (natCast_pos_of_exp_le hN), Real.log_rpow (sourceL_pos hN)]
  unfold sourceL
  ring

theorem log_sourceVaughanV {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    Real.log (sourceVaughanV N) =
      (2 * sourceL N + Real.log (sourceL N)) / 5 := by
  rw [sourceVaughanV, Real.log_mul
    (Real.rpow_pos_of_pos (natCast_pos_of_exp_le hN) _).ne'
    (Real.rpow_pos_of_pos (sourceL_pos hN) _).ne',
    Real.log_rpow (natCast_pos_of_exp_le hN), Real.log_rpow (sourceL_pos hN)]
  unfold sourceL
  ring

theorem sourceVaughanV_eq_U_mul_L {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    sourceVaughanV N = sourceVaughanU N * sourceL N := by
  unfold sourceVaughanV sourceVaughanU
  rw [mul_assoc, ← Real.rpow_add_one (sourceL_pos hN).ne']
  norm_num

theorem one_lt_sourceVaughanU {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    1 < sourceVaughanU N := by
  apply (Real.log_pos_iff (sourceVaughanU_pos hN).le).1
  rw [log_sourceVaughanU hN]
  have h := nat_mul_log_lt (k := 2) (sourceL_ge_2000 hN) (by norm_num)
  norm_num at h
  linarith

theorem sourceVaughanU_le_V {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    sourceVaughanU N ≤ sourceVaughanV N := by
  rw [sourceVaughanV_eq_U_mul_L hN]
  exact le_mul_of_one_le_right (sourceVaughanU_pos hN).le (one_le_sourceL hN)

theorem sourceVaughanV_lt_natCast {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    sourceVaughanV N < (N : Real) := by
  apply (Real.log_lt_log_iff (sourceVaughanV_pos hN) (natCast_pos_of_exp_le hN)).1
  rw [log_sourceVaughanV hN]
  change (2 * sourceL N + Real.log (sourceL N)) / 5 < sourceL N
  have h := nat_mul_log_lt (k := 1) (sourceL_ge_2000 hN) (by norm_num)
  norm_num at h
  linarith [sourceL_pos hN]

theorem sourceVaughanUV_lt_natCast {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    sourceVaughanU N * sourceVaughanV N < (N : Real) := by
  apply (Real.log_lt_log_iff (mul_pos (sourceVaughanU_pos hN) (sourceVaughanV_pos hN))
    (natCast_pos_of_exp_le hN)).1
  rw [Real.log_mul (sourceVaughanU_pos hN).ne' (sourceVaughanV_pos hN).ne',
    log_sourceVaughanU hN, log_sourceVaughanV hN]
  change (2 * sourceL N - 4 * Real.log (sourceL N)) / 5 +
    (2 * sourceL N + Real.log (sourceL N)) / 5 < sourceL N
  have hlog := Real.log_nonneg (one_le_sourceL hN)
  linarith [sourceL_pos hN]

theorem natCast_lt_sourceVaughanU_sq_mul_V {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    (N : Real) < sourceVaughanU N ^ (2 : Nat) * sourceVaughanV N := by
  apply (Real.log_lt_log_iff (natCast_pos_of_exp_le hN)
    (mul_pos (pow_pos (sourceVaughanU_pos hN) _) (sourceVaughanV_pos hN))).1
  rw [Real.log_mul (pow_pos (sourceVaughanU_pos hN) 2).ne' (sourceVaughanV_pos hN).ne',
    Real.log_pow, log_sourceVaughanU hN, log_sourceVaughanV hN]
  change sourceL N < 2 * ((2 * sourceL N - 4 * Real.log (sourceL N)) / 5) +
    (2 * sourceL N + Real.log (sourceL N)) / 5
  have h := nat_mul_log_lt (k := 7) (sourceL_ge_2000 hN) (by norm_num)
  norm_num at h
  linarith

end LiuWang.Proof.Parameters
