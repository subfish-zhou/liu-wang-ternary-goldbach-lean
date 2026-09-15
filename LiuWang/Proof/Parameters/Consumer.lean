import LiuWang.Proof.Parameters.Main

set_option autoImplicit false

noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

section General

variable (N n : Nat) {b x c : Real} {k : Nat}

example (hN : Real.exp b ≤ (N : Real)) : 0 < (N : Real) :=
  natCast_pos_of_exp_le hN

example (hN : Real.exp b ≤ (N : Real)) : 0 < N :=
  nat_pos_of_exp_le hN

example (hN : Real.exp b ≤ (N : Real)) : b ≤ sourceL N :=
  le_sourceL_of_exp_le hN

example (hN : 0 < N) : Real.exp (sourceL N) = (N : Real) :=
  exp_sourceL hN

example (hx : 2000 ≤ x) : x ^ (16 : Nat) < Real.exp x :=
  pow_sixteen_lt_exp hx

example (hx : 2000 ≤ x) (hc : c ≤ 1000) (hk : k ≤ 15) :
    c * x ^ k < Real.exp x :=
  mul_pow_lt_exp hx hc hk

example (hx : 2000 ≤ x) (hk : k ≤ 16) : (k : Real) * Real.log x < x :=
  nat_mul_log_lt hx hk

example : sourceQ N = (N : Real) / sourceL N ^ (7 : Nat) :=
  sourceQ_eq_div N

example : sourceWindowLower N ≤ (n : Real) ↔ N ≤ 1000 * n :=
  sourceWindowLower_le_natCast_iff N n

example : n ∈ windowSet N ↔ sourceWindowLower N ≤ (n : Real) ∧ (n : Real) ≤ N :=
  mem_windowSet_iff_real N n

example : ⌈sourceWindowLower N⌉₊ ≤ n ↔ N ≤ 1000 * n :=
  ceil_windowLower_le_iff N n

example : Real.log (sourceP N) = 3 * Real.log (sourceL N) :=
  log_sourceP N

example : Real.log (sourceP1 N) = 6 * Real.log (sourceL N) :=
  log_sourceP1 N

example : Real.log (sourceT N) = 15 * Real.log (sourceL N) :=
  log_sourceT N

example : sourceVaughanU N =
    (N : Real) ^ ((2 : Real) / 5) * sourceL N ^ ((-4 : Real) / 5) := rfl

example : sourceVaughanV N =
    (N : Real) ^ ((2 : Real) / 5) * sourceL N ^ ((1 : Real) / 5) := rfl

end General

section Companion

variable {N n q k : Nat} {t c : Real}
variable (hN : Real.exp 2000 ≤ (N : Real))

example : 2000 ≤ sourceL N := sourceL_ge_2000 hN

example : 0 < sourceL N := sourceL_pos hN

example : 1 ≤ sourceL N := one_le_sourceL hN

example (hc : c ≤ 1000) (hk : k ≤ 15) :
    c * sourceL N ^ k < (N : Real) := mul_sourceL_pow_lt hN hc hk

example : 0 < sourceP N := sourceP_pos hN

example : 0 < sourceP1 N := sourceP1_pos hN

example : 0 < sourceQ N := sourceQ_pos hN

example : 0 < sourceT N := sourceT_pos hN

example : 1 ≤ sourceP N := one_le_sourceP hN

example : sourceP N ≤ sourceP1 N := sourceP_le_sourceP1 hN

example : sourceP1 N ≤ sourceT N := sourceP1_le_sourceT hN

example : sourceT N < sourceWindowLower N := sourceT_lt_windowLower hN

example (ht : sourceWindowLower N ≤ t) : sourceT N < t :=
  sourceT_lt_real_endpoint hN ht

example : sourceT N < (N : Real) := sourceT_lt_natCast hN

example : sourceP1 N < sourceQ N / 2 := sourceP1_lt_sourceQ_half hN

example : 2 < sourceQ N := two_lt_sourceQ hN

example : sourceQ N < (N : Real) := sourceQ_lt_natCast hN

example (hq : 0 < q) : 1 / ((q : Real) * sourceQ N) =
    sourceL N ^ (7 : Nat) / ((q : Real) * (N : Real)) :=
  approximationRadius_eq hN hq

example (hq : 0 < q) : 0 < omegaCutoff N q := omegaCutoff_pos hN hq

example (hq : 0 < q) (hqP : (q : Real) ≤ sourceP N) :
    3.36 ≤ omegaCutoff N q := omegaCutoff_ge hq hqP

example (hq : 0 < q) : 0 < deltaRadius N q := deltaRadius_pos hN hq

example : deltaRadius N q = omegaCutoff N q / (10 * Real.pi * (N : Real)) :=
  deltaRadius_eq_omega

example (hq : 0 < q) : deltaRadius N q ≤ 1 / ((q : Real) * sourceQ N) :=
  deltaRadius_le_approximationRadius hN hq

example (hn : n ∈ windowSet N) : sourceT N < (n : Real) :=
  sourceT_lt_window_member hN hn

example : q ≤ ⌊sourceQ N⌋₊ ↔ (q : Real) ≤ sourceQ N :=
  nat_le_floor_sourceQ_iff hN

example : (⌊sourceQ N⌋₊ : Real) ≤ sourceQ N := floor_sourceQ_le_natCast hN

example : sourceP1 N < (⌊sourceQ N⌋₊ : Real) := sourceP1_lt_floor_sourceQ hN

example : 2 ≤ ⌊sourceQ N⌋₊ := two_le_floor_sourceQ hN

example : q ≤ ⌊sourceP N⌋₊ ↔ (q : Real) ≤ sourceP N :=
  nat_le_floor_sourceP_iff hN

example : q ≤ ⌊sourceP1 N⌋₊ ↔ (q : Real) ≤ sourceP1 N :=
  nat_le_floor_sourceP1_iff hN

example : n ≤ ⌊sourceT N⌋₊ ↔ (n : Real) ≤ sourceT N :=
  nat_le_floor_sourceT_iff hN

example :
    2000 ≤ sourceL N ∧
    1 ≤ sourceP N ∧ sourceP N ≤ sourceP1 N ∧ sourceP1 N ≤ sourceT N ∧
    sourceT N < sourceWindowLower N ∧
    sourceP1 N < sourceQ N / 2 ∧ 2 < sourceQ N ∧ sourceQ N < (N : Real) :=
  parameters_2000 hN

example : Real.log (sourceQ N) = sourceL N - 7 * Real.log (sourceL N) :=
  log_sourceQ hN

example : sourceL N / 2 < Real.log (sourceQ N) :=
  sourceL_half_lt_log_sourceQ hN

example : 0 < sourceVaughanU N := sourceVaughanU_pos hN

example : 0 < sourceVaughanV N := sourceVaughanV_pos hN

example : Real.log (sourceVaughanU N) =
    (2 * sourceL N - 4 * Real.log (sourceL N)) / 5 :=
  log_sourceVaughanU hN

example : Real.log (sourceVaughanV N) =
    (2 * sourceL N + Real.log (sourceL N)) / 5 :=
  log_sourceVaughanV hN

example : sourceVaughanV N = sourceVaughanU N * sourceL N :=
  sourceVaughanV_eq_U_mul_L hN

example : 1 < sourceVaughanU N := one_lt_sourceVaughanU hN

example : sourceVaughanU N ≤ sourceVaughanV N := sourceVaughanU_le_V hN

example : sourceVaughanV N < (N : Real) := sourceVaughanV_lt_natCast hN

example : sourceVaughanU N * sourceVaughanV N < (N : Real) :=
  sourceVaughanUV_lt_natCast hN

example : (N : Real) < sourceVaughanU N ^ (2 : Nat) * sourceVaughanV N :=
  natCast_lt_sourceVaughanU_sq_mul_V hN

end Companion

section MainPaper

variable {N q : Nat} (hN : Real.exp 3100 ≤ (N : Real))

example : 3100 ≤ sourceL N := sourceL_ge_3100 hN

example : Real.exp 2000 ≤ (N : Real) := exp_2000_le_of_exp_3100_le hN

example : sourceP1 N < sourceQ N / 2 := sourceP1_lt_sourceQ_half_3100 hN

example (hq : 0 < q) : deltaRadius N q ≤ 1 / ((q : Real) * sourceQ N) :=
  deltaRadius_le_approximationRadius_3100 hN hq

example :
    3100 ≤ sourceL N ∧
    1 ≤ sourceP N ∧ sourceP N ≤ sourceP1 N ∧ sourceP1 N ≤ sourceT N ∧
    sourceT N < sourceWindowLower N ∧
    sourceP1 N < sourceQ N / 2 ∧ 2 < sourceQ N ∧ sourceQ N < (N : Real) :=
  parameters_3100 hN

example (a : Nat) (hq : 0 < q) : majorCoreArc N a q ⊆ approximationArc N a q := by
  intro x hx
  have hδ := deltaRadius_le_approximationRadius_3100 hN hq
  change rationalCenter a q - deltaRadius N q ≤ x ∧
    x ≤ rationalCenter a q + deltaRadius N q at hx
  change rationalCenter a q - 1 / ((q : Real) * sourceQ N) ≤ x ∧
    x ≤ rationalCenter a q + 1 / ((q : Real) * sourceQ N)
  constructor <;> linarith [hx.1, hx.2]

example (hq : (q : Real) ≤ sourceP1 N) : q ≤ ⌊sourceQ N⌋₊ := by
  have h2000 := exp_2000_le_of_exp_3100_le hN
  exact (nat_le_floor_sourceQ_iff h2000).2
    (hq.trans ((sourceP1_lt_floor_sourceQ h2000).le.trans (floor_sourceQ_le_natCast h2000)))

example (n : Nat) (hn : n ∈ windowFinset N) : sourceT N < (n : Real) := by
  exact sourceT_lt_window_member (exp_2000_le_of_exp_3100_le hN)
    ((mem_windowFinset_iff N n).1 hn)

end MainPaper
