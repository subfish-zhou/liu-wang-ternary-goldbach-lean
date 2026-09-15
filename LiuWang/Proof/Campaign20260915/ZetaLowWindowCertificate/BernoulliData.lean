import LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate.EMCorrection

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate

theorem bernoulli_data_0 : bernoulli 0 = (1 / 1 : ℚ) := by
  norm_num

theorem bernoulli_data_1 : bernoulli 1 = (-1 / 2 : ℚ) := by
  norm_num

theorem bernoulli_data_2 : bernoulli 2 = (1 / 6 : ℚ) := by
  norm_num

theorem bernoulli_data_3 : bernoulli 3 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 3) (by decide) (by decide)

theorem bernoulli_data_4 : bernoulli 4 = (-1 / 30 : ℚ) := by
  have h := sum_bernoulli 5
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3] at h
  linarith

theorem bernoulli_data_5 : bernoulli 5 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 5) (by decide) (by decide)

theorem bernoulli_data_6 : bernoulli 6 = (1 / 42 : ℚ) := by
  have h := sum_bernoulli 7
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5] at h
  linarith

theorem bernoulli_data_7 : bernoulli 7 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 7) (by decide) (by decide)

theorem bernoulli_data_8 : bernoulli 8 = (-1 / 30 : ℚ) := by
  have h := sum_bernoulli 9
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7] at h
  linarith

theorem bernoulli_data_9 : bernoulli 9 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 9) (by decide) (by decide)

theorem bernoulli_data_10 : bernoulli 10 = (5 / 66 : ℚ) := by
  have h := sum_bernoulli 11
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9] at h
  linarith

theorem bernoulli_data_11 : bernoulli 11 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 11) (by decide) (by decide)

theorem bernoulli_data_12 : bernoulli 12 = (-691 / 2730 : ℚ) := by
  have h := sum_bernoulli 13
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11] at h
  linarith

theorem bernoulli_data_13 : bernoulli 13 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 13) (by decide) (by decide)

theorem bernoulli_data_14 : bernoulli 14 = (7 / 6 : ℚ) := by
  have h := sum_bernoulli 15
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13] at h
  linarith

theorem bernoulli_data_15 : bernoulli 15 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 15) (by decide) (by decide)

theorem bernoulli_data_16 : bernoulli 16 = (-3617 / 510 : ℚ) := by
  have h := sum_bernoulli 17
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15] at h
  linarith

theorem bernoulli_data_17 : bernoulli 17 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 17) (by decide) (by decide)

theorem bernoulli_data_18 : bernoulli 18 = (43867 / 798 : ℚ) := by
  have h := sum_bernoulli 19
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17] at h
  linarith

theorem bernoulli_data_19 : bernoulli 19 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 19) (by decide) (by decide)

theorem bernoulli_data_20 : bernoulli 20 = (-174611 / 330 : ℚ) := by
  have h := sum_bernoulli 21
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19] at h
  linarith

theorem bernoulli_data_21 : bernoulli 21 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 21) (by decide) (by decide)

theorem bernoulli_data_22 : bernoulli 22 = (854513 / 138 : ℚ) := by
  have h := sum_bernoulli 23
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21] at h
  linarith

theorem bernoulli_data_23 : bernoulli 23 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 23) (by decide) (by decide)

theorem bernoulli_data_24 : bernoulli 24 = (-236364091 / 2730 : ℚ) := by
  have h := sum_bernoulli 25
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23] at h
  linarith

theorem bernoulli_data_25 : bernoulli 25 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 25) (by decide) (by decide)

theorem bernoulli_data_26 : bernoulli 26 = (8553103 / 6 : ℚ) := by
  have h := sum_bernoulli 27
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25] at h
  linarith

theorem bernoulli_data_27 : bernoulli 27 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 27) (by decide) (by decide)

theorem bernoulli_data_28 : bernoulli 28 = (-23749461029 / 870 : ℚ) := by
  have h := sum_bernoulli 29
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27] at h
  linarith

theorem bernoulli_data_29 : bernoulli 29 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 29) (by decide) (by decide)

theorem bernoulli_data_30 : bernoulli 30 = (8615841276005 / 14322 : ℚ) := by
  have h := sum_bernoulli 31
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29] at h
  linarith

theorem bernoulli_data_31 : bernoulli 31 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 31) (by decide) (by decide)

theorem bernoulli_data_32 : bernoulli 32 = (-7709321041217 / 510 : ℚ) := by
  have h := sum_bernoulli 33
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31] at h
  linarith

theorem bernoulli_data_33 : bernoulli 33 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 33) (by decide) (by decide)

theorem bernoulli_data_34 : bernoulli 34 = (2577687858367 / 6 : ℚ) := by
  have h := sum_bernoulli 35
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33] at h
  linarith

theorem bernoulli_data_35 : bernoulli 35 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 35) (by decide) (by decide)

theorem bernoulli_data_36 : bernoulli 36 = (-26315271553053477373 / 1919190 : ℚ) := by
  have h := sum_bernoulli 37
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35] at h
  linarith

theorem bernoulli_data_37 : bernoulli 37 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 37) (by decide) (by decide)

theorem bernoulli_data_38 : bernoulli 38 = (2929993913841559 / 6 : ℚ) := by
  have h := sum_bernoulli 39
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37] at h
  linarith

theorem bernoulli_data_39 : bernoulli 39 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 39) (by decide) (by decide)

theorem bernoulli_data_40 : bernoulli 40 = (-261082718496449122051 / 13530 : ℚ) := by
  have h := sum_bernoulli 41
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39] at h
  linarith

theorem bernoulli_data_41 : bernoulli 41 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 41) (by decide) (by decide)

theorem bernoulli_data_42 : bernoulli 42 = (1520097643918070802691 / 1806 : ℚ) := by
  have h := sum_bernoulli 43
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39, bernoulli_data_40, bernoulli_data_41] at h
  linarith

theorem bernoulli_data_43 : bernoulli 43 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 43) (by decide) (by decide)

theorem bernoulli_data_44 : bernoulli 44 = (-27833269579301024235023 / 690 : ℚ) := by
  have h := sum_bernoulli 45
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39, bernoulli_data_40, bernoulli_data_41, bernoulli_data_42, bernoulli_data_43] at h
  linarith

theorem bernoulli_data_45 : bernoulli 45 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 45) (by decide) (by decide)

theorem bernoulli_data_46 : bernoulli 46 = (596451111593912163277961 / 282 : ℚ) := by
  have h := sum_bernoulli 47
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39, bernoulli_data_40, bernoulli_data_41, bernoulli_data_42, bernoulli_data_43, bernoulli_data_44, bernoulli_data_45] at h
  linarith

theorem bernoulli_data_47 : bernoulli 47 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 47) (by decide) (by decide)

theorem bernoulli_data_48 : bernoulli 48 = (-5609403368997817686249127547 / 46410 : ℚ) := by
  have h := sum_bernoulli 49
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39, bernoulli_data_40, bernoulli_data_41, bernoulli_data_42, bernoulli_data_43, bernoulli_data_44, bernoulli_data_45, bernoulli_data_46, bernoulli_data_47] at h
  linarith

theorem bernoulli_data_49 : bernoulli 49 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 49) (by decide) (by decide)

theorem bernoulli_data_50 : bernoulli 50 = (495057205241079648212477525 / 66 : ℚ) := by
  have h := sum_bernoulli 51
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39, bernoulli_data_40, bernoulli_data_41, bernoulli_data_42, bernoulli_data_43, bernoulli_data_44, bernoulli_data_45, bernoulli_data_46, bernoulli_data_47, bernoulli_data_48, bernoulli_data_49] at h
  linarith

theorem bernoulli_data_51 : bernoulli 51 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 51) (by decide) (by decide)

theorem bernoulli_data_52 : bernoulli 52 = (-801165718135489957347924991853 / 1590 : ℚ) := by
  have h := sum_bernoulli 53
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39, bernoulli_data_40, bernoulli_data_41, bernoulli_data_42, bernoulli_data_43, bernoulli_data_44, bernoulli_data_45, bernoulli_data_46, bernoulli_data_47, bernoulli_data_48, bernoulli_data_49, bernoulli_data_50, bernoulli_data_51] at h
  linarith

theorem bernoulli_data_53 : bernoulli 53 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 53) (by decide) (by decide)

theorem bernoulli_data_54 : bernoulli 54 = (29149963634884862421418123812691 / 798 : ℚ) := by
  have h := sum_bernoulli 55
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39, bernoulli_data_40, bernoulli_data_41, bernoulli_data_42, bernoulli_data_43, bernoulli_data_44, bernoulli_data_45, bernoulli_data_46, bernoulli_data_47, bernoulli_data_48, bernoulli_data_49, bernoulli_data_50, bernoulli_data_51, bernoulli_data_52, bernoulli_data_53] at h
  linarith

theorem bernoulli_data_55 : bernoulli 55 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 55) (by decide) (by decide)

theorem bernoulli_data_56 : bernoulli 56 = (-2479392929313226753685415739663229 / 870 : ℚ) := by
  have h := sum_bernoulli 57
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39, bernoulli_data_40, bernoulli_data_41, bernoulli_data_42, bernoulli_data_43, bernoulli_data_44, bernoulli_data_45, bernoulli_data_46, bernoulli_data_47, bernoulli_data_48, bernoulli_data_49, bernoulli_data_50, bernoulli_data_51, bernoulli_data_52, bernoulli_data_53, bernoulli_data_54, bernoulli_data_55] at h
  linarith

theorem bernoulli_data_57 : bernoulli 57 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 57) (by decide) (by decide)

theorem bernoulli_data_58 : bernoulli 58 = (84483613348880041862046775994036021 / 354 : ℚ) := by
  have h := sum_bernoulli 59
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39, bernoulli_data_40, bernoulli_data_41, bernoulli_data_42, bernoulli_data_43, bernoulli_data_44, bernoulli_data_45, bernoulli_data_46, bernoulli_data_47, bernoulli_data_48, bernoulli_data_49, bernoulli_data_50, bernoulli_data_51, bernoulli_data_52, bernoulli_data_53, bernoulli_data_54, bernoulli_data_55, bernoulli_data_56, bernoulli_data_57] at h
  linarith

theorem bernoulli_data_59 : bernoulli 59 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 59) (by decide) (by decide)

theorem bernoulli_data_60 : bernoulli 60 = (-1215233140483755572040304994079820246041491 / 56786730 : ℚ) := by
  have h := sum_bernoulli 61
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39, bernoulli_data_40, bernoulli_data_41, bernoulli_data_42, bernoulli_data_43, bernoulli_data_44, bernoulli_data_45, bernoulli_data_46, bernoulli_data_47, bernoulli_data_48, bernoulli_data_49, bernoulli_data_50, bernoulli_data_51, bernoulli_data_52, bernoulli_data_53, bernoulli_data_54, bernoulli_data_55, bernoulli_data_56, bernoulli_data_57, bernoulli_data_58, bernoulli_data_59] at h
  linarith

theorem bernoulli_data_61 : bernoulli 61 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 61) (by decide) (by decide)

theorem bernoulli_data_62 : bernoulli 62 = (12300585434086858541953039857403386151 / 6 : ℚ) := by
  have h := sum_bernoulli 63
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39, bernoulli_data_40, bernoulli_data_41, bernoulli_data_42, bernoulli_data_43, bernoulli_data_44, bernoulli_data_45, bernoulli_data_46, bernoulli_data_47, bernoulli_data_48, bernoulli_data_49, bernoulli_data_50, bernoulli_data_51, bernoulli_data_52, bernoulli_data_53, bernoulli_data_54, bernoulli_data_55, bernoulli_data_56, bernoulli_data_57, bernoulli_data_58, bernoulli_data_59, bernoulli_data_60, bernoulli_data_61] at h
  linarith

theorem bernoulli_data_63 : bernoulli 63 = (0 / 1 : ℚ) := by
  simpa using bernoulli_eq_zero_of_odd (n := 63) (by decide) (by decide)

theorem bernoulli_data_64 : bernoulli 64 = (-106783830147866529886385444979142647942017 / 510 : ℚ) := by
  have h := sum_bernoulli 65
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,
    bernoulli_data_0, bernoulli_data_1, bernoulli_data_2, bernoulli_data_3, bernoulli_data_4, bernoulli_data_5, bernoulli_data_6, bernoulli_data_7, bernoulli_data_8, bernoulli_data_9, bernoulli_data_10, bernoulli_data_11, bernoulli_data_12, bernoulli_data_13, bernoulli_data_14, bernoulli_data_15, bernoulli_data_16, bernoulli_data_17, bernoulli_data_18, bernoulli_data_19, bernoulli_data_20, bernoulli_data_21, bernoulli_data_22, bernoulli_data_23, bernoulli_data_24, bernoulli_data_25, bernoulli_data_26, bernoulli_data_27, bernoulli_data_28, bernoulli_data_29, bernoulli_data_30, bernoulli_data_31, bernoulli_data_32, bernoulli_data_33, bernoulli_data_34, bernoulli_data_35, bernoulli_data_36, bernoulli_data_37, bernoulli_data_38, bernoulli_data_39, bernoulli_data_40, bernoulli_data_41, bernoulli_data_42, bernoulli_data_43, bernoulli_data_44, bernoulli_data_45, bernoulli_data_46, bernoulli_data_47, bernoulli_data_48, bernoulli_data_49, bernoulli_data_50, bernoulli_data_51, bernoulli_data_52, bernoulli_data_53, bernoulli_data_54, bernoulli_data_55, bernoulli_data_56, bernoulli_data_57, bernoulli_data_58, bernoulli_data_59, bernoulli_data_60, bernoulli_data_61, bernoulli_data_62, bernoulli_data_63] at h
  linarith

#print axioms bernoulli_data_64

end LiuWang.Proof.Campaign20260915.ZetaLowWindowCertificate
