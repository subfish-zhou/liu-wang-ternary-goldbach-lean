import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesPilot

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem threeHalves_row_5 :
    ((8944271 / 100000000) : ℝ) ≤ (5 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 5 ≤ (7197629 / 50000000) := by
  have hlog : Real.log ((5 : ℕ) : ℝ) ≤ (804719 / 500000) := by
    apply log_nat_upper_certificate 5 2 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 5 (by norm_num)
    (2236067 / 1000000) (559017 / 250000) (804719 / 500000) (8944271 / 100000000) (7197629 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_6 :
    ((6804137 / 100000000) : ℝ) ≤ (6 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 6 ≤ (12191383 / 100000000) := by
  have hlog : Real.log ((6 : ℕ) : ℝ) ≤ (3583519 / 2000000) := by
    apply log_nat_upper_certificate 6 2 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 6 (by norm_num)
    (2449489 / 1000000) (244949 / 100000) (3583519 / 2000000) (6804137 / 100000000) (12191383 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_7 :
    ((5399491 / 100000000) : ℝ) ≤ (7 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 7 ≤ (10506929 / 100000000) := by
  have hlog : Real.log ((7 : ℕ) : ℝ) ≤ (9729551 / 5000000) := by
    apply log_nat_upper_certificate 7 2 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 7 (by norm_num)
    (2645751 / 1000000) (330719 / 125000) (9729551 / 5000000) (5399491 / 100000000) (10506929 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_8 :
    ((552427 / 12500000) : ℝ) ≤ (8 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 8 ≤ (9189921 / 100000000) := by
  have hlog : Real.log ((8 : ℕ) : ℝ) ≤ (1299651 / 625000) := by
    apply log_nat_upper_certificate 8 3 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 8 (by norm_num)
    (2828427 / 1000000) (707107 / 250000) (1299651 / 625000) (552427 / 12500000) (9189921 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_9 :
    ((1851851 / 50000000) : ℝ) ≤ (9 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 9 ≤ (8137869 / 100000000) := by
  have hlog : Real.log ((9 : ℕ) : ℝ) ≤ (10986123 / 5000000) := by
    apply log_nat_upper_certificate 9 3 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 9 (by norm_num)
    3 (3000001 / 1000000) (10986123 / 5000000) (1851851 / 50000000) (8137869 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_10 :
    ((3162277 / 100000000) : ℝ) ≤ (10 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 10 ≤ (1456283 / 20000000) := by
  have hlog : Real.log ((10 : ℕ) : ℝ) ≤ (23025851 / 10000000) := by
    apply log_nat_upper_certificate 10 3 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 10 (by norm_num)
    (3162277 / 1000000) (1581139 / 500000) (23025851 / 10000000) (3162277 / 100000000) (1456283 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_11 :
    ((685253 / 25000000) : ℝ) ≤ (11 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 11 ≤ (3286331 / 50000000) := by
  have hlog : Real.log ((11 : ℕ) : ℝ) ≤ (23978953 / 10000000) := by
    apply log_nat_upper_certificate 11 3 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 11 (by norm_num)
    (207289 / 62500) (26533 / 8000) (23978953 / 10000000) (685253 / 25000000) (3286331 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_12 :
    ((3849 / 160000) : ℝ) ≤ (12 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 12 ≤ (2988879 / 50000000) := by
  have hlog : Real.log ((12 : ℕ) : ℝ) ≤ (24849067 / 10000000) := by
    apply log_nat_upper_certificate 12 3 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 12 (by norm_num)
    (3464101 / 1000000) (1732051 / 500000) (24849067 / 10000000) (3849 / 160000) (2988879 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_13 :
    ((2133461 / 100000000) : ℝ) ≤ (13 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 13 ≤ (171007 / 3125000) := by
  have hlog : Real.log ((13 : ℕ) : ℝ) ≤ (12824747 / 5000000) := by
    apply log_nat_upper_certificate 13 3 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 13 (by norm_num)
    (3605551 / 1000000) (225347 / 62500) (12824747 / 5000000) (2133461 / 100000000) (171007 / 3125000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_14 :
    ((119313 / 6250000) : ℝ) ≤ (14 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 14 ≤ (1007597 / 20000000) := by
  have hlog : Real.log ((14 : ℕ) : ℝ) ≤ (13195287 / 5000000) := by
    apply log_nat_upper_certificate 14 3 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 14 (by norm_num)
    (3741657 / 1000000) (1870829 / 500000) (13195287 / 5000000) (119313 / 6250000) (1007597 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_15 :
    ((68853 / 4000000) : ℝ) ≤ (15 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 15 ≤ (2330719 / 50000000) := by
  have hlog : Real.log ((15 : ℕ) : ℝ) ≤ (27080503 / 10000000) := by
    apply log_nat_upper_certificate 15 3 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 15 (by norm_num)
    (3872983 / 1000000) (484123 / 125000) (27080503 / 10000000) (68853 / 4000000) (2330719 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_16 :
    ((1562499 / 100000000) : ℝ) ≤ (16 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 16 ≤ (433217 / 10000000) := by
  have hlog : Real.log ((16 : ℕ) : ℝ) ≤ (433217 / 156250) := by
    apply log_nat_upper_certificate 16 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 16 (by norm_num)
    4 (4000001 / 1000000) (433217 / 156250) (1562499 / 100000000) (433217 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_17 :
    ((35667 / 2500000) : ℝ) ≤ (17 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 17 ≤ (404209 / 10000000) := by
  have hlog : Real.log ((17 : ℕ) : ℝ) ≤ (14166067 / 5000000) := by
    apply log_nat_upper_certificate 17 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 17 (by norm_num)
    (824621 / 200000) (2061553 / 500000) (14166067 / 5000000) (35667 / 2500000) (404209 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_18 :
    ((81841 / 6250000) : ℝ) ≤ (18 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 18 ≤ (3784819 / 100000000) := by
  have hlog : Real.log ((18 : ℕ) : ℝ) ≤ (14451859 / 5000000) := by
    apply log_nat_upper_certificate 18 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 18 (by norm_num)
    (53033 / 12500) (4242641 / 1000000) (14451859 / 5000000) (81841 / 6250000) (3784819 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_19 :
    ((1207451 / 100000000) : ℝ) ≤ (19 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 19 ≤ (888817 / 25000000) := by
  have hlog : Real.log ((19 : ℕ) : ℝ) ≤ (2944439 / 1000000) := by
    apply log_nat_upper_certificate 19 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 19 (by norm_num)
    (2179449 / 500000) (4358899 / 1000000) (2944439 / 1000000) (1207451 / 100000000) (888817 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_20 :
    ((1118033 / 100000000) : ℝ) ≤ (20 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 20 ≤ (837333 / 25000000) := by
  have hlog : Real.log ((20 : ℕ) : ℝ) ≤ (29957323 / 10000000) := by
    apply log_nat_upper_certificate 20 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 20 (by norm_num)
    (894427 / 200000) (559017 / 125000) (29957323 / 10000000) (1118033 / 100000000) (837333 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_21 :
    ((259783 / 25000000) : ℝ) ≤ (21 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 21 ≤ (197729 / 6250000) := by
  have hlog : Real.log ((21 : ℕ) : ℝ) ≤ (1217809 / 400000) := by
    apply log_nat_upper_certificate 21 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 21 (by norm_num)
    (183303 / 40000) (286411 / 62500) (1217809 / 400000) (259783 / 25000000) (197729 / 6250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_22 :
    ((484547 / 50000000) : ℝ) ≤ (22 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 22 ≤ (374439 / 12500000) := by
  have hlog : Real.log ((22 : ℕ) : ℝ) ≤ (1236417 / 400000) := by
    apply log_nat_upper_certificate 22 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 22 (by norm_num)
    (938083 / 200000) (293151 / 62500) (1236417 / 400000) (484547 / 50000000) (374439 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_23 :
    ((113323 / 12500000) : ℝ) ≤ (23 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 23 ≤ (2842591 / 100000000) := by
  have hlog : Real.log ((23 : ℕ) : ℝ) ≤ (31354943 / 10000000) := by
    apply log_nat_upper_certificate 23 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 23 (by norm_num)
    (4795831 / 1000000) (599479 / 125000) (31354943 / 10000000) (113323 / 12500000) (2842591 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_24 :
    ((850517 / 100000000) : ℝ) ≤ (24 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 24 ≤ (2702991 / 100000000) := by
  have hlog : Real.log ((24 : ℕ) : ℝ) ≤ (31780539 / 10000000) := by
    apply log_nat_upper_certificate 24 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 24 (by norm_num)
    (4898979 / 1000000) (244949 / 50000) (31780539 / 10000000) (850517 / 100000000) (2702991 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_25 :
    ((799999 / 100000000) : ℝ) ≤ (25 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 25 ≤ (2575101 / 100000000) := by
  have hlog : Real.log ((25 : ℕ) : ℝ) ≤ (32188759 / 10000000) := by
    apply log_nat_upper_certificate 25 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 25 (by norm_num)
    5 (5000001 / 1000000) (32188759 / 10000000) (799999 / 100000000) (2575101 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_26 :
    ((188573 / 25000000) : ℝ) ≤ (26 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 26 ≤ (61439 / 2500000) := by
  have hlog : Real.log ((26 : ℕ) : ℝ) ≤ (16290483 / 5000000) := by
    apply log_nat_upper_certificate 26 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 26 (by norm_num)
    (5099019 / 1000000) (254951 / 50000) (16290483 / 5000000) (188573 / 25000000) (61439 / 2500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_27 :
    ((356389 / 50000000) : ℝ) ≤ (27 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 27 ≤ (2349201 / 100000000) := by
  have hlog : Real.log ((27 : ℕ) : ℝ) ≤ (32958369 / 10000000) := by
    apply log_nat_upper_certificate 27 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 27 (by norm_num)
    (649519 / 125000) (5196153 / 1000000) (32958369 / 10000000) (356389 / 50000000) (2349201 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_28 :
    ((84367 / 12500000) : ℝ) ≤ (28 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 28 ≤ (2249027 / 100000000) := by
  have hlog : Real.log ((28 : ℕ) : ℝ) ≤ (16661023 / 5000000) := by
    apply log_nat_upper_certificate 28 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 28 (by norm_num)
    (2645751 / 500000) (5291503 / 1000000) (16661023 / 5000000) (84367 / 12500000) (2249027 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_29 :
    ((80041 / 12500000) : ℝ) ≤ (29 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 29 ≤ (2156177 / 100000000) := by
  have hlog : Real.log ((29 : ℕ) : ℝ) ≤ (33672959 / 10000000) := by
    apply log_nat_upper_certificate 29 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 29 (by norm_num)
    (1346291 / 250000) (1077033 / 200000) (33672959 / 10000000) (80041 / 12500000) (2156177 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_30 :
    ((30429 / 5000000) : ℝ) ≤ (30 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 30 ≤ (129369 / 6250000) := by
  have hlog : Real.log ((30 : ℕ) : ℝ) ≤ (17005987 / 5000000) := by
    apply log_nat_upper_certificate 30 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 30 (by norm_num)
    (219089 / 40000) (2738613 / 500000) (17005987 / 5000000) (30429 / 5000000) (129369 / 6250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_31 :
    ((579371 / 100000000) : ℝ) ≤ (31 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 31 ≤ (1989557 / 100000000) := by
  have hlog : Real.log ((31 : ℕ) : ℝ) ≤ (34339873 / 10000000) := by
    apply log_nat_upper_certificate 31 4 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 31 (by norm_num)
    (1391941 / 250000) (1113553 / 200000) (34339873 / 10000000) (579371 / 100000000) (1989557 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_32 :
    ((552427 / 100000000) : ℝ) ≤ (32 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 32 ≤ (1914567 / 100000000) := by
  have hlog : Real.log ((32 : ℕ) : ℝ) ≤ (433217 / 125000) := by
    apply log_nat_upper_certificate 32 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 32 (by norm_num)
    (2828427 / 500000) (1131371 / 200000) (433217 / 125000) (552427 / 100000000) (1914567 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_33 :
    ((131877 / 25000000) : ℝ) ≤ (33 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 33 ≤ (1844437 / 100000000) := by
  have hlog : Real.log ((33 : ℕ) : ℝ) ≤ (8741269 / 2500000) := by
    apply log_nat_upper_certificate 33 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 33 (by norm_num)
    (2872281 / 500000) (5744563 / 1000000) (8741269 / 2500000) (131877 / 25000000) (1844437 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_34 :
    ((504407 / 100000000) : ℝ) ≤ (34 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 34 ≤ (444681 / 25000000) := by
  have hlog : Real.log ((34 : ℕ) : ℝ) ≤ (17631803 / 5000000) := by
    apply log_nat_upper_certificate 34 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 34 (by norm_num)
    (5830951 / 1000000) (728869 / 125000) (17631803 / 5000000) (504407 / 100000000) (444681 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_35 :
    ((96589 / 20000000) : ℝ) ≤ (35 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 35 ≤ (1717039 / 100000000) := by
  have hlog : Real.log ((35 : ℕ) : ℝ) ≤ (35553481 / 10000000) := by
    apply log_nat_upper_certificate 35 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 35 (by norm_num)
    (5916079 / 1000000) (73951 / 12500) (35553481 / 10000000) (96589 / 20000000) (1717039 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_36 :
    ((231481 / 50000000) : ℝ) ≤ (36 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 36 ≤ (1659037 / 100000000) := by
  have hlog : Real.log ((36 : ℕ) : ℝ) ≤ (3583519 / 1000000) := by
    apply log_nat_upper_certificate 36 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 36 (by norm_num)
    6 (6000001 / 1000000) (3583519 / 1000000) (231481 / 50000000) (1659037 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem ThreeHalvesBlock00_lower :
    ((7629213 / 12500000) : ℝ) ≤ (∑ n ∈ Finset.Ico (5 : ℕ) 37, (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  have h5 := threeHalves_row_5.1
  have h6 := threeHalves_row_6.1
  have h7 := threeHalves_row_7.1
  have h8 := threeHalves_row_8.1
  have h9 := threeHalves_row_9.1
  have h10 := threeHalves_row_10.1
  have h11 := threeHalves_row_11.1
  have h12 := threeHalves_row_12.1
  have h13 := threeHalves_row_13.1
  have h14 := threeHalves_row_14.1
  have h15 := threeHalves_row_15.1
  have h16 := threeHalves_row_16.1
  have h17 := threeHalves_row_17.1
  have h18 := threeHalves_row_18.1
  have h19 := threeHalves_row_19.1
  have h20 := threeHalves_row_20.1
  have h21 := threeHalves_row_21.1
  have h22 := threeHalves_row_22.1
  have h23 := threeHalves_row_23.1
  have h24 := threeHalves_row_24.1
  have h25 := threeHalves_row_25.1
  have h26 := threeHalves_row_26.1
  have h27 := threeHalves_row_27.1
  have h28 := threeHalves_row_28.1
  have h29 := threeHalves_row_29.1
  have h30 := threeHalves_row_30.1
  have h31 := threeHalves_row_31.1
  have h32 := threeHalves_row_32.1
  have h33 := threeHalves_row_33.1
  have h34 := threeHalves_row_34.1
  have h35 := threeHalves_row_35.1
  have h36 := threeHalves_row_36.1
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

#print axioms ThreeHalvesBlock00_lower

theorem ThreeHalvesBlock00_upper :
    (∑ n ∈ Finset.Ico (5 : ℕ) 37, logPowerTerm n) ≤ ((14495361 / 10000000) : ℝ) := by
  have h5 := threeHalves_row_5.2
  have h6 := threeHalves_row_6.2
  have h7 := threeHalves_row_7.2
  have h8 := threeHalves_row_8.2
  have h9 := threeHalves_row_9.2
  have h10 := threeHalves_row_10.2
  have h11 := threeHalves_row_11.2
  have h12 := threeHalves_row_12.2
  have h13 := threeHalves_row_13.2
  have h14 := threeHalves_row_14.2
  have h15 := threeHalves_row_15.2
  have h16 := threeHalves_row_16.2
  have h17 := threeHalves_row_17.2
  have h18 := threeHalves_row_18.2
  have h19 := threeHalves_row_19.2
  have h20 := threeHalves_row_20.2
  have h21 := threeHalves_row_21.2
  have h22 := threeHalves_row_22.2
  have h23 := threeHalves_row_23.2
  have h24 := threeHalves_row_24.2
  have h25 := threeHalves_row_25.2
  have h26 := threeHalves_row_26.2
  have h27 := threeHalves_row_27.2
  have h28 := threeHalves_row_28.2
  have h29 := threeHalves_row_29.2
  have h30 := threeHalves_row_30.2
  have h31 := threeHalves_row_31.2
  have h32 := threeHalves_row_32.2
  have h33 := threeHalves_row_33.2
  have h34 := threeHalves_row_34.2
  have h35 := threeHalves_row_35.2
  have h36 := threeHalves_row_36.2
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]

#print axioms ThreeHalvesBlock00_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
