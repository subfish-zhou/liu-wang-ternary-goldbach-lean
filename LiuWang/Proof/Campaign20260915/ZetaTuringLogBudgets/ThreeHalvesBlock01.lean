import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesPilot

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem threeHalves_row_37 :
    ((444321 / 100000000) : ℝ) ≤ (37 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 37 ≤ (1604409 / 100000000) := by
  have hlog : Real.log ((37 : ℕ) : ℝ) ≤ (1805459 / 500000) := by
    apply log_nat_upper_certificate 37 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 37 (by norm_num)
    (3041381 / 500000) (6082763 / 1000000) (1805459 / 500000) (444321 / 100000000) (1604409 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_38 :
    ((213449 / 50000000) : ℝ) ≤ (38 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 38 ≤ (1552881 / 100000000) := by
  have hlog : Real.log ((38 : ℕ) : ℝ) ≤ (18187931 / 5000000) := by
    apply log_nat_upper_certificate 38 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 38 (by norm_num)
    (3082207 / 500000) (1232883 / 200000) (18187931 / 5000000) (213449 / 50000000) (1552881 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_39 :
    ((82117 / 20000000) : ℝ) ≤ (39 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 39 ≤ (376051 / 25000000) := by
  have hlog : Real.log ((39 : ℕ) : ℝ) ≤ (36635617 / 10000000) := by
    apply log_nat_upper_certificate 39 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 39 (by norm_num)
    (6244997 / 1000000) (3122499 / 500000) (36635617 / 10000000) (82117 / 20000000) (376051 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_40 :
    ((98821 / 25000000) : ℝ) ≤ (40 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 40 ≤ (729079 / 50000000) := by
  have hlog : Real.log ((40 : ℕ) : ℝ) ≤ (7377759 / 2000000) := by
    apply log_nat_upper_certificate 40 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 40 (by norm_num)
    (1264911 / 200000) (1581139 / 250000) (7377759 / 2000000) (98821 / 25000000) (729079 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_41 :
    ((380911 / 100000000) : ℝ) ≤ (41 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 41 ≤ (1414543 / 100000000) := by
  have hlog : Real.log ((41 : ℕ) : ℝ) ≤ (37135721 / 10000000) := by
    apply log_nat_upper_certificate 41 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 41 (by norm_num)
    (1600781 / 250000) (2049 / 320) (37135721 / 10000000) (380911 / 100000000) (1414543 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_42 :
    ((91847 / 25000000) : ℝ) ≤ (42 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 42 ≤ (1373179 / 100000000) := by
  have hlog : Real.log ((42 : ℕ) : ℝ) ≤ (37376697 / 10000000) := by
    apply log_nat_upper_certificate 42 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 42 (by norm_num)
    (324037 / 50000) (6480741 / 1000000) (37376697 / 10000000) (91847 / 25000000) (1373179 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_43 :
    ((354647 / 100000000) : ℝ) ≤ (43 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 43 ≤ (666951 / 50000000) := by
  have hlog : Real.log ((43 : ℕ) : ℝ) ≤ (18806001 / 5000000) := by
    apply log_nat_upper_certificate 43 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 43 (by norm_num)
    (3278719 / 500000) (6557439 / 1000000) (18806001 / 5000000) (354647 / 100000000) (666951 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_44 :
    ((171313 / 50000000) : ℝ) ≤ (44 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 44 ≤ (324141 / 25000000) := by
  have hlog : Real.log ((44 : ℕ) : ℝ) ≤ (37841897 / 10000000) := by
    apply log_nat_upper_certificate 44 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 44 (by norm_num)
    (6633249 / 1000000) (26533 / 4000) (37841897 / 10000000) (171313 / 50000000) (324141 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_45 :
    ((331269 / 100000000) : ℝ) ≤ (45 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 45 ≤ (1261031 / 100000000) := by
  have hlog : Real.log ((45 : ℕ) : ℝ) ≤ (304533 / 80000) := by
    apply log_nat_upper_certificate 45 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 45 (by norm_num)
    (6708203 / 1000000) (1677051 / 250000) (304533 / 80000) (331269 / 100000000) (1261031 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_46 :
    ((12821 / 4000000) : ℝ) ≤ (46 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 46 ≤ (61359 / 5000000) := by
  have hlog : Real.log ((46 : ℕ) : ℝ) ≤ (19143207 / 5000000) := by
    apply log_nat_upper_certificate 46 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 46 (by norm_num)
    (6782329 / 1000000) (678233 / 100000) (19143207 / 5000000) (12821 / 4000000) (61359 / 5000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_47 :
    ((310351 / 100000000) : ℝ) ≤ (47 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 47 ≤ (597449 / 50000000) := by
  have hlog : Real.log ((47 : ℕ) : ℝ) ≤ (38501477 / 10000000) := by
    apply log_nat_upper_certificate 47 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 47 (by norm_num)
    (3427827 / 500000) (1371131 / 200000) (38501477 / 10000000) (310351 / 100000000) (597449 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_48 :
    ((300703 / 100000000) : ℝ) ≤ (48 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 48 ≤ (1164083 / 100000000) := by
  have hlog : Real.log ((48 : ℕ) : ℝ) ≤ (38712011 / 10000000) := by
    apply log_nat_upper_certificate 48 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 48 (by norm_num)
    (6928203 / 1000000) (1732051 / 250000) (38712011 / 10000000) (300703 / 100000000) (1164083 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_49 :
    ((58309 / 20000000) : ℝ) ≤ (49 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 49 ≤ (567321 / 50000000) := by
  have hlog : Real.log ((49 : ℕ) : ℝ) ≤ (38918203 / 10000000) := by
    apply log_nat_upper_certificate 49 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 49 (by norm_num)
    7 (7000001 / 1000000) (38918203 / 10000000) (58309 / 20000000) (567321 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_50 :
    ((141421 / 50000000) : ℝ) ≤ (50 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 50 ≤ (138311 / 12500000) := by
  have hlog : Real.log ((50 : ℕ) : ℝ) ≤ (39120231 / 10000000) := by
    apply log_nat_upper_certificate 50 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 50 (by norm_num)
    (7071067 / 1000000) (1767767 / 250000) (39120231 / 10000000) (141421 / 50000000) (138311 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_51 :
    ((68641 / 25000000) : ℝ) ≤ (51 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 51 ≤ (1079541 / 100000000) := by
  have hlog : Real.log ((51 : ℕ) : ℝ) ≤ (39318257 / 10000000) := by
    apply log_nat_upper_certificate 51 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 51 (by norm_num)
    (1785357 / 250000) (7141429 / 1000000) (39318257 / 10000000) (68641 / 25000000) (1079541 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_52 :
    ((133341 / 50000000) : ℝ) ≤ (52 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 52 ≤ (1053729 / 100000000) := by
  have hlog : Real.log ((52 : ℕ) : ℝ) ≤ (19756219 / 5000000) := by
    apply log_nat_upper_certificate 52 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 52 (by norm_num)
    (3605551 / 500000) (7211103 / 1000000) (19756219 / 5000000) (133341 / 50000000) (1053729 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_53 :
    ((25917 / 10000000) : ℝ) ≤ (53 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 53 ≤ (205797 / 20000000) := by
  have hlog : Real.log ((53 : ℕ) : ℝ) ≤ (992573 / 250000) := by
    apply log_nat_upper_certificate 53 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 53 (by norm_num)
    (7280109 / 1000000) (728011 / 100000) (992573 / 250000) (25917 / 10000000) (205797 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_54 :
    ((50401 / 20000000) : ℝ) ≤ (54 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 54 ≤ (201049 / 20000000) := by
  have hlog : Real.log ((54 : ℕ) : ℝ) ≤ (39889841 / 10000000) := by
    apply log_nat_upper_certificate 54 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 54 (by norm_num)
    (7348469 / 1000000) (734847 / 100000) (39889841 / 10000000) (50401 / 20000000) (201049 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_55 :
    ((245163 / 100000000) : ℝ) ≤ (55 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 55 ≤ (982453 / 100000000) := by
  have hlog : Real.log ((55 : ℕ) : ℝ) ≤ (10018333 / 2500000) := by
    apply log_nat_upper_certificate 55 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 55 (by norm_num)
    (3708099 / 500000) (7416199 / 1000000) (10018333 / 2500000) (245163 / 100000000) (982453 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_56 :
    ((119313 / 50000000) : ℝ) ≤ (56 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 56 ≤ (192111 / 20000000) := by
  have hlog : Real.log ((56 : ℕ) : ℝ) ≤ (40253517 / 10000000) := by
    apply log_nat_upper_certificate 56 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 56 (by norm_num)
    (3741657 / 500000) (1496663 / 200000) (40253517 / 10000000) (119313 / 50000000) (192111 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_57 :
    ((116187 / 50000000) : ℝ) ≤ (57 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 57 ≤ (939501 / 100000000) := by
  have hlog : Real.log ((57 : ℕ) : ℝ) ≤ (40430513 / 10000000) := by
    apply log_nat_upper_certificate 57 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 57 (by norm_num)
    (3774917 / 500000) (1509967 / 200000) (40430513 / 10000000) (116187 / 50000000) (939501 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_58 :
    ((22639 / 10000000) : ℝ) ≤ (58 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 58 ≤ (459623 / 50000000) := by
  have hlog : Real.log ((58 : ℕ) : ℝ) ≤ (40604431 / 10000000) := by
    apply log_nat_upper_certificate 58 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 58 (by norm_num)
    (7615773 / 1000000) (3807887 / 500000) (40604431 / 10000000) (22639 / 10000000) (459623 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_59 :
    ((220659 / 100000000) : ℝ) ≤ (59 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 59 ≤ (899747 / 100000000) := by
  have hlog : Real.log ((59 : ℕ) : ℝ) ≤ (326203 / 80000) := by
    apply log_nat_upper_certificate 59 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 59 (by norm_num)
    (1536229 / 200000) (3840573 / 500000) (326203 / 80000) (220659 / 100000000) (899747 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_60 :
    ((43033 / 20000000) : ℝ) ≤ (60 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 60 ≤ (880963 / 100000000) := by
  have hlog : Real.log ((60 : ℕ) : ℝ) ≤ (20471723 / 5000000) := by
    apply log_nat_upper_certificate 60 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 60 (by norm_num)
    (3872983 / 500000) (7745967 / 1000000) (20471723 / 5000000) (43033 / 20000000) (880963 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_61 :
    ((26237 / 12500000) : ℝ) ≤ (61 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 61 ≤ (862859 / 100000000) := by
  have hlog : Real.log ((61 : ℕ) : ℝ) ≤ (41108739 / 10000000) := by
    apply log_nat_upper_certificate 61 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 61 (by norm_num)
    (7810249 / 1000000) (31241 / 4000) (41108739 / 10000000) (26237 / 12500000) (862859 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_62 :
    ((102419 / 50000000) : ℝ) ≤ (62 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 62 ≤ (422699 / 50000000) := by
  have hlog : Real.log ((62 : ℕ) : ℝ) ≤ (2579459 / 625000) := by
    apply log_nat_upper_certificate 62 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 62 (by norm_num)
    (7874007 / 1000000) (984251 / 125000) (2579459 / 625000) (102419 / 50000000) (422699 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_63 :
    ((199981 / 100000000) : ℝ) ≤ (63 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 63 ≤ (16571 / 2000000) := by
  have hlog : Real.log ((63 : ℕ) : ℝ) ≤ (10357837 / 2500000) := by
    apply log_nat_upper_certificate 63 5 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 63 (by norm_num)
    (7937253 / 1000000) (3968627 / 500000) (10357837 / 2500000) (199981 / 100000000) (16571 / 2000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_64 :
    ((12207 / 6250000) : ℝ) ≤ (64 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 64 ≤ (406141 / 50000000) := by
  have hlog : Real.log ((64 : ℕ) : ℝ) ≤ (41588831 / 10000000) := by
    apply log_nat_upper_certificate 64 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 64 (by norm_num)
    8 (8000001 / 1000000) (41588831 / 10000000) (12207 / 6250000) (406141 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_65 :
    ((95411 / 50000000) : ℝ) ≤ (65 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 65 ≤ (99571 / 12500000) := by
  have hlog : Real.log ((65 : ℕ) : ℝ) ≤ (41743873 / 10000000) := by
    apply log_nat_upper_certificate 65 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 65 (by norm_num)
    (8062257 / 1000000) (4031129 / 500000) (41743873 / 10000000) (95411 / 50000000) (99571 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_66 :
    ((93251 / 50000000) : ℝ) ≤ (66 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 66 ≤ (781381 / 100000000) := by
  have hlog : Real.log ((66 : ℕ) : ℝ) ≤ (10474137 / 2500000) := by
    apply log_nat_upper_certificate 66 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 66 (by norm_num)
    (4062019 / 500000) (8124039 / 1000000) (10474137 / 2500000) (93251 / 50000000) (781381 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_67 :
    ((91171 / 50000000) : ℝ) ≤ (67 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 67 ≤ (153339 / 20000000) := by
  have hlog : Real.log ((67 : ℕ) : ℝ) ≤ (42046927 / 10000000) := by
    apply log_nat_upper_certificate 67 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 67 (by norm_num)
    (1023169 / 125000) (8185353 / 1000000) (42046927 / 10000000) (91171 / 50000000) (153339 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_68 :
    ((35667 / 20000000) : ℝ) ≤ (68 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 68 ≤ (752487 / 100000000) := by
  have hlog : Real.log ((68 : ℕ) : ℝ) ≤ (21097539 / 5000000) := by
    apply log_nat_upper_certificate 68 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 68 (by norm_num)
    (8246211 / 1000000) (2061553 / 250000) (21097539 / 5000000) (35667 / 20000000) (752487 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem ThreeHalvesBlock01_lower :
    ((8938721 / 100000000) : ℝ) ≤ (∑ n ∈ Finset.Ico (37 : ℕ) 69, (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  have h37 := threeHalves_row_37.1
  have h38 := threeHalves_row_38.1
  have h39 := threeHalves_row_39.1
  have h40 := threeHalves_row_40.1
  have h41 := threeHalves_row_41.1
  have h42 := threeHalves_row_42.1
  have h43 := threeHalves_row_43.1
  have h44 := threeHalves_row_44.1
  have h45 := threeHalves_row_45.1
  have h46 := threeHalves_row_46.1
  have h47 := threeHalves_row_47.1
  have h48 := threeHalves_row_48.1
  have h49 := threeHalves_row_49.1
  have h50 := threeHalves_row_50.1
  have h51 := threeHalves_row_51.1
  have h52 := threeHalves_row_52.1
  have h53 := threeHalves_row_53.1
  have h54 := threeHalves_row_54.1
  have h55 := threeHalves_row_55.1
  have h56 := threeHalves_row_56.1
  have h57 := threeHalves_row_57.1
  have h58 := threeHalves_row_58.1
  have h59 := threeHalves_row_59.1
  have h60 := threeHalves_row_60.1
  have h61 := threeHalves_row_61.1
  have h62 := threeHalves_row_62.1
  have h63 := threeHalves_row_63.1
  have h64 := threeHalves_row_64.1
  have h65 := threeHalves_row_65.1
  have h66 := threeHalves_row_66.1
  have h67 := threeHalves_row_67.1
  have h68 := threeHalves_row_68.1
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68]

#print axioms ThreeHalvesBlock01_lower

theorem ThreeHalvesBlock01_upper :
    (∑ n ∈ Finset.Ico (37 : ℕ) 69, logPowerTerm n) ≤ ((34822347 / 100000000) : ℝ) := by
  have h37 := threeHalves_row_37.2
  have h38 := threeHalves_row_38.2
  have h39 := threeHalves_row_39.2
  have h40 := threeHalves_row_40.2
  have h41 := threeHalves_row_41.2
  have h42 := threeHalves_row_42.2
  have h43 := threeHalves_row_43.2
  have h44 := threeHalves_row_44.2
  have h45 := threeHalves_row_45.2
  have h46 := threeHalves_row_46.2
  have h47 := threeHalves_row_47.2
  have h48 := threeHalves_row_48.2
  have h49 := threeHalves_row_49.2
  have h50 := threeHalves_row_50.2
  have h51 := threeHalves_row_51.2
  have h52 := threeHalves_row_52.2
  have h53 := threeHalves_row_53.2
  have h54 := threeHalves_row_54.2
  have h55 := threeHalves_row_55.2
  have h56 := threeHalves_row_56.2
  have h57 := threeHalves_row_57.2
  have h58 := threeHalves_row_58.2
  have h59 := threeHalves_row_59.2
  have h60 := threeHalves_row_60.2
  have h61 := threeHalves_row_61.2
  have h62 := threeHalves_row_62.2
  have h63 := threeHalves_row_63.2
  have h64 := threeHalves_row_64.2
  have h65 := threeHalves_row_65.2
  have h66 := threeHalves_row_66.2
  have h67 := threeHalves_row_67.2
  have h68 := threeHalves_row_68.2
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68]

#print axioms ThreeHalvesBlock01_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
