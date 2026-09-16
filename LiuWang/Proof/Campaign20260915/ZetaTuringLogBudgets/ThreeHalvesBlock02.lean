import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesPilot

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem threeHalves_row_69 :
    ((21809 / 12500000) : ℝ) ≤ (69 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 69 ≤ (147747 / 20000000) := by
  have hlog : Real.log ((69 : ℕ) : ℝ) ≤ (21170533 / 5000000) := by
    apply log_nat_upper_certificate 69 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 69 (by norm_num)
    (8306623 / 1000000) (129791 / 15625) (21170533 / 5000000) (21809 / 12500000) (147747 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_70 :
    ((85373 / 50000000) : ℝ) ≤ (70 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 70 ≤ (362709 / 50000000) := by
  have hlog : Real.log ((70 : ℕ) : ℝ) ≤ (42484953 / 10000000) := by
    apply log_nat_upper_certificate 70 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 70 (by norm_num)
    (41833 / 5000) (8366601 / 1000000) (42484953 / 10000000) (85373 / 50000000) (362709 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_71 :
    ((10447 / 6250000) : ℝ) ≤ (71 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 71 ≤ (356259 / 50000000) := by
  have hlog : Real.log ((71 : ℕ) : ℝ) ≤ (42626799 / 10000000) := by
    apply log_nat_upper_certificate 71 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 71 (by norm_num)
    (8426149 / 1000000) (168523 / 20000) (42626799 / 10000000) (10447 / 6250000) (356259 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_72 :
    ((81841 / 50000000) : ℝ) ≤ (72 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 72 ≤ (350007 / 50000000) := by
  have hlog : Real.log ((72 : ℕ) : ℝ) ≤ (21383331 / 5000000) := by
    apply log_nat_upper_certificate 72 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 72 (by norm_num)
    (8485281 / 1000000) (4242641 / 500000) (21383331 / 5000000) (81841 / 50000000) (350007 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_73 :
    ((16033 / 10000000) : ℝ) ≤ (73 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 73 ≤ (687891 / 100000000) := by
  have hlog : Real.log ((73 : ℕ) : ℝ) ≤ (8580919 / 2000000) := by
    apply log_nat_upper_certificate 73 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 73 (by norm_num)
    (8544003 / 1000000) (2136001 / 250000) (8580919 / 2000000) (16033 / 10000000) (687891 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_74 :
    ((157091 / 100000000) : ℝ) ≤ (74 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 74 ≤ (169033 / 25000000) := by
  have hlog : Real.log ((74 : ℕ) : ℝ) ≤ (43040651 / 10000000) := by
    apply log_nat_upper_certificate 74 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 74 (by norm_num)
    (344093 / 40000) (4301163 / 500000) (43040651 / 10000000) (157091 / 100000000) (169033 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_75 :
    ((3849 / 2500000) : ℝ) ≤ (75 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 75 ≤ (664721 / 100000000) := by
  have hlog : Real.log ((75 : ℕ) : ℝ) ≤ (21587441 / 5000000) := by
    apply log_nat_upper_certificate 75 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 75 (by norm_num)
    (4330127 / 500000) (1732051 / 200000) (21587441 / 5000000) (3849 / 2500000) (664721 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_76 :
    ((150931 / 100000000) : ℝ) ≤ (76 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 76 ≤ (163411 / 25000000) := by
  have hlog : Real.log ((76 : ℕ) : ℝ) ≤ (21653667 / 5000000) := by
    apply log_nat_upper_certificate 76 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 76 (by norm_num)
    (8717797 / 1000000) (4358899 / 500000) (21653667 / 5000000) (150931 / 100000000) (163411 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_77 :
    ((37 / 25000) : ℝ) ≤ (77 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 77 ≤ (642887 / 100000000) := by
  have hlog : Real.log ((77 : ℕ) : ℝ) ≤ (8687611 / 2000000) := by
    apply log_nat_upper_certificate 77 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 77 (by norm_num)
    (2193741 / 250000) (1754993 / 200000) (8687611 / 2000000) (37 / 25000) (642887 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_78 :
    ((145163 / 100000000) : ℝ) ≤ (78 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 78 ≤ (632437 / 100000000) := by
  have hlog : Real.log ((78 : ℕ) : ℝ) ≤ (43567089 / 10000000) := by
    apply log_nat_upper_certificate 78 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 78 (by norm_num)
    (110397 / 12500) (8831761 / 1000000) (43567089 / 10000000) (145163 / 100000000) (632437 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_79 :
    ((8901 / 6250000) : ℝ) ≤ (79 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 79 ≤ (622281 / 100000000) := by
  have hlog : Real.log ((79 : ℕ) : ℝ) ≤ (43694479 / 10000000) := by
    apply log_nat_upper_certificate 79 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 79 (by norm_num)
    (4444097 / 500000) (1777639 / 200000) (43694479 / 10000000) (8901 / 6250000) (622281 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_80 :
    ((69877 / 50000000) : ℝ) ≤ (80 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 80 ≤ (612407 / 100000000) := by
  have hlog : Real.log ((80 : ℕ) : ℝ) ≤ (43820267 / 10000000) := by
    apply log_nat_upper_certificate 80 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 80 (by norm_num)
    (8944271 / 1000000) (559017 / 62500) (43820267 / 10000000) (69877 / 50000000) (612407 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_81 :
    ((68587 / 50000000) : ℝ) ≤ (81 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 81 ≤ (301403 / 50000000) := by
  have hlog : Real.log ((81 : ℕ) : ℝ) ≤ (10986123 / 2500000) := by
    apply log_nat_upper_certificate 81 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 81 (by norm_num)
    9 (9000001 / 1000000) (10986123 / 2500000) (68587 / 50000000) (301403 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_82 :
    ((8417 / 6250000) : ℝ) ≤ (82 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 82 ≤ (118693 / 20000000) := by
  have hlog : Real.log ((82 : ℕ) : ℝ) ≤ (44067193 / 10000000) := by
    apply log_nat_upper_certificate 82 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 82 (by norm_num)
    (1811077 / 200000) (4527693 / 500000) (44067193 / 10000000) (8417 / 6250000) (118693 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_83 :
    ((66123 / 50000000) : ℝ) ≤ (83 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 83 ≤ (187 / 32000) := by
  have hlog : Real.log ((83 : ℕ) : ℝ) ≤ (44188407 / 10000000) := by
    apply log_nat_upper_certificate 83 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 83 (by norm_num)
    (9110433 / 1000000) (4555217 / 500000) (44188407 / 10000000) (66123 / 50000000) (187 / 32000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_84 :
    ((129891 / 100000000) : ℝ) ≤ (84 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 84 ≤ (287763 / 50000000) := by
  have hlog : Real.log ((84 : ℕ) : ℝ) ≤ (44308169 / 10000000) := by
    apply log_nat_upper_certificate 84 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 84 (by norm_num)
    (9165151 / 1000000) (286411 / 31250) (44308169 / 10000000) (129891 / 100000000) (287763 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_85 :
    ((63803 / 50000000) : ℝ) ≤ (85 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 85 ≤ (56691 / 10000000) := by
  have hlog : Real.log ((85 : ℕ) : ℝ) ≤ (44426513 / 10000000) := by
    apply log_nat_upper_certificate 85 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 85 (by norm_num)
    (1152443 / 125000) (1843909 / 200000) (44426513 / 10000000) (63803 / 50000000) (56691 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_86 :
    ((62693 / 50000000) : ℝ) ≤ (86 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 86 ≤ (279259 / 50000000) := by
  have hlog : Real.log ((86 : ℕ) : ℝ) ≤ (44543473 / 10000000) := by
    apply log_nat_upper_certificate 86 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 86 (by norm_num)
    (4636809 / 500000) (9273619 / 1000000) (44543473 / 10000000) (62693 / 50000000) (279259 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_87 :
    ((123231 / 100000000) : ℝ) ≤ (87 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 87 ≤ (27517 / 5000000) := by
  have hlog : Real.log ((87 : ℕ) : ℝ) ≤ (22329541 / 5000000) := by
    apply log_nat_upper_certificate 87 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 87 (by norm_num)
    (9327379 / 1000000) (466369 / 50000) (22329541 / 5000000) (123231 / 100000000) (27517 / 5000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_88 :
    ((7571 / 6250000) : ℝ) ≤ (88 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 88 ≤ (542371 / 100000000) := by
  have hlog : Real.log ((88 : ℕ) : ℝ) ≤ (44773369 / 10000000) := by
    apply log_nat_upper_certificate 88 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 88 (by norm_num)
    (9380831 / 1000000) (293151 / 31250) (44773369 / 10000000) (7571 / 6250000) (542371 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_89 :
    ((1191 / 1000000) : ℝ) ≤ (89 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 89 ≤ (534601 / 100000000) := by
  have hlog : Real.log ((89 : ℕ) : ℝ) ≤ (11221591 / 2500000) := by
    apply log_nat_upper_certificate 89 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 89 (by norm_num)
    (9433981 / 1000000) (4716991 / 500000) (11221591 / 2500000) (1191 / 1000000) (534601 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_90 :
    ((117121 / 100000000) : ℝ) ≤ (90 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 90 ≤ (21081 / 4000000) := by
  have hlog : Real.log ((90 : ℕ) : ℝ) ≤ (44998097 / 10000000) := by
    apply log_nat_upper_certificate 90 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 90 (by norm_num)
    (592927 / 62500) (9486833 / 1000000) (44998097 / 10000000) (117121 / 100000000) (21081 / 4000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_91 :
    ((28799 / 25000000) : ℝ) ≤ (91 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 91 ≤ (259817 / 50000000) := by
  have hlog : Real.log ((91 : ℕ) : ℝ) ≤ (11277149 / 2500000) := by
    apply log_nat_upper_certificate 91 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 91 (by norm_num)
    (149053 / 15625) (9539393 / 1000000) (11277149 / 2500000) (28799 / 25000000) (259817 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_92 :
    ((113323 / 100000000) : ℝ) ≤ (92 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 92 ≤ (512423 / 100000000) := by
  have hlog : Real.log ((92 : ℕ) : ℝ) ≤ (22608943 / 5000000) := by
    apply log_nat_upper_certificate 92 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 92 (by norm_num)
    (9591663 / 1000000) (599479 / 62500) (22608943 / 5000000) (113323 / 100000000) (512423 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_93 :
    ((223 / 200000) : ℝ) ≤ (93 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 93 ≤ (252693 / 50000000) := by
  have hlog : Real.log ((93 : ℕ) : ℝ) ≤ (9065199 / 2000000) := by
    apply log_nat_upper_certificate 93 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 93 (by norm_num)
    (192873 / 20000) (9643651 / 1000000) (9065199 / 2000000) (223 / 200000) (252693 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_94 :
    ((4389 / 4000000) : ℝ) ≤ (94 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 94 ≤ (498517 / 100000000) := by
  have hlog : Real.log ((94 : ℕ) : ℝ) ≤ (11358237 / 2500000) := by
    apply log_nat_upper_certificate 94 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 94 (by norm_num)
    (9695359 / 1000000) (30298 / 3125) (11358237 / 2500000) (4389 / 4000000) (498517 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_95 :
    ((107997 / 100000000) : ℝ) ≤ (95 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 95 ≤ (491809 / 100000000) := by
  have hlog : Real.log ((95 : ℕ) : ℝ) ≤ (45538769 / 10000000) := by
    apply log_nat_upper_certificate 95 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 95 (by norm_num)
    (4873397 / 500000) (1949359 / 200000) (45538769 / 10000000) (107997 / 100000000) (491809 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_96 :
    ((53157 / 50000000) : ℝ) ≤ (96 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 96 ≤ (242629 / 50000000) := by
  have hlog : Real.log ((96 : ℕ) : ℝ) ≤ (22821741 / 5000000) := by
    apply log_nat_upper_certificate 96 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 96 (by norm_num)
    (4898979 / 500000) (9797959 / 1000000) (22821741 / 5000000) (53157 / 50000000) (242629 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_97 :
    ((52337 / 50000000) : ℝ) ≤ (97 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 97 ≤ (239429 / 50000000) := by
  have hlog : Real.log ((97 : ℕ) : ℝ) ≤ (4574711 / 1000000) := by
    apply log_nat_upper_certificate 97 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 97 (by norm_num)
    (9848857 / 1000000) (4924429 / 500000) (4574711 / 1000000) (52337 / 50000000) (239429 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_98 :
    ((25769 / 25000000) : ℝ) ≤ (98 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 98 ≤ (118151 / 25000000) := by
  have hlog : Real.log ((98 : ℕ) : ℝ) ≤ (1833987 / 400000) := by
    apply log_nat_upper_certificate 98 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 98 (by norm_num)
    (4949747 / 500000) (1979899 / 200000) (1833987 / 400000) (25769 / 25000000) (118151 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_99 :
    ((50759 / 50000000) : ℝ) ≤ (99 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 99 ≤ (116623 / 25000000) := by
  have hlog : Real.log ((99 : ℕ) : ℝ) ≤ (45951199 / 10000000) := by
    apply log_nat_upper_certificate 99 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 99 (by norm_num)
    (4974937 / 500000) (79599 / 8000) (45951199 / 10000000) (50759 / 50000000) (116623 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_100 :
    ((99999 / 100000000) : ℝ) ≤ (100 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 100 ≤ (230259 / 50000000) := by
  have hlog : Real.log ((100 : ℕ) : ℝ) ≤ (23025851 / 5000000) := by
    apply log_nat_upper_certificate 100 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 100 (by norm_num)
    10 (10000001 / 1000000) (23025851 / 5000000) (99999 / 100000000) (230259 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem ThreeHalvesBlock02_lower :
    ((2107291 / 50000000) : ℝ) ≤ (∑ n ∈ Finset.Ico (69 : ℕ) 101, (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  have h69 := threeHalves_row_69.1
  have h70 := threeHalves_row_70.1
  have h71 := threeHalves_row_71.1
  have h72 := threeHalves_row_72.1
  have h73 := threeHalves_row_73.1
  have h74 := threeHalves_row_74.1
  have h75 := threeHalves_row_75.1
  have h76 := threeHalves_row_76.1
  have h77 := threeHalves_row_77.1
  have h78 := threeHalves_row_78.1
  have h79 := threeHalves_row_79.1
  have h80 := threeHalves_row_80.1
  have h81 := threeHalves_row_81.1
  have h82 := threeHalves_row_82.1
  have h83 := threeHalves_row_83.1
  have h84 := threeHalves_row_84.1
  have h85 := threeHalves_row_85.1
  have h86 := threeHalves_row_86.1
  have h87 := threeHalves_row_87.1
  have h88 := threeHalves_row_88.1
  have h89 := threeHalves_row_89.1
  have h90 := threeHalves_row_90.1
  have h91 := threeHalves_row_91.1
  have h92 := threeHalves_row_92.1
  have h93 := threeHalves_row_93.1
  have h94 := threeHalves_row_94.1
  have h95 := threeHalves_row_95.1
  have h96 := threeHalves_row_96.1
  have h97 := threeHalves_row_97.1
  have h98 := threeHalves_row_98.1
  have h99 := threeHalves_row_99.1
  have h100 := threeHalves_row_100.1
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100]

#print axioms ThreeHalvesBlock02_lower

theorem ThreeHalvesBlock02_upper :
    (∑ n ∈ Finset.Ico (69 : ℕ) 101, logPowerTerm n) ≤ ((18596521 / 100000000) : ℝ) := by
  have h69 := threeHalves_row_69.2
  have h70 := threeHalves_row_70.2
  have h71 := threeHalves_row_71.2
  have h72 := threeHalves_row_72.2
  have h73 := threeHalves_row_73.2
  have h74 := threeHalves_row_74.2
  have h75 := threeHalves_row_75.2
  have h76 := threeHalves_row_76.2
  have h77 := threeHalves_row_77.2
  have h78 := threeHalves_row_78.2
  have h79 := threeHalves_row_79.2
  have h80 := threeHalves_row_80.2
  have h81 := threeHalves_row_81.2
  have h82 := threeHalves_row_82.2
  have h83 := threeHalves_row_83.2
  have h84 := threeHalves_row_84.2
  have h85 := threeHalves_row_85.2
  have h86 := threeHalves_row_86.2
  have h87 := threeHalves_row_87.2
  have h88 := threeHalves_row_88.2
  have h89 := threeHalves_row_89.2
  have h90 := threeHalves_row_90.2
  have h91 := threeHalves_row_91.2
  have h92 := threeHalves_row_92.2
  have h93 := threeHalves_row_93.2
  have h94 := threeHalves_row_94.2
  have h95 := threeHalves_row_95.2
  have h96 := threeHalves_row_96.2
  have h97 := threeHalves_row_97.2
  have h98 := threeHalves_row_98.2
  have h99 := threeHalves_row_99.2
  have h100 := threeHalves_row_100.2
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100]

#print axioms ThreeHalvesBlock02_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
