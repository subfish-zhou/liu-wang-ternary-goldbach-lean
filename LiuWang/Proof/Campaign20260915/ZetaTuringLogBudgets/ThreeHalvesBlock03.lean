import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesPilot

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem threeHalves_row_101 :
    ((49259 / 50000000) : ℝ) ≤ (101 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 101 ≤ (18187 / 4000000) := by
  have hlog : Real.log ((101 : ℕ) : ℝ) ≤ (23075603 / 5000000) := by
    apply log_nat_upper_certificate 101 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 101 (by norm_num)
    (80399 / 8000) (2512469 / 250000) (23075603 / 5000000) (49259 / 50000000) (18187 / 4000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_102 :
    ((97073 / 100000000) : ℝ) ≤ (102 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 102 ≤ (224481 / 50000000) := by
  have hlog : Real.log ((102 : ℕ) : ℝ) ≤ (46249729 / 10000000) := by
    apply log_nat_upper_certificate 102 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 102 (by norm_num)
    (631219 / 62500) (2019901 / 200000) (46249729 / 10000000) (97073 / 100000000) (224481 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_103 :
    ((95663 / 100000000) : ℝ) ≤ (103 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 103 ≤ (443373 / 100000000) := by
  have hlog : Real.log ((103 : ℕ) : ℝ) ≤ (4634729 / 1000000) := by
    apply log_nat_upper_certificate 103 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 103 (by norm_num)
    (10148891 / 1000000) (2537223 / 250000) (4634729 / 1000000) (95663 / 100000000) (443373 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_104 :
    ((47143 / 50000000) : ℝ) ≤ (104 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 104 ≤ (27369 / 6250000) := by
  have hlog : Real.log ((104 : ℕ) : ℝ) ≤ (4644391 / 1000000) := by
    apply log_nat_upper_certificate 104 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 104 (by norm_num)
    (10198039 / 1000000) (254951 / 25000) (4644391 / 1000000) (47143 / 50000000) (27369 / 6250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_105 :
    ((46471 / 50000000) : ℝ) ≤ (105 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 105 ≤ (432553 / 100000000) := by
  have hlog : Real.log ((105 : ℕ) : ℝ) ≤ (11634901 / 2500000) := by
    apply log_nat_upper_certificate 105 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 105 (by norm_num)
    (204939 / 20000) (10246951 / 1000000) (11634901 / 2500000) (46471 / 50000000) (432553 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_106 :
    ((9163 / 10000000) : ℝ) ≤ (106 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 106 ≤ (85463 / 20000000) := by
  have hlog : Real.log ((106 : ℕ) : ℝ) ≤ (46634391 / 10000000) := by
    apply log_nat_upper_certificate 106 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 106 (by norm_num)
    (1029563 / 100000) (10295631 / 1000000) (46634391 / 10000000) (9163 / 10000000) (85463 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_107 :
    ((90349 / 100000000) : ℝ) ≤ (107 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 107 ≤ (422187 / 100000000) := by
  have hlog : Real.log ((107 : ℕ) : ℝ) ≤ (46728289 / 10000000) := by
    apply log_nat_upper_certificate 107 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 107 (by norm_num)
    (129301 / 12500) (10344081 / 1000000) (46728289 / 10000000) (90349 / 100000000) (422187 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_108 :
    ((89097 / 100000000) : ℝ) ≤ (108 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 108 ≤ (208583 / 50000000) := by
  have hlog : Real.log ((108 : ℕ) : ℝ) ≤ (46821313 / 10000000) := by
    apply log_nat_upper_certificate 108 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 108 (by norm_num)
    (649519 / 62500) (2078461 / 200000) (46821313 / 10000000) (89097 / 100000000) (208583 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_109 :
    ((87873 / 100000000) : ℝ) ≤ (109 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 109 ≤ (51531 / 12500000) := by
  have hlog : Real.log ((109 : ℕ) : ℝ) ≤ (46913479 / 10000000) := by
    apply log_nat_upper_certificate 109 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 109 (by norm_num)
    (5220153 / 500000) (10440307 / 1000000) (46913479 / 10000000) (87873 / 100000000) (51531 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_110 :
    ((43339 / 50000000) : ℝ) ≤ (110 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 110 ≤ (407431 / 100000000) := by
  have hlog : Real.log ((110 : ℕ) : ℝ) ≤ (11751201 / 2500000) := by
    apply log_nat_upper_certificate 110 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 110 (by norm_num)
    (1311011 / 125000) (10488089 / 1000000) (11751201 / 2500000) (43339 / 50000000) (407431 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_111 :
    ((85509 / 100000000) : ℝ) ≤ (111 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 111 ≤ (402711 / 100000000) := by
  have hlog : Real.log ((111 : ℕ) : ℝ) ≤ (47095303 / 10000000) := by
    apply log_nat_upper_certificate 111 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 111 (by norm_num)
    (10535653 / 1000000) (5267827 / 500000) (47095303 / 10000000) (85509 / 100000000) (402711 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_112 :
    ((84367 / 100000000) : ℝ) ≤ (112 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 112 ≤ (199043 / 50000000) := by
  have hlog : Real.log ((112 : ℕ) : ℝ) ≤ (47184989 / 10000000) := by
    apply log_nat_upper_certificate 112 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 112 (by norm_num)
    (2116601 / 200000) (5291503 / 500000) (47184989 / 10000000) (84367 / 100000000) (199043 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_113 :
    ((83249 / 100000000) : ℝ) ≤ (113 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 113 ≤ (196777 / 50000000) := by
  have hlog : Real.log ((113 : ℕ) : ℝ) ≤ (47273879 / 10000000) := by
    apply log_nat_upper_certificate 113 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 113 (by norm_num)
    (2126029 / 200000) (5315073 / 500000) (47273879 / 10000000) (83249 / 100000000) (196777 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_114 :
    ((20539 / 25000000) : ℝ) ≤ (114 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 114 ≤ (389111 / 100000000) := by
  have hlog : Real.log ((114 : ℕ) : ℝ) ≤ (9472397 / 2000000) := by
    apply log_nat_upper_certificate 114 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 114 (by norm_num)
    (5338539 / 500000) (10677079 / 1000000) (9472397 / 2000000) (20539 / 25000000) (389111 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_115 :
    ((81087 / 100000000) : ℝ) ≤ (115 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 115 ≤ (76951 / 20000000) := by
  have hlog : Real.log ((115 : ℕ) : ℝ) ≤ (23724661 / 5000000) := by
    apply log_nat_upper_certificate 115 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 115 (by norm_num)
    (2144761 / 200000) (5361903 / 500000) (23724661 / 5000000) (81087 / 100000000) (76951 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_116 :
    ((80041 / 100000000) : ℝ) ≤ (116 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 116 ≤ (380483 / 100000000) := by
  have hlog : Real.log ((116 : ℕ) : ℝ) ≤ (23767951 / 5000000) := by
    apply log_nat_upper_certificate 116 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 116 (by norm_num)
    (10770329 / 1000000) (1077033 / 100000) (23767951 / 5000000) (80041 / 100000000) (380483 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_117 :
    ((79017 / 100000000) : ℝ) ≤ (117 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 117 ≤ (188147 / 50000000) := by
  have hlog : Real.log ((117 : ℕ) : ℝ) ≤ (2381087 / 500000) := by
    apply log_nat_upper_certificate 117 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 117 (by norm_num)
    (10816653 / 1000000) (5408327 / 500000) (2381087 / 500000) (79017 / 100000000) (188147 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_118 :
    ((39007 / 50000000) : ℝ) ≤ (118 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 118 ≤ (74437 / 20000000) := by
  have hlog : Real.log ((118 : ℕ) : ℝ) ≤ (47706847 / 10000000) := by
    apply log_nat_upper_certificate 118 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 118 (by norm_num)
    (543139 / 50000) (10862781 / 1000000) (47706847 / 10000000) (39007 / 50000000) (74437 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_119 :
    ((77033 / 100000000) : ℝ) ≤ (119 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 119 ≤ (368153 / 100000000) := by
  have hlog : Real.log ((119 : ℕ) : ℝ) ≤ (9558247 / 2000000) := by
    apply log_nat_upper_certificate 119 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 119 (by norm_num)
    (1363589 / 125000) (10908713 / 1000000) (9558247 / 2000000) (77033 / 100000000) (368153 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_120 :
    ((9509 / 12500000) : ℝ) ≤ (120 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 120 ≤ (364197 / 100000000) := by
  have hlog : Real.log ((120 : ℕ) : ℝ) ≤ (23937459 / 5000000) := by
    apply log_nat_upper_certificate 120 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 120 (by norm_num)
    (10954451 / 1000000) (2738613 / 250000) (23937459 / 5000000) (9509 / 12500000) (364197 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_121 :
    ((75131 / 100000000) : ℝ) ≤ (121 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 121 ≤ (72063 / 20000000) := by
  have hlog : Real.log ((121 : ℕ) : ℝ) ≤ (23978953 / 5000000) := by
    apply log_nat_upper_certificate 121 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 121 (by norm_num)
    11 (11000001 / 1000000) (23978953 / 5000000) (75131 / 100000000) (72063 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_122 :
    ((74209 / 100000000) : ℝ) ≤ (122 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 122 ≤ (71301 / 20000000) := by
  have hlog : Real.log ((122 : ℕ) : ℝ) ≤ (48040211 / 10000000) := by
    apply log_nat_upper_certificate 122 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 122 (by norm_num)
    (11045361 / 1000000) (5522681 / 500000) (48040211 / 10000000) (74209 / 100000000) (71301 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_123 :
    ((36653 / 50000000) : ℝ) ≤ (123 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 123 ≤ (70553 / 20000000) := by
  have hlog : Real.log ((123 : ℕ) : ℝ) ≤ (12030461 / 2500000) := by
    apply log_nat_upper_certificate 123 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 123 (by norm_num)
    (1386317 / 125000) (11090537 / 1000000) (12030461 / 2500000) (36653 / 50000000) (70553 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_124 :
    ((72421 / 100000000) : ℝ) ≤ (124 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 124 ≤ (349093 / 100000000) := by
  have hlog : Real.log ((124 : ℕ) : ℝ) ≤ (753169 / 156250) := by
    apply log_nat_upper_certificate 124 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 124 (by norm_num)
    (1391941 / 125000) (11135529 / 1000000) (753169 / 156250) (72421 / 100000000) (349093 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_125 :
    ((35777 / 50000000) : ℝ) ≤ (125 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 125 ≤ (345487 / 100000000) := by
  have hlog : Real.log ((125 : ℕ) : ℝ) ≤ (24141569 / 5000000) := by
    apply log_nat_upper_certificate 125 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 125 (by norm_num)
    (11180339 / 1000000) (559017 / 50000) (24141569 / 5000000) (35777 / 50000000) (345487 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_126 :
    ((4419 / 6250000) : ℝ) ≤ (126 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 126 ≤ (68389 / 20000000) := by
  have hlog : Real.log ((126 : ℕ) : ℝ) ≤ (2418141 / 500000) := by
    apply log_nat_upper_certificate 126 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 126 (by norm_num)
    (2806243 / 250000) (11224973 / 1000000) (2418141 / 500000) (4419 / 6250000) (68389 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_127 :
    ((6987 / 10000000) : ℝ) ≤ (127 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 127 ≤ (338467 / 100000000) := by
  have hlog : Real.log ((127 : ℕ) : ℝ) ≤ (3027617 / 625000) := by
    apply log_nat_upper_certificate 127 6 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 127 (by norm_num)
    (11269427 / 1000000) (2817357 / 250000) (3027617 / 625000) (6987 / 10000000) (338467 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_128 :
    ((69053 / 100000000) : ℝ) ≤ (128 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 128 ≤ (6701 / 2000000) := by
  have hlog : Real.log ((128 : ℕ) : ℝ) ≤ (48520303 / 10000000) := by
    apply log_nat_upper_certificate 128 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 128 (by norm_num)
    (2828427 / 250000) (11313709 / 1000000) (48520303 / 10000000) (69053 / 100000000) (6701 / 2000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_129 :
    ((17063 / 25000000) : ℝ) ≤ (129 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 129 ≤ (82923 / 25000000) := by
  have hlog : Real.log ((129 : ℕ) : ℝ) ≤ (77757 / 16000) := by
    apply log_nat_upper_certificate 129 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 129 (by norm_num)
    (1419727 / 125000) (11357817 / 1000000) (77757 / 16000) (17063 / 25000000) (82923 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_130 :
    ((13493 / 20000000) : ℝ) ≤ (130 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 130 ≤ (164197 / 50000000) := by
  have hlog : Real.log ((130 : ℕ) : ℝ) ≤ (9735069 / 2000000) := by
    apply log_nat_upper_certificate 130 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 130 (by norm_num)
    (5700877 / 500000) (2280351 / 200000) (9735069 / 2000000) (13493 / 20000000) (164197 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_131 :
    ((33347 / 50000000) : ℝ) ≤ (131 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 131 ≤ (10161 / 3125000) := by
  have hlog : Real.log ((131 : ℕ) : ℝ) ≤ (24375987 / 5000000) := by
    apply log_nat_upper_certificate 131 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 131 (by norm_num)
    (11445523 / 1000000) (2861381 / 250000) (24375987 / 5000000) (33347 / 50000000) (10161 / 3125000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_132 :
    ((32969 / 50000000) : ℝ) ≤ (132 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 132 ≤ (64393 / 20000000) := by
  have hlog : Real.log ((132 : ℕ) : ℝ) ≤ (2441401 / 500000) := by
    apply log_nat_upper_certificate 132 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 132 (by norm_num)
    (91913 / 8000) (5744563 / 500000) (2441401 / 500000) (32969 / 50000000) (64393 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem ThreeHalvesBlock03_lower :
    ((2575251 / 100000000) : ℝ) ≤ (∑ n ∈ Finset.Ico (101 : ℕ) 133, (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  have h101 := threeHalves_row_101.1
  have h102 := threeHalves_row_102.1
  have h103 := threeHalves_row_103.1
  have h104 := threeHalves_row_104.1
  have h105 := threeHalves_row_105.1
  have h106 := threeHalves_row_106.1
  have h107 := threeHalves_row_107.1
  have h108 := threeHalves_row_108.1
  have h109 := threeHalves_row_109.1
  have h110 := threeHalves_row_110.1
  have h111 := threeHalves_row_111.1
  have h112 := threeHalves_row_112.1
  have h113 := threeHalves_row_113.1
  have h114 := threeHalves_row_114.1
  have h115 := threeHalves_row_115.1
  have h116 := threeHalves_row_116.1
  have h117 := threeHalves_row_117.1
  have h118 := threeHalves_row_118.1
  have h119 := threeHalves_row_119.1
  have h120 := threeHalves_row_120.1
  have h121 := threeHalves_row_121.1
  have h122 := threeHalves_row_122.1
  have h123 := threeHalves_row_123.1
  have h124 := threeHalves_row_124.1
  have h125 := threeHalves_row_125.1
  have h126 := threeHalves_row_126.1
  have h127 := threeHalves_row_127.1
  have h128 := threeHalves_row_128.1
  have h129 := threeHalves_row_129.1
  have h130 := threeHalves_row_130.1
  have h131 := threeHalves_row_131.1
  have h132 := threeHalves_row_132.1
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127, h128, h129, h130, h131, h132]

#print axioms ThreeHalvesBlock03_lower

theorem ThreeHalvesBlock03_upper :
    (∑ n ∈ Finset.Ico (101 : ℕ) 133, logPowerTerm n) ≤ ((12220173 / 100000000) : ℝ) := by
  have h101 := threeHalves_row_101.2
  have h102 := threeHalves_row_102.2
  have h103 := threeHalves_row_103.2
  have h104 := threeHalves_row_104.2
  have h105 := threeHalves_row_105.2
  have h106 := threeHalves_row_106.2
  have h107 := threeHalves_row_107.2
  have h108 := threeHalves_row_108.2
  have h109 := threeHalves_row_109.2
  have h110 := threeHalves_row_110.2
  have h111 := threeHalves_row_111.2
  have h112 := threeHalves_row_112.2
  have h113 := threeHalves_row_113.2
  have h114 := threeHalves_row_114.2
  have h115 := threeHalves_row_115.2
  have h116 := threeHalves_row_116.2
  have h117 := threeHalves_row_117.2
  have h118 := threeHalves_row_118.2
  have h119 := threeHalves_row_119.2
  have h120 := threeHalves_row_120.2
  have h121 := threeHalves_row_121.2
  have h122 := threeHalves_row_122.2
  have h123 := threeHalves_row_123.2
  have h124 := threeHalves_row_124.2
  have h125 := threeHalves_row_125.2
  have h126 := threeHalves_row_126.2
  have h127 := threeHalves_row_127.2
  have h128 := threeHalves_row_128.2
  have h129 := threeHalves_row_129.2
  have h130 := threeHalves_row_130.2
  have h131 := threeHalves_row_131.2
  have h132 := threeHalves_row_132.2
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127, h128, h129, h130, h131, h132]

#print axioms ThreeHalvesBlock03_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
