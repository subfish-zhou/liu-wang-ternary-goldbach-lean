import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesPilot

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem threeHalves_row_133 :
    ((16299 / 25000000) : ℝ) ≤ (133 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 133 ≤ (318833 / 100000000) := by
  have hlog : Real.log ((133 : ℕ) : ℝ) ≤ (12225873 / 2500000) := by
    apply log_nat_upper_certificate 133 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 133 (by norm_num)
    (5766281 / 500000) (11532563 / 1000000) (12225873 / 2500000) (16299 / 25000000) (318833 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_134 :
    ((64467 / 100000000) : ℝ) ≤ (134 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 134 ≤ (315753 / 100000000) := by
  have hlog : Real.log ((134 : ℕ) : ℝ) ≤ (48978399 / 10000000) := by
    apply log_nat_upper_certificate 134 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 134 (by norm_num)
    (2893959 / 250000) (11575837 / 1000000) (48978399 / 10000000) (64467 / 100000000) (315753 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_135 :
    ((7969 / 12500000) : ℝ) ≤ (135 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 135 ≤ (156363 / 50000000) := by
  have hlog : Real.log ((135 : ℕ) : ℝ) ≤ (12263187 / 2500000) := by
    apply log_nat_upper_certificate 135 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 135 (by norm_num)
    (232379 / 20000) (11618951 / 1000000) (12263187 / 2500000) (7969 / 12500000) (156363 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_136 :
    ((1261 / 2000000) : ℝ) ≤ (136 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 136 ≤ (77437 / 25000000) := by
  have hlog : Real.log ((136 : ℕ) : ℝ) ≤ (49126549 / 10000000) := by
    apply log_nat_upper_certificate 136 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 136 (by norm_num)
    (11661903 / 1000000) (728869 / 62500) (49126549 / 10000000) (1261 / 2000000) (77437 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_137 :
    ((62361 / 100000000) : ℝ) ≤ (137 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 137 ≤ (15341 / 5000000) := by
  have hlog : Real.log ((137 : ℕ) : ℝ) ≤ (4919981 / 1000000) := by
    apply log_nat_upper_certificate 137 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 137 (by norm_num)
    (11704699 / 1000000) (117047 / 10000) (4919981 / 1000000) (62361 / 100000000) (15341 / 5000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_138 :
    ((12337 / 20000000) : ℝ) ≤ (138 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 138 ≤ (303939 / 100000000) := by
  have hlog : Real.log ((138 : ℕ) : ℝ) ≤ (49272537 / 10000000) := by
    apply log_nat_upper_certificate 138 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 138 (by norm_num)
    (587367 / 50000) (11747341 / 1000000) (49272537 / 10000000) (12337 / 20000000) (303939 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_139 :
    ((3051 / 5000000) : ℝ) ≤ (139 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 139 ≤ (150553 / 50000000) := by
  have hlog : Real.log ((139 : ℕ) : ℝ) ≤ (2467237 / 500000) := by
    apply log_nat_upper_certificate 139 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 139 (by norm_num)
    (5894913 / 500000) (11789827 / 1000000) (2467237 / 500000) (3051 / 5000000) (150553 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_140 :
    ((3773 / 6250000) : ℝ) ≤ (140 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 140 ≤ (149159 / 50000000) := by
  have hlog : Real.log ((140 : ℕ) : ℝ) ≤ (1976657 / 400000) := by
    apply log_nat_upper_certificate 140 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 140 (by norm_num)
    (11832159 / 1000000) (73951 / 6250) (1976657 / 400000) (3773 / 6250000) (149159 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_141 :
    ((59727 / 100000000) : ℝ) ≤ (141 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 141 ≤ (36947 / 12500000) := by
  have hlog : Real.log ((141 : ℕ) : ℝ) ≤ (49487599 / 10000000) := by
    apply log_nat_upper_certificate 141 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 141 (by norm_num)
    (5937171 / 500000) (11874343 / 1000000) (49487599 / 10000000) (59727 / 100000000) (36947 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_142 :
    ((59097 / 100000000) : ℝ) ≤ (142 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 142 ≤ (73219 / 25000000) := by
  have hlog : Real.log ((142 : ℕ) : ℝ) ≤ (49558271 / 10000000) := by
    apply log_nat_upper_certificate 142 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 142 (by norm_num)
    (95331 / 8000) (1489547 / 125000) (49558271 / 10000000) (59097 / 100000000) (73219 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_143 :
    ((29239 / 50000000) : ℝ) ≤ (143 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 143 ≤ (14511 / 5000000) := by
  have hlog : Real.log ((143 : ℕ) : ℝ) ≤ (49628447 / 10000000) := by
    apply log_nat_upper_certificate 143 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 143 (by norm_num)
    (597913 / 50000) (11958261 / 1000000) (49628447 / 10000000) (29239 / 50000000) (14511 / 5000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_144 :
    ((5787 / 10000000) : ℝ) ≤ (144 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 144 ≤ (57521 / 20000000) := by
  have hlog : Real.log ((144 : ℕ) : ℝ) ≤ (24849067 / 5000000) := by
    apply log_nat_upper_certificate 144 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 144 (by norm_num)
    12 (12000001 / 1000000) (24849067 / 5000000) (5787 / 10000000) (57521 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_145 :
    ((7159 / 12500000) : ℝ) ≤ (145 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 145 ≤ (35629 / 12500000) := by
  have hlog : Real.log ((145 : ℕ) : ℝ) ≤ (24883669 / 5000000) := by
    apply log_nat_upper_certificate 145 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 145 (by norm_num)
    (6020797 / 500000) (2408319 / 200000) (24883669 / 5000000) (7159 / 12500000) (35629 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_146 :
    ((11337 / 20000000) : ℝ) ≤ (146 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 146 ≤ (141249 / 50000000) := by
  have hlog : Real.log ((146 : ℕ) : ℝ) ≤ (49836067 / 10000000) := by
    apply log_nat_upper_certificate 146 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 146 (by norm_num)
    (2416609 / 200000) (6041523 / 500000) (49836067 / 10000000) (11337 / 20000000) (141249 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_147 :
    ((56107 / 100000000) : ℝ) ≤ (147 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 147 ≤ (280003 / 100000000) := by
  have hlog : Real.log ((147 : ℕ) : ℝ) ≤ (24952163 / 5000000) := by
    apply log_nat_upper_certificate 147 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 147 (by norm_num)
    (2424871 / 200000) (3031089 / 250000) (24952163 / 5000000) (56107 / 100000000) (280003 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_148 :
    ((2777 / 5000000) : ℝ) ≤ (148 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 148 ≤ (277547 / 100000000) := by
  have hlog : Real.log ((148 : ℕ) : ℝ) ≤ (49972123 / 10000000) := by
    apply log_nat_upper_certificate 148 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 148 (by norm_num)
    (486621 / 40000) (6082763 / 500000) (49972123 / 10000000) (2777 / 5000000) (277547 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_149 :
    ((27491 / 50000000) : ℝ) ≤ (149 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 149 ≤ (34391 / 12500000) := by
  have hlog : Real.log ((149 : ℕ) : ℝ) ≤ (6254933 / 1250000) := by
    apply log_nat_upper_certificate 149 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 149 (by norm_num)
    (2441311 / 200000) (3051639 / 250000) (6254933 / 1250000) (27491 / 50000000) (34391 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_150 :
    ((54433 / 100000000) : ℝ) ≤ (150 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 150 ≤ (54549 / 20000000) := by
  have hlog : Real.log ((150 : ℕ) : ℝ) ≤ (50106353 / 10000000) := by
    apply log_nat_upper_certificate 150 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 150 (by norm_num)
    (1530931 / 125000) (12247449 / 1000000) (50106353 / 10000000) (54433 / 100000000) (54549 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_151 :
    ((53893 / 100000000) : ℝ) ≤ (151 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 151 ≤ (135199 / 50000000) := by
  have hlog : Real.log ((151 : ℕ) : ℝ) ≤ (50172799 / 10000000) := by
    apply log_nat_upper_certificate 151 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 151 (by norm_num)
    (2457641 / 200000) (6144103 / 500000) (50172799 / 10000000) (53893 / 100000000) (135199 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_152 :
    ((26681 / 50000000) : ℝ) ≤ (152 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 152 ≤ (134043 / 50000000) := by
  have hlog : Real.log ((152 : ℕ) : ℝ) ≤ (25119403 / 5000000) := by
    apply log_nat_upper_certificate 152 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 152 (by norm_num)
    (3082207 / 250000) (12328829 / 1000000) (25119403 / 5000000) (26681 / 50000000) (134043 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_153 :
    ((1321 / 2500000) : ℝ) ≤ (153 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 153 ≤ (265809 / 100000000) := by
  have hlog : Real.log ((153 : ℕ) : ℝ) ≤ (2515219 / 500000) := by
    apply log_nat_upper_certificate 153 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 153 (by norm_num)
    (3092329 / 250000) (12369317 / 1000000) (2515219 / 500000) (1321 / 2500000) (265809 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_154 :
    ((26163 / 50000000) : ℝ) ≤ (154 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 154 ≤ (52713 / 20000000) := by
  have hlog : Real.log ((154 : ℕ) : ℝ) ≤ (50369527 / 10000000) := by
    apply log_nat_upper_certificate 154 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 154 (by norm_num)
    (12409673 / 1000000) (6204837 / 500000) (50369527 / 10000000) (26163 / 50000000) (52713 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_155 :
    ((2591 / 5000000) : ℝ) ≤ (155 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 155 ≤ (130677 / 50000000) := by
  have hlog : Real.log ((155 : ℕ) : ℝ) ≤ (12608563 / 2500000) := by
    apply log_nat_upper_certificate 155 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 155 (by norm_num)
    (12449899 / 1000000) (124499 / 10000) (12608563 / 2500000) (2591 / 5000000) (130677 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_156 :
    ((51323 / 100000000) : ℝ) ≤ (156 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 156 ≤ (10367 / 4000000) := by
  have hlog : Real.log ((156 : ℕ) : ℝ) ≤ (50498561 / 10000000) := by
    apply log_nat_upper_certificate 156 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 156 (by norm_num)
    (2497999 / 200000) (3122499 / 250000) (50498561 / 10000000) (51323 / 100000000) (10367 / 4000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_157 :
    ((50833 / 100000000) : ℝ) ≤ (157 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 157 ≤ (257027 / 100000000) := by
  have hlog : Real.log ((157 : ℕ) : ℝ) ≤ (50562459 / 10000000) := by
    apply log_nat_upper_certificate 157 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 157 (by norm_num)
    (3132491 / 250000) (2505993 / 200000) (50562459 / 10000000) (50833 / 100000000) (257027 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_158 :
    ((50351 / 100000000) : ℝ) ≤ (158 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 158 ≤ (254911 / 100000000) := by
  have hlog : Real.log ((158 : ℕ) : ℝ) ≤ (50625951 / 10000000) := by
    apply log_nat_upper_certificate 158 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 158 (by norm_num)
    (2513961 / 200000) (6284903 / 500000) (50625951 / 10000000) (50351 / 100000000) (254911 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_159 :
    ((49877 / 100000000) : ℝ) ≤ (159 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 159 ≤ (10113 / 4000000) := by
  have hlog : Real.log ((159 : ℕ) : ℝ) ≤ (50689043 / 10000000) := by
    apply log_nat_upper_certificate 159 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 159 (by norm_num)
    (157619 / 12500) (12609521 / 1000000) (50689043 / 10000000) (49877 / 100000000) (10113 / 4000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_160 :
    ((4941 / 10000000) : ℝ) ≤ (160 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 160 ≤ (15673 / 6250000) := by
  have hlog : Real.log ((160 : ℕ) : ℝ) ≤ (50751739 / 10000000) := by
    apply log_nat_upper_certificate 160 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 160 (by norm_num)
    (1264911 / 100000) (12649111 / 1000000) (50751739 / 10000000) (4941 / 10000000) (15673 / 6250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_161 :
    ((979 / 2000000) : ℝ) ≤ (161 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 161 ≤ (12437 / 5000000) := by
  have hlog : Real.log ((161 : ℕ) : ℝ) ≤ (12703511 / 2500000) := by
    apply log_nat_upper_certificate 161 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 161 (by norm_num)
    (12688577 / 1000000) (6344289 / 500000) (12703511 / 2500000) (979 / 2000000) (12437 / 5000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_162 :
    ((24249 / 50000000) : ℝ) ≤ (162 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 162 ≤ (246741 / 100000000) := by
  have hlog : Real.log ((162 : ℕ) : ℝ) ≤ (12718991 / 2500000) := by
    apply log_nat_upper_certificate 162 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 162 (by norm_num)
    (6363961 / 500000) (12727923 / 1000000) (12718991 / 2500000) (24249 / 50000000) (246741 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_163 :
    ((12013 / 25000000) : ℝ) ≤ (163 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 163 ≤ (244769 / 100000000) := by
  have hlog : Real.log ((163 : ℕ) : ℝ) ≤ (50937503 / 10000000) := by
    apply log_nat_upper_certificate 163 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 163 (by norm_num)
    (2553429 / 200000) (6383573 / 500000) (50937503 / 10000000) (12013 / 25000000) (244769 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_164 :
    ((47613 / 100000000) : ℝ) ≤ (164 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 164 ≤ (9713 / 4000000) := by
  have hlog : Real.log ((164 : ℕ) : ℝ) ≤ (10199733 / 2000000) := by
    apply log_nat_upper_certificate 164 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 164 (by norm_num)
    (1600781 / 125000) (12806249 / 1000000) (10199733 / 2000000) (47613 / 100000000) (9713 / 4000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem ThreeHalvesBlock04_lower :
    ((890619 / 50000000) : ℝ) ≤ (∑ n ∈ Finset.Ico (133 : ℕ) 165, (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  have h133 := threeHalves_row_133.1
  have h134 := threeHalves_row_134.1
  have h135 := threeHalves_row_135.1
  have h136 := threeHalves_row_136.1
  have h137 := threeHalves_row_137.1
  have h138 := threeHalves_row_138.1
  have h139 := threeHalves_row_139.1
  have h140 := threeHalves_row_140.1
  have h141 := threeHalves_row_141.1
  have h142 := threeHalves_row_142.1
  have h143 := threeHalves_row_143.1
  have h144 := threeHalves_row_144.1
  have h145 := threeHalves_row_145.1
  have h146 := threeHalves_row_146.1
  have h147 := threeHalves_row_147.1
  have h148 := threeHalves_row_148.1
  have h149 := threeHalves_row_149.1
  have h150 := threeHalves_row_150.1
  have h151 := threeHalves_row_151.1
  have h152 := threeHalves_row_152.1
  have h153 := threeHalves_row_153.1
  have h154 := threeHalves_row_154.1
  have h155 := threeHalves_row_155.1
  have h156 := threeHalves_row_156.1
  have h157 := threeHalves_row_157.1
  have h158 := threeHalves_row_158.1
  have h159 := threeHalves_row_159.1
  have h160 := threeHalves_row_160.1
  have h161 := threeHalves_row_161.1
  have h162 := threeHalves_row_162.1
  have h163 := threeHalves_row_163.1
  have h164 := threeHalves_row_164.1
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h133, h134, h135, h136, h137, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h151, h152, h153, h154, h155, h156, h157, h158, h159, h160, h161, h162, h163, h164]

#print axioms ThreeHalvesBlock04_lower

theorem ThreeHalvesBlock04_upper :
    (∑ n ∈ Finset.Ico (133 : ℕ) 165, logPowerTerm n) ≤ ((4446733 / 50000000) : ℝ) := by
  have h133 := threeHalves_row_133.2
  have h134 := threeHalves_row_134.2
  have h135 := threeHalves_row_135.2
  have h136 := threeHalves_row_136.2
  have h137 := threeHalves_row_137.2
  have h138 := threeHalves_row_138.2
  have h139 := threeHalves_row_139.2
  have h140 := threeHalves_row_140.2
  have h141 := threeHalves_row_141.2
  have h142 := threeHalves_row_142.2
  have h143 := threeHalves_row_143.2
  have h144 := threeHalves_row_144.2
  have h145 := threeHalves_row_145.2
  have h146 := threeHalves_row_146.2
  have h147 := threeHalves_row_147.2
  have h148 := threeHalves_row_148.2
  have h149 := threeHalves_row_149.2
  have h150 := threeHalves_row_150.2
  have h151 := threeHalves_row_151.2
  have h152 := threeHalves_row_152.2
  have h153 := threeHalves_row_153.2
  have h154 := threeHalves_row_154.2
  have h155 := threeHalves_row_155.2
  have h156 := threeHalves_row_156.2
  have h157 := threeHalves_row_157.2
  have h158 := threeHalves_row_158.2
  have h159 := threeHalves_row_159.2
  have h160 := threeHalves_row_160.2
  have h161 := threeHalves_row_161.2
  have h162 := threeHalves_row_162.2
  have h163 := threeHalves_row_163.2
  have h164 := threeHalves_row_164.2
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h133, h134, h135, h136, h137, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h151, h152, h153, h154, h155, h156, h157, h158, h159, h160, h161, h162, h163, h164]

#print axioms ThreeHalvesBlock04_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
