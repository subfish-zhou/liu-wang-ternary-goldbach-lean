import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesPilot

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem threeHalves_row_165 :
    ((47181 / 100000000) : ℝ) ≤ (165 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 165 ≤ (60227 / 25000000) := by
  have hlog : Real.log ((165 : ℕ) : ℝ) ≤ (10211891 / 2000000) := by
    apply log_nat_upper_certificate 165 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 165 (by norm_num)
    (802827 / 62500) (12845233 / 1000000) (10211891 / 2000000) (47181 / 100000000) (60227 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_166 :
    ((11689 / 25000000) : ℝ) ≤ (166 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 166 ≤ (239017 / 100000000) := by
  have hlog : Real.log ((166 : ℕ) : ℝ) ≤ (25559939 / 5000000) := by
    apply log_nat_upper_certificate 166 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 166 (by norm_num)
    (6442049 / 500000) (12884099 / 1000000) (25559939 / 5000000) (11689 / 25000000) (239017 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_167 :
    ((181 / 390625) : ℝ) ≤ (167 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 167 ≤ (7411 / 3125000) := by
  have hlog : Real.log ((167 : ℕ) : ℝ) ≤ (51179939 / 10000000) := by
    apply log_nat_upper_certificate 167 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 167 (by norm_num)
    (12922847 / 1000000) (403839 / 31250) (51179939 / 10000000) (181 / 390625) (7411 / 3125000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_168 :
    ((45923 / 100000000) : ℝ) ≤ (168 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 168 ≤ (235311 / 100000000) := by
  have hlog : Real.log ((168 : ℕ) : ℝ) ≤ (1280991 / 250000) := by
    apply log_nat_upper_certificate 168 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 168 (by norm_num)
    (12961481 / 1000000) (6480741 / 500000) (1280991 / 250000) (45923 / 100000000) (235311 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_169 :
    ((11379 / 25000000) : ℝ) ≤ (169 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 169 ≤ (29187 / 12500000) := by
  have hlog : Real.log ((169 : ℕ) : ℝ) ≤ (12824747 / 2500000) := by
    apply log_nat_upper_certificate 169 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 169 (by norm_num)
    13 (13000001 / 1000000) (12824747 / 2500000) (11379 / 25000000) (29187 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_170 :
    ((9023 / 20000000) : ℝ) ≤ (170 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 170 ≤ (46341 / 20000000) := by
  have hlog : Real.log ((170 : ℕ) : ℝ) ≤ (10271597 / 2000000) := by
    apply log_nat_upper_certificate 170 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 170 (by norm_num)
    (3259601 / 250000) (2607681 / 200000) (10271597 / 2000000) (9023 / 20000000) (46341 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_171 :
    ((559 / 1250000) : ℝ) ≤ (171 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 171 ≤ (114969 / 50000000) := by
  have hlog : Real.log ((171 : ℕ) : ℝ) ≤ (12854159 / 2500000) := by
    apply log_nat_upper_certificate 171 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 171 (by norm_num)
    (1634587 / 125000) (13076697 / 1000000) (12854159 / 2500000) (559 / 1250000) (114969 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_172 :
    ((4433 / 10000000) : ℝ) ≤ (172 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 172 ≤ (114097 / 50000000) := by
  have hlog : Real.log ((172 : ℕ) : ℝ) ≤ (10294989 / 2000000) := by
    apply log_nat_upper_certificate 172 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 172 (by norm_num)
    (13114877 / 1000000) (6557439 / 500000) (10294989 / 2000000) (4433 / 10000000) (114097 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_173 :
    ((43947 / 100000000) : ℝ) ≤ (173 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 173 ≤ (226473 / 100000000) := by
  have hlog : Real.log ((173 : ℕ) : ℝ) ≤ (12883229 / 2500000) := by
    apply log_nat_upper_certificate 173 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 173 (by norm_num)
    (6576473 / 500000) (13152947 / 1000000) (12883229 / 2500000) (43947 / 100000000) (226473 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_174 :
    ((2723 / 6250000) : ℝ) ≤ (174 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 174 ≤ (8991 / 4000000) := by
  have hlog : Real.log ((174 : ℕ) : ℝ) ≤ (25795277 / 5000000) := by
    apply log_nat_upper_certificate 174 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 174 (by norm_num)
    (2638181 / 200000) (6595453 / 500000) (25795277 / 5000000) (2723 / 6250000) (8991 / 4000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_175 :
    ((8639 / 20000000) : ℝ) ≤ (175 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 175 ≤ (111549 / 50000000) := by
  have hlog : Real.log ((175 : ℕ) : ℝ) ≤ (2582393 / 500000) := by
    apply log_nat_upper_certificate 175 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 175 (by norm_num)
    (3307189 / 250000) (13228757 / 1000000) (2582393 / 500000) (8639 / 20000000) (111549 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_176 :
    ((10707 / 25000000) : ℝ) ≤ (176 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 176 ≤ (55361 / 25000000) := by
  have hlog : Real.log ((176 : ℕ) : ℝ) ≤ (1292621 / 250000) := by
    apply log_nat_upper_certificate 176 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 176 (by norm_num)
    (13266499 / 1000000) (26533 / 2000) (1292621 / 250000) (10707 / 25000000) (55361 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_177 :
    ((8493 / 20000000) : ℝ) ≤ (177 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 177 ≤ (21981 / 10000000) := by
  have hlog : Real.log ((177 : ℕ) : ℝ) ≤ (25880749 / 5000000) := by
    apply log_nat_upper_certificate 177 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 177 (by norm_num)
    (6652067 / 500000) (2660827 / 200000) (25880749 / 5000000) (8493 / 20000000) (21981 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_178 :
    ((10527 / 25000000) : ℝ) ≤ (178 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 178 ≤ (109099 / 50000000) := by
  have hlog : Real.log ((178 : ℕ) : ℝ) ≤ (12954459 / 2500000) := by
    apply log_nat_upper_certificate 178 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 178 (by norm_num)
    (416927 / 31250) (2668333 / 200000) (12954459 / 2500000) (10527 / 25000000) (109099 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_179 :
    ((10439 / 25000000) : ℝ) ≤ (179 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 179 ≤ (108303 / 50000000) := by
  have hlog : Real.log ((179 : ℕ) : ℝ) ≤ (51873859 / 10000000) := by
    apply log_nat_upper_certificate 179 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 179 (by norm_num)
    (836193 / 62500) (13379089 / 1000000) (51873859 / 10000000) (10439 / 25000000) (108303 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_180 :
    ((647 / 1562500) : ℝ) ≤ (180 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 180 ≤ (107517 / 50000000) := by
  have hlog : Real.log ((180 : ℕ) : ℝ) ≤ (51929569 / 10000000) := by
    apply log_nat_upper_certificate 180 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 180 (by norm_num)
    (13416407 / 1000000) (1677051 / 125000) (51929569 / 10000000) (647 / 1562500) (107517 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_181 :
    ((8213 / 20000000) : ℝ) ≤ (181 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 181 ≤ (106741 / 50000000) := by
  have hlog : Real.log ((181 : ℕ) : ℝ) ≤ (51984971 / 10000000) := by
    apply log_nat_upper_certificate 181 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 181 (by norm_num)
    (1681703 / 125000) (107629 / 8000) (51984971 / 10000000) (8213 / 20000000) (106741 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_182 :
    ((40727 / 100000000) : ℝ) ≤ (182 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 182 ≤ (211949 / 100000000) := by
  have hlog : Real.log ((182 : ℕ) : ℝ) ≤ (52040067 / 10000000) := by
    apply log_nat_upper_certificate 182 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 182 (by norm_num)
    (13490737 / 1000000) (6745369 / 500000) (52040067 / 10000000) (40727 / 100000000) (211949 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_183 :
    ((20197 / 50000000) : ℝ) ≤ (183 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 183 ≤ (52609 / 25000000) := by
  have hlog : Real.log ((183 : ℕ) : ℝ) ≤ (26047431 / 5000000) := by
    apply log_nat_upper_certificate 183 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 183 (by norm_num)
    (13527749 / 1000000) (54111 / 4000) (26047431 / 5000000) (20197 / 50000000) (52609 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_184 :
    ((8013 / 20000000) : ℝ) ≤ (184 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 184 ≤ (208941 / 100000000) := by
  have hlog : Real.log ((184 : ℕ) : ℝ) ≤ (26074679 / 5000000) := by
    apply log_nat_upper_certificate 184 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 184 (by norm_num)
    (13564659 / 1000000) (678233 / 50000) (26074679 / 5000000) (8013 / 20000000) (208941 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_185 :
    ((39741 / 100000000) : ℝ) ≤ (185 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 185 ≤ (25933 / 12500000) := by
  have hlog : Real.log ((185 : ℕ) : ℝ) ≤ (52203559 / 10000000) := by
    apply log_nat_upper_certificate 185 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 185 (by norm_num)
    (1360147 / 100000) (13601471 / 1000000) (52203559 / 10000000) (39741 / 100000000) (25933 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_186 :
    ((39421 / 100000000) : ℝ) ≤ (186 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 186 ≤ (103003 / 50000000) := by
  have hlog : Real.log ((186 : ℕ) : ℝ) ≤ (52257467 / 10000000) := by
    apply log_nat_upper_certificate 186 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 186 (by norm_num)
    (13638181 / 1000000) (6819091 / 500000) (52257467 / 10000000) (39421 / 100000000) (103003 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_187 :
    ((7821 / 20000000) : ℝ) ≤ (187 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 187 ≤ (102283 / 50000000) := by
  have hlog : Real.log ((187 : ℕ) : ℝ) ≤ (52311087 / 10000000) := by
    apply log_nat_upper_certificate 187 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 187 (by norm_num)
    (6837397 / 500000) (2734959 / 200000) (52311087 / 10000000) (7821 / 20000000) (102283 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_188 :
    ((38793 / 100000000) : ℝ) ≤ (188 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 188 ≤ (101571 / 50000000) := by
  have hlog : Real.log ((188 : ℕ) : ℝ) ≤ (2618221 / 500000) := by
    apply log_nat_upper_certificate 188 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 188 (by norm_num)
    (13711309 / 1000000) (1371131 / 100000) (2618221 / 500000) (38793 / 100000000) (101571 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_189 :
    ((19243 / 50000000) : ℝ) ≤ (189 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 189 ≤ (25217 / 12500000) := by
  have hlog : Real.log ((189 : ℕ) : ℝ) ≤ (52417471 / 10000000) := by
    apply log_nat_upper_certificate 189 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 189 (by norm_num)
    (13747727 / 1000000) (859233 / 62500) (52417471 / 10000000) (19243 / 50000000) (25217 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_190 :
    ((19091 / 50000000) : ℝ) ≤ (190 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 190 ≤ (200347 / 100000000) := by
  have hlog : Real.log ((190 : ℕ) : ℝ) ≤ (52470241 / 10000000) := by
    apply log_nat_upper_certificate 190 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 190 (by norm_num)
    (861503 / 62500) (13784049 / 1000000) (52470241 / 10000000) (19091 / 50000000) (200347 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_191 :
    ((37883 / 100000000) : ℝ) ≤ (191 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 191 ≤ (7959 / 4000000) := by
  have hlog : Real.log ((191 : ℕ) : ℝ) ≤ (10504547 / 2000000) := by
    apply log_nat_upper_certificate 191 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 191 (by norm_num)
    (6910137 / 500000) (552811 / 40000) (10504547 / 2000000) (37883 / 100000000) (7959 / 4000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_192 :
    ((37587 / 100000000) : ℝ) ≤ (192 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 192 ≤ (197619 / 100000000) := by
  have hlog : Real.log ((192 : ℕ) : ℝ) ≤ (26287477 / 5000000) := by
    apply log_nat_upper_certificate 192 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 192 (by norm_num)
    (6928203 / 500000) (13856407 / 1000000) (26287477 / 5000000) (37587 / 100000000) (197619 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_193 :
    ((2331 / 6250000) : ℝ) ≤ (193 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 193 ≤ (196279 / 100000000) := by
  have hlog : Real.log ((193 : ℕ) : ℝ) ≤ (26313451 / 5000000) := by
    apply log_nat_upper_certificate 193 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 193 (by norm_num)
    (13892443 / 1000000) (3473111 / 250000) (26313451 / 5000000) (2331 / 6250000) (196279 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_194 :
    ((2313 / 6250000) : ℝ) ≤ (194 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 194 ≤ (97477 / 50000000) := by
  have hlog : Real.log ((194 : ℕ) : ℝ) ≤ (26339291 / 5000000) := by
    apply log_nat_upper_certificate 194 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 194 (by norm_num)
    (3482097 / 250000) (13928389 / 1000000) (26339291 / 5000000) (2313 / 6250000) (97477 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_195 :
    ((36723 / 100000000) : ℝ) ≤ (195 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 195 ≤ (38729 / 20000000) := by
  have hlog : Real.log ((195 : ℕ) : ℝ) ≤ (13182499 / 2500000) := by
    apply log_nat_upper_certificate 195 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 195 (by norm_num)
    (174553 / 12500) (13964241 / 1000000) (13182499 / 2500000) (36723 / 100000000) (38729 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_196 :
    ((36443 / 100000000) : ℝ) ≤ (196 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 196 ≤ (6011 / 3125000) := by
  have hlog : Real.log ((196 : ℕ) : ℝ) ≤ (52781147 / 10000000) := by
    apply log_nat_upper_certificate 196 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 196 (by norm_num)
    14 (14000001 / 1000000) (52781147 / 10000000) (36443 / 100000000) (6011 / 3125000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem ThreeHalvesBlock05_lower :
    ((1326071 / 100000000) : ℝ) ≤ (∑ n ∈ Finset.Ico (165 : ℕ) 197, (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  have h165 := threeHalves_row_165.1
  have h166 := threeHalves_row_166.1
  have h167 := threeHalves_row_167.1
  have h168 := threeHalves_row_168.1
  have h169 := threeHalves_row_169.1
  have h170 := threeHalves_row_170.1
  have h171 := threeHalves_row_171.1
  have h172 := threeHalves_row_172.1
  have h173 := threeHalves_row_173.1
  have h174 := threeHalves_row_174.1
  have h175 := threeHalves_row_175.1
  have h176 := threeHalves_row_176.1
  have h177 := threeHalves_row_177.1
  have h178 := threeHalves_row_178.1
  have h179 := threeHalves_row_179.1
  have h180 := threeHalves_row_180.1
  have h181 := threeHalves_row_181.1
  have h182 := threeHalves_row_182.1
  have h183 := threeHalves_row_183.1
  have h184 := threeHalves_row_184.1
  have h185 := threeHalves_row_185.1
  have h186 := threeHalves_row_186.1
  have h187 := threeHalves_row_187.1
  have h188 := threeHalves_row_188.1
  have h189 := threeHalves_row_189.1
  have h190 := threeHalves_row_190.1
  have h191 := threeHalves_row_191.1
  have h192 := threeHalves_row_192.1
  have h193 := threeHalves_row_193.1
  have h194 := threeHalves_row_194.1
  have h195 := threeHalves_row_195.1
  have h196 := threeHalves_row_196.1
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h165, h166, h167, h168, h169, h170, h171, h172, h173, h174, h175, h176, h177, h178, h179, h180, h181, h182, h183, h184, h185, h186, h187, h188, h189, h190, h191, h192, h193, h194, h195, h196]

#print axioms ThreeHalvesBlock05_lower

theorem ThreeHalvesBlock05_upper :
    (∑ n ∈ Finset.Ico (165 : ℕ) 197, logPowerTerm n) ≤ ((1720763 / 25000000) : ℝ) := by
  have h165 := threeHalves_row_165.2
  have h166 := threeHalves_row_166.2
  have h167 := threeHalves_row_167.2
  have h168 := threeHalves_row_168.2
  have h169 := threeHalves_row_169.2
  have h170 := threeHalves_row_170.2
  have h171 := threeHalves_row_171.2
  have h172 := threeHalves_row_172.2
  have h173 := threeHalves_row_173.2
  have h174 := threeHalves_row_174.2
  have h175 := threeHalves_row_175.2
  have h176 := threeHalves_row_176.2
  have h177 := threeHalves_row_177.2
  have h178 := threeHalves_row_178.2
  have h179 := threeHalves_row_179.2
  have h180 := threeHalves_row_180.2
  have h181 := threeHalves_row_181.2
  have h182 := threeHalves_row_182.2
  have h183 := threeHalves_row_183.2
  have h184 := threeHalves_row_184.2
  have h185 := threeHalves_row_185.2
  have h186 := threeHalves_row_186.2
  have h187 := threeHalves_row_187.2
  have h188 := threeHalves_row_188.2
  have h189 := threeHalves_row_189.2
  have h190 := threeHalves_row_190.2
  have h191 := threeHalves_row_191.2
  have h192 := threeHalves_row_192.2
  have h193 := threeHalves_row_193.2
  have h194 := threeHalves_row_194.2
  have h195 := threeHalves_row_195.2
  have h196 := threeHalves_row_196.2
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h165, h166, h167, h168, h169, h170, h171, h172, h173, h174, h175, h176, h177, h178, h179, h180, h181, h182, h183, h184, h185, h186, h187, h188, h189, h190, h191, h192, h193, h194, h195, h196]

#print axioms ThreeHalvesBlock05_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
