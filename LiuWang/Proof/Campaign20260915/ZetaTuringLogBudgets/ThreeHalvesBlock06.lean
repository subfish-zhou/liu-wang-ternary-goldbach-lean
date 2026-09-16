import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesPilot

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem threeHalves_row_197 :
    ((18083 / 50000000) : ℝ) ≤ (197 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 197 ≤ (191073 / 100000000) := by
  have hlog : Real.log ((197 : ℕ) : ℝ) ≤ (26416019 / 5000000) := by
    apply log_nat_upper_certificate 197 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 197 (by norm_num)
    (3508917 / 250000) (14035669 / 1000000) (26416019 / 5000000) (18083 / 50000000) (191073 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_198 :
    ((8973 / 25000000) : ℝ) ≤ (198 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 198 ≤ (189809 / 100000000) := by
  have hlog : Real.log ((198 : ℕ) : ℝ) ≤ (52882671 / 10000000) := by
    apply log_nat_upper_certificate 198 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 198 (by norm_num)
    (14071247 / 1000000) (879453 / 62500) (52882671 / 10000000) (8973 / 25000000) (189809 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_199 :
    ((17811 / 50000000) : ℝ) ≤ (199 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 199 ≤ (2357 / 1250000) := by
  have hlog : Real.log ((199 : ℕ) : ℝ) ≤ (52933049 / 10000000) := by
    apply log_nat_upper_certificate 199 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 199 (by norm_num)
    (2821347 / 200000) (881671 / 62500) (52933049 / 10000000) (17811 / 50000000) (2357 / 1250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_200 :
    ((7071 / 20000000) : ℝ) ≤ (200 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 200 ≤ (46831 / 25000000) := by
  have hlog : Real.log ((200 : ℕ) : ℝ) ≤ (26491587 / 5000000) := by
    apply log_nat_upper_certificate 200 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 200 (by norm_num)
    (2828427 / 200000) (1767767 / 125000) (26491587 / 5000000) (7071 / 20000000) (46831 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_201 :
    ((35091 / 100000000) : ℝ) ≤ (201 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 201 ≤ (186103 / 100000000) := by
  have hlog : Real.log ((201 : ℕ) : ℝ) ≤ (1060661 / 200000) := by
    apply log_nat_upper_certificate 201 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 201 (by norm_num)
    (7088723 / 500000) (14177447 / 1000000) (1060661 / 200000) (35091 / 100000000) (186103 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_202 :
    ((34831 / 100000000) : ℝ) ≤ (202 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 202 ≤ (2889 / 1562500) := by
  have hlog : Real.log ((202 : ℕ) : ℝ) ≤ (53082677 / 10000000) := by
    apply log_nat_upper_certificate 202 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 202 (by norm_num)
    (1421267 / 100000) (14212671 / 1000000) (53082677 / 10000000) (34831 / 100000000) (2889 / 1562500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_203 :
    ((17287 / 50000000) : ℝ) ≤ (203 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 203 ≤ (91851 / 50000000) := by
  have hlog : Real.log ((203 : ℕ) : ℝ) ≤ (2656603 / 500000) := by
    apply log_nat_upper_certificate 203 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 203 (by norm_num)
    (7123903 / 500000) (14247807 / 1000000) (2656603 / 500000) (17287 / 50000000) (91851 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_204 :
    ((429 / 1250000) : ℝ) ≤ (204 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 204 ≤ (91261 / 50000000) := by
  have hlog : Real.log ((204 : ℕ) : ℝ) ≤ (132953 / 25000) := by
    apply log_nat_upper_certificate 204 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 204 (by norm_num)
    (1785357 / 125000) (14282857 / 1000000) (132953 / 25000) (429 / 1250000) (91261 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_205 :
    ((34069 / 100000000) : ℝ) ≤ (205 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 205 ≤ (90677 / 50000000) := by
  have hlog : Real.log ((205 : ℕ) : ℝ) ≤ (532301 / 100000) := by
    apply log_nat_upper_certificate 205 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 205 (by norm_num)
    (14317821 / 1000000) (7158911 / 500000) (532301 / 100000) (34069 / 100000000) (90677 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_206 :
    ((33821 / 100000000) : ℝ) ≤ (206 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 206 ≤ (901 / 500000) := by
  have hlog : Real.log ((206 : ℕ) : ℝ) ≤ (26639381 / 5000000) := by
    apply log_nat_upper_certificate 206 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 206 (by norm_num)
    (143527 / 10000) (14352701 / 1000000) (26639381 / 5000000) (33821 / 100000000) (901 / 500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_207 :
    ((33577 / 100000000) : ℝ) ≤ (207 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 207 ≤ (89529 / 50000000) := by
  have hlog : Real.log ((207 : ℕ) : ℝ) ≤ (13331797 / 2500000) := by
    apply log_nat_upper_certificate 207 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 207 (by norm_num)
    (7193747 / 500000) (2877499 / 200000) (13331797 / 2500000) (33577 / 100000000) (89529 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_208 :
    ((6667 / 20000000) : ℝ) ≤ (208 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 208 ≤ (177929 / 100000000) := by
  have hlog : Real.log ((208 : ℕ) : ℝ) ≤ (53375381 / 10000000) := by
    apply log_nat_upper_certificate 208 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 208 (by norm_num)
    (2884441 / 200000) (7211103 / 500000) (53375381 / 10000000) (6667 / 20000000) (177929 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_209 :
    ((4137 / 12500000) : ℝ) ≤ (209 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 209 ≤ (44203 / 25000000) := by
  have hlog : Real.log ((209 : ℕ) : ℝ) ≤ (53423343 / 10000000) := by
    apply log_nat_upper_certificate 209 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 209 (by norm_num)
    (225888 / 15625) (14456833 / 1000000) (53423343 / 10000000) (4137 / 12500000) (44203 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_210 :
    ((1643 / 5000000) : ℝ) ≤ (210 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 210 ≤ (43927 / 25000000) := by
  have hlog : Real.log ((210 : ℕ) : ℝ) ≤ (13367769 / 2500000) := by
    apply log_nat_upper_certificate 210 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 210 (by norm_num)
    (905711 / 62500) (14491377 / 1000000) (13367769 / 2500000) (1643 / 5000000) (43927 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_211 :
    ((16313 / 50000000) : ℝ) ≤ (211 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 211 ≤ (34923 / 20000000) := by
  have hlog : Real.log ((211 : ℕ) : ℝ) ≤ (26759291 / 5000000) := by
    apply log_nat_upper_certificate 211 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 211 (by norm_num)
    (14525839 / 1000000) (181573 / 12500) (26759291 / 5000000) (16313 / 50000000) (34923 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_212 :
    ((8099 / 25000000) : ℝ) ≤ (212 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 212 ≤ (86767 / 50000000) := by
  have hlog : Real.log ((212 : ℕ) : ℝ) ≤ (53565863 / 10000000) := by
    apply log_nat_upper_certificate 212 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 212 (by norm_num)
    (14560219 / 1000000) (728011 / 50000) (53565863 / 10000000) (8099 / 25000000) (86767 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_213 :
    ((4021 / 12500000) : ℝ) ≤ (213 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 213 ≤ (34493 / 20000000) := by
  have hlog : Real.log ((213 : ℕ) : ℝ) ≤ (26806461 / 5000000) := by
    apply log_nat_upper_certificate 213 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 213 (by norm_num)
    (14594519 / 1000000) (364863 / 25000) (26806461 / 5000000) (4021 / 12500000) (34493 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_214 :
    ((31943 / 100000000) : ℝ) ≤ (214 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 214 ≤ (171407 / 100000000) := by
  have hlog : Real.log ((214 : ℕ) : ℝ) ≤ (53659761 / 10000000) := by
    apply log_nat_upper_certificate 214 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 214 (by norm_num)
    (7314369 / 500000) (14628739 / 1000000) (53659761 / 10000000) (31943 / 100000000) (171407 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_215 :
    ((793 / 2500000) : ℝ) ≤ (215 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 215 ≤ (170361 / 100000000) := by
  have hlog : Real.log ((215 : ℕ) : ℝ) ≤ (53706381 / 10000000) := by
    apply log_nat_upper_certificate 215 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 215 (by norm_num)
    (7331439 / 500000) (14662879 / 1000000) (53706381 / 10000000) (793 / 2500000) (170361 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_216 :
    ((63 / 200000) : ℝ) ≤ (216 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 216 ≤ (6773 / 4000000) := by
  have hlog : Real.log ((216 : ℕ) : ℝ) ≤ (10750557 / 2000000) := by
    apply log_nat_upper_certificate 216 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 216 (by norm_num)
    (7348469 / 500000) (14696939 / 1000000) (10750557 / 2000000) (63 / 200000) (6773 / 4000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_217 :
    ((31283 / 100000000) : ℝ) ≤ (217 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 217 ≤ (168301 / 100000000) := by
  have hlog : Real.log ((217 : ℕ) : ℝ) ≤ (26899487 / 5000000) := by
    apply log_nat_upper_certificate 217 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 217 (by norm_num)
    (14730919 / 1000000) (368273 / 25000) (26899487 / 5000000) (31283 / 100000000) (168301 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_218 :
    ((7767 / 25000000) : ℝ) ≤ (218 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 218 ≤ (167287 / 100000000) := by
  have hlog : Real.log ((218 : ℕ) : ℝ) ≤ (53844951 / 10000000) := by
    apply log_nat_upper_certificate 218 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 218 (by norm_num)
    (14764823 / 1000000) (1845603 / 125000) (53844951 / 10000000) (7767 / 25000000) (167287 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_219 :
    ((6171 / 20000000) : ℝ) ≤ (219 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 219 ≤ (166283 / 100000000) := by
  have hlog : Real.log ((219 : ℕ) : ℝ) ≤ (26945359 / 5000000) := by
    apply log_nat_upper_certificate 219 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 219 (by norm_num)
    (1849831 / 125000) (14798649 / 1000000) (26945359 / 5000000) (6171 / 20000000) (166283 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_220 :
    ((6129 / 20000000) : ℝ) ≤ (220 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 220 ≤ (165291 / 100000000) := by
  have hlog : Real.log ((220 : ℕ) : ℝ) ≤ (13484069 / 2500000) := by
    apply log_nat_upper_certificate 220 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 220 (by norm_num)
    (3708099 / 250000) (14832397 / 1000000) (13484069 / 2500000) (6129 / 20000000) (165291 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_221 :
    ((30437 / 100000000) : ℝ) ≤ (221 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 221 ≤ (41077 / 25000000) := by
  have hlog : Real.log ((221 : ℕ) : ℝ) ≤ (13495407 / 2500000) := by
    apply log_nat_upper_certificate 221 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 221 (by norm_num)
    (3716517 / 250000) (14866069 / 1000000) (13495407 / 2500000) (30437 / 100000000) (41077 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_222 :
    ((3779 / 12500000) : ℝ) ≤ (222 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 222 ≤ (20417 / 12500000) := by
  have hlog : Real.log ((222 : ℕ) : ℝ) ≤ (27013387 / 5000000) := by
    apply log_nat_upper_certificate 222 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 222 (by norm_num)
    (931229 / 62500) (2979933 / 200000) (27013387 / 5000000) (3779 / 12500000) (20417 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_223 :
    ((30029 / 100000000) : ℝ) ≤ (223 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 223 ≤ (162373 / 100000000) := by
  have hlog : Real.log ((223 : ℕ) : ℝ) ≤ (27035859 / 5000000) := by
    apply log_nat_upper_certificate 223 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 223 (by norm_num)
    (233331 / 15625) (2986637 / 200000) (27035859 / 5000000) (30029 / 100000000) (162373 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_224 :
    ((7457 / 25000000) : ℝ) ≤ (224 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 224 ≤ (161421 / 100000000) := by
  have hlog : Real.log ((224 : ℕ) : ℝ) ≤ (54116461 / 10000000) := by
    apply log_nat_upper_certificate 224 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 224 (by norm_num)
    (14966629 / 1000000) (1496663 / 100000) (54116461 / 10000000) (7457 / 25000000) (161421 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_225 :
    ((29629 / 100000000) : ℝ) ≤ (225 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 225 ≤ (80239 / 50000000) := by
  have hlog : Real.log ((225 : ℕ) : ℝ) ≤ (10832201 / 2000000) := by
    apply log_nat_upper_certificate 225 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 225 (by norm_num)
    15 (15000001 / 1000000) (10832201 / 2000000) (29629 / 100000000) (80239 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_226 :
    ((29433 / 100000000) : ℝ) ≤ (226 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 226 ≤ (19943 / 12500000) := by
  have hlog : Real.log ((226 : ℕ) : ℝ) ≤ (54205351 / 10000000) := by
    apply log_nat_upper_certificate 226 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 226 (by norm_num)
    (939581 / 62500) (15033297 / 1000000) (54205351 / 10000000) (29433 / 100000000) (19943 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_227 :
    ((14619 / 50000000) : ℝ) ≤ (227 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 227 ≤ (7931 / 5000000) := by
  have hlog : Real.log ((227 : ℕ) : ℝ) ≤ (54249501 / 10000000) := by
    apply log_nat_upper_certificate 227 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 227 (by norm_num)
    (15066519 / 1000000) (376663 / 25000) (54249501 / 10000000) (14619 / 50000000) (7931 / 5000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_228 :
    ((14523 / 50000000) : ℝ) ≤ (228 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 228 ≤ (31541 / 20000000) := by
  have hlog : Real.log ((228 : ℕ) : ℝ) ≤ (54293457 / 10000000) := by
    apply log_nat_upper_certificate 228 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 228 (by norm_num)
    (3774917 / 250000) (15099669 / 1000000) (54293457 / 10000000) (14523 / 50000000) (31541 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem ThreeHalvesBlock06_lower :
    ((207337 / 20000000) : ℝ) ≤ (∑ n ∈ Finset.Ico (197 : ℕ) 229, (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  have h197 := threeHalves_row_197.1
  have h198 := threeHalves_row_198.1
  have h199 := threeHalves_row_199.1
  have h200 := threeHalves_row_200.1
  have h201 := threeHalves_row_201.1
  have h202 := threeHalves_row_202.1
  have h203 := threeHalves_row_203.1
  have h204 := threeHalves_row_204.1
  have h205 := threeHalves_row_205.1
  have h206 := threeHalves_row_206.1
  have h207 := threeHalves_row_207.1
  have h208 := threeHalves_row_208.1
  have h209 := threeHalves_row_209.1
  have h210 := threeHalves_row_210.1
  have h211 := threeHalves_row_211.1
  have h212 := threeHalves_row_212.1
  have h213 := threeHalves_row_213.1
  have h214 := threeHalves_row_214.1
  have h215 := threeHalves_row_215.1
  have h216 := threeHalves_row_216.1
  have h217 := threeHalves_row_217.1
  have h218 := threeHalves_row_218.1
  have h219 := threeHalves_row_219.1
  have h220 := threeHalves_row_220.1
  have h221 := threeHalves_row_221.1
  have h222 := threeHalves_row_222.1
  have h223 := threeHalves_row_223.1
  have h224 := threeHalves_row_224.1
  have h225 := threeHalves_row_225.1
  have h226 := threeHalves_row_226.1
  have h227 := threeHalves_row_227.1
  have h228 := threeHalves_row_228.1
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h197, h198, h199, h200, h201, h202, h203, h204, h205, h206, h207, h208, h209, h210, h211, h212, h213, h214, h215, h216, h217, h218, h219, h220, h221, h222, h223, h224, h225, h226, h227, h228]

#print axioms ThreeHalvesBlock06_lower

theorem ThreeHalvesBlock06_upper :
    (∑ n ∈ Finset.Ico (197 : ℕ) 229, logPowerTerm n) ≤ ((693963 / 12500000) : ℝ) := by
  have h197 := threeHalves_row_197.2
  have h198 := threeHalves_row_198.2
  have h199 := threeHalves_row_199.2
  have h200 := threeHalves_row_200.2
  have h201 := threeHalves_row_201.2
  have h202 := threeHalves_row_202.2
  have h203 := threeHalves_row_203.2
  have h204 := threeHalves_row_204.2
  have h205 := threeHalves_row_205.2
  have h206 := threeHalves_row_206.2
  have h207 := threeHalves_row_207.2
  have h208 := threeHalves_row_208.2
  have h209 := threeHalves_row_209.2
  have h210 := threeHalves_row_210.2
  have h211 := threeHalves_row_211.2
  have h212 := threeHalves_row_212.2
  have h213 := threeHalves_row_213.2
  have h214 := threeHalves_row_214.2
  have h215 := threeHalves_row_215.2
  have h216 := threeHalves_row_216.2
  have h217 := threeHalves_row_217.2
  have h218 := threeHalves_row_218.2
  have h219 := threeHalves_row_219.2
  have h220 := threeHalves_row_220.2
  have h221 := threeHalves_row_221.2
  have h222 := threeHalves_row_222.2
  have h223 := threeHalves_row_223.2
  have h224 := threeHalves_row_224.2
  have h225 := threeHalves_row_225.2
  have h226 := threeHalves_row_226.2
  have h227 := threeHalves_row_227.2
  have h228 := threeHalves_row_228.2
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h197, h198, h199, h200, h201, h202, h203, h204, h205, h206, h207, h208, h209, h210, h211, h212, h213, h214, h215, h216, h217, h218, h219, h220, h221, h222, h223, h224, h225, h226, h227, h228]

#print axioms ThreeHalvesBlock06_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
