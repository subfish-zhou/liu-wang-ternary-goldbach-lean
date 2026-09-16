import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.ThreeHalvesPilot

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

theorem threeHalves_row_229 :
    ((3607 / 12500000) : ℝ) ≤ (229 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 229 ≤ (49 / 31250) := by
  have hlog : Real.log ((229 : ℕ) : ℝ) ≤ (54337221 / 10000000) := by
    apply log_nat_upper_certificate 229 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 229 (by norm_num)
    (3026549 / 200000) (7566373 / 500000) (54337221 / 10000000) (3607 / 12500000) (49 / 31250)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_230 :
    ((7167 / 25000000) : ℝ) ≤ (230 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 230 ≤ (155903 / 100000000) := by
  have hlog : Real.log ((230 : ℕ) : ℝ) ≤ (27190397 / 5000000) := by
    apply log_nat_upper_certificate 230 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 230 (by norm_num)
    (60663 / 4000) (15165751 / 1000000) (27190397 / 5000000) (7167 / 25000000) (155903 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_231 :
    ((14241 / 50000000) : ℝ) ≤ (231 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 231 ≤ (19377 / 12500000) := by
  have hlog : Real.log ((231 : ℕ) : ℝ) ≤ (27212089 / 5000000) := by
    apply log_nat_upper_certificate 231 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 231 (by norm_num)
    (3799671 / 250000) (3039737 / 200000) (27212089 / 5000000) (14241 / 50000000) (19377 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_232 :
    ((14149 / 50000000) : ℝ) ≤ (232 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 232 ≤ (154137 / 100000000) := by
  have hlog : Real.log ((232 : ℕ) : ℝ) ≤ (27233687 / 5000000) := by
    apply log_nat_upper_certificate 232 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 232 (by norm_num)
    (7615773 / 500000) (15231547 / 1000000) (27233687 / 5000000) (14149 / 50000000) (154137 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_233 :
    ((7029 / 25000000) : ℝ) ≤ (233 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 233 ≤ (76633 / 50000000) := by
  have hlog : Real.log ((233 : ℕ) : ℝ) ≤ (10902077 / 2000000) := by
    apply log_nat_upper_certificate 233 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 233 (by norm_num)
    (15264337 / 1000000) (7632169 / 500000) (10902077 / 2000000) (7029 / 25000000) (76633 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_234 :
    ((873 / 3125000) : ℝ) ≤ (234 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 234 ≤ (30481 / 20000000) := by
  have hlog : Real.log ((234 : ℕ) : ℝ) ≤ (13638303 / 2500000) := by
    apply log_nat_upper_certificate 234 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 234 (by norm_num)
    (7648529 / 500000) (15297059 / 1000000) (13638303 / 2500000) (873 / 3125000) (30481 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_235 :
    ((13879 / 50000000) : ℝ) ≤ (235 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 235 ≤ (151551 / 100000000) := by
  have hlog : Real.log ((235 : ℕ) : ℝ) ≤ (3412241 / 625000) := by
    apply log_nat_upper_certificate 235 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 235 (by norm_num)
    (15329709 / 1000000) (1532971 / 100000) (3412241 / 625000) (13879 / 50000000) (151551 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_236 :
    ((13791 / 50000000) : ℝ) ≤ (236 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 236 ≤ (75353 / 50000000) := by
  have hlog : Real.log ((236 : ℕ) : ℝ) ≤ (54638319 / 10000000) := by
    apply log_nat_upper_certificate 236 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 236 (by norm_num)
    (15362291 / 1000000) (3840573 / 250000) (54638319 / 10000000) (13791 / 50000000) (75353 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_237 :
    ((1713 / 6250000) : ℝ) ≤ (237 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 237 ≤ (149869 / 100000000) := by
  have hlog : Real.log ((237 : ℕ) : ℝ) ≤ (27340301 / 5000000) := by
    apply log_nat_upper_certificate 237 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 237 (by norm_num)
    (3848701 / 250000) (3078961 / 200000) (27340301 / 5000000) (1713 / 6250000) (149869 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_238 :
    ((5447 / 20000000) : ℝ) ≤ (238 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 238 ≤ (1863 / 1250000) := by
  have hlog : Real.log ((238 : ℕ) : ℝ) ≤ (54722707 / 10000000) := by
    apply log_nat_upper_certificate 238 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 238 (by norm_num)
    (964203 / 62500) (15427249 / 1000000) (54722707 / 10000000) (5447 / 20000000) (1863 / 1250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_239 :
    ((3383 / 12500000) : ℝ) ≤ (239 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 239 ≤ (148219 / 100000000) := by
  have hlog : Real.log ((239 : ℕ) : ℝ) ≤ (13691159 / 2500000) := by
    apply log_nat_upper_certificate 239 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 239 (by norm_num)
    (1932453 / 125000) (123677 / 8000) (13691159 / 2500000) (3383 / 12500000) (148219 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_240 :
    ((5379 / 20000000) : ℝ) ≤ (240 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 240 ≤ (73703 / 50000000) := by
  have hlog : Real.log ((240 : ℕ) : ℝ) ≤ (5480639 / 1000000) := by
    apply log_nat_upper_certificate 240 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 240 (by norm_num)
    (15491933 / 1000000) (7745967 / 500000) (5480639 / 1000000) (5379 / 20000000) (73703 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_241 :
    ((3341 / 12500000) : ℝ) ≤ (241 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 241 ≤ (146601 / 100000000) := by
  have hlog : Real.log ((241 : ℕ) : ℝ) ≤ (5484797 / 1000000) := by
    apply log_nat_upper_certificate 241 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 241 (by norm_num)
    (7762087 / 500000) (620967 / 40000) (5484797 / 1000000) (3341 / 12500000) (146601 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_242 :
    ((13281 / 50000000) : ℝ) ≤ (242 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 242 ≤ (145803 / 100000000) := by
  have hlog : Real.log ((242 : ℕ) : ℝ) ≤ (27444689 / 5000000) := by
    apply log_nat_upper_certificate 242 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 242 (by norm_num)
    (15556349 / 1000000) (311127 / 20000) (27444689 / 5000000) (13281 / 50000000) (145803 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_243 :
    ((26399 / 100000000) : ℝ) ≤ (243 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 243 ≤ (145013 / 100000000) := by
  have hlog : Real.log ((243 : ℕ) : ℝ) ≤ (10986123 / 2000000) := by
    apply log_nat_upper_certificate 243 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 243 (by norm_num)
    (15588457 / 1000000) (7794229 / 500000) (10986123 / 2000000) (26399 / 100000000) (145013 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_244 :
    ((26237 / 100000000) : ℝ) ≤ (244 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 244 ≤ (14423 / 10000000) := by
  have hlog : Real.log ((244 : ℕ) : ℝ) ≤ (54971683 / 10000000) := by
    apply log_nat_upper_certificate 244 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 244 (by norm_num)
    (15620499 / 1000000) (31241 / 2000) (54971683 / 10000000) (26237 / 100000000) (14423 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_245 :
    ((6519 / 25000000) : ℝ) ≤ (245 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 245 ≤ (28691 / 20000000) := by
  have hlog : Real.log ((245 : ℕ) : ℝ) ≤ (55012583 / 10000000) := by
    apply log_nat_upper_certificate 245 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 245 (by norm_num)
    (626099 / 40000) (3913119 / 250000) (55012583 / 10000000) (6519 / 25000000) (28691 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_246 :
    ((25917 / 100000000) : ℝ) ≤ (246 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 246 ≤ (71343 / 50000000) := by
  have hlog : Real.log ((246 : ℕ) : ℝ) ≤ (13763329 / 2500000) := by
    apply log_nat_upper_certificate 246 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 246 (by norm_num)
    (15684387 / 1000000) (3921097 / 250000) (13763329 / 2500000) (25917 / 100000000) (71343 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_247 :
    ((161 / 625000) : ℝ) ≤ (247 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 247 ≤ (5677 / 4000000) := by
  have hlog : Real.log ((247 : ℕ) : ℝ) ≤ (13773471 / 2500000) := by
    apply log_nat_upper_certificate 247 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 247 (by norm_num)
    (15716233 / 1000000) (7858117 / 500000) (13773471 / 2500000) (161 / 625000) (5677 / 4000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_248 :
    ((6401 / 25000000) : ℝ) ≤ (248 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 248 ≤ (141171 / 100000000) := by
  have hlog : Real.log ((248 : ℕ) : ℝ) ≤ (3445893 / 625000) := by
    apply log_nat_upper_certificate 248 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 248 (by norm_num)
    (3149603 / 200000) (984251 / 62500) (3445893 / 625000) (6401 / 25000000) (141171 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_249 :
    ((509 / 2000000) : ℝ) ≤ (249 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 249 ≤ (17553 / 12500000) := by
  have hlog : Real.log ((249 : ℕ) : ℝ) ≤ (5517453 / 1000000) := by
    apply log_nat_upper_certificate 249 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 249 (by norm_num)
    (15779733 / 1000000) (7889867 / 500000) (5517453 / 1000000) (509 / 2000000) (17553 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_250 :
    ((12649 / 50000000) : ℝ) ≤ (250 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 250 ≤ (34921 / 25000000) := by
  have hlog : Real.log ((250 : ℕ) : ℝ) ≤ (5521461 / 1000000) := by
    apply log_nat_upper_certificate 250 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 250 (by norm_num)
    (3952847 / 250000) (15811389 / 1000000) (5521461 / 1000000) (12649 / 50000000) (34921 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_251 :
    ((25147 / 100000000) : ℝ) ≤ (251 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 251 ≤ (2779 / 2000000) := by
  have hlog : Real.log ((251 : ℕ) : ℝ) ≤ (5525453 / 1000000) := by
    apply log_nat_upper_certificate 251 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 251 (by norm_num)
    (15842979 / 1000000) (792149 / 50000) (5525453 / 1000000) (25147 / 100000000) (2779 / 2000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_252 :
    ((24997 / 100000000) : ℝ) ≤ (252 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 252 ≤ (138223 / 100000000) := by
  have hlog : Real.log ((252 : ℕ) : ℝ) ≤ (13823573 / 2500000) := by
    apply log_nat_upper_certificate 252 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 252 (by norm_num)
    (15874507 / 1000000) (3968627 / 250000) (13823573 / 2500000) (24997 / 100000000) (138223 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_253 :
    ((24849 / 100000000) : ℝ) ≤ (253 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 253 ≤ (137503 / 100000000) := by
  have hlog : Real.log ((253 : ℕ) : ℝ) ≤ (6916737 / 1250000) := by
    apply log_nat_upper_certificate 253 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 253 (by norm_num)
    (15905973 / 1000000) (7952987 / 500000) (6916737 / 1250000) (24849 / 100000000) (137503 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_254 :
    ((12351 / 50000000) : ℝ) ≤ (254 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 254 ≤ (136789 / 100000000) := by
  have hlog : Real.log ((254 : ℕ) : ℝ) ≤ (55373343 / 10000000) := by
    apply log_nat_upper_certificate 254 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 254 (by norm_num)
    (15937377 / 1000000) (7968689 / 500000) (55373343 / 10000000) (12351 / 50000000) (136789 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem threeHalves_row_255 :
    ((24557 / 100000000) : ℝ) ≤ (255 : ℝ) ^ (-3 / 2 : ℝ) ∧ logPowerTerm 255 ≤ (68041 / 50000000) := by
  have hlog : Real.log ((255 : ℕ) : ℝ) ≤ (13853159 / 2500000) := by
    apply log_nat_upper_certificate 255 7 (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ]
  simpa using! threeHalves_term_certificate 255 (by norm_num)
    (15968719 / 1000000) (199609 / 12500) (13853159 / 2500000) (24557 / 100000000) (68041 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog (by norm_num) (by norm_num)

theorem ThreeHalvesBlock07_lower :
    ((718581 / 100000000) : ℝ) ≤ (∑ n ∈ Finset.Ico (229 : ℕ) 256, (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  have h229 := threeHalves_row_229.1
  have h230 := threeHalves_row_230.1
  have h231 := threeHalves_row_231.1
  have h232 := threeHalves_row_232.1
  have h233 := threeHalves_row_233.1
  have h234 := threeHalves_row_234.1
  have h235 := threeHalves_row_235.1
  have h236 := threeHalves_row_236.1
  have h237 := threeHalves_row_237.1
  have h238 := threeHalves_row_238.1
  have h239 := threeHalves_row_239.1
  have h240 := threeHalves_row_240.1
  have h241 := threeHalves_row_241.1
  have h242 := threeHalves_row_242.1
  have h243 := threeHalves_row_243.1
  have h244 := threeHalves_row_244.1
  have h245 := threeHalves_row_245.1
  have h246 := threeHalves_row_246.1
  have h247 := threeHalves_row_247.1
  have h248 := threeHalves_row_248.1
  have h249 := threeHalves_row_249.1
  have h250 := threeHalves_row_250.1
  have h251 := threeHalves_row_251.1
  have h252 := threeHalves_row_252.1
  have h253 := threeHalves_row_253.1
  have h254 := threeHalves_row_254.1
  have h255 := threeHalves_row_255.1
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h229, h230, h231, h232, h233, h234, h235, h236, h237, h238, h239, h240, h241, h242, h243, h244, h245, h246, h247, h248, h249, h250, h251, h252, h253, h254, h255]

#print axioms ThreeHalvesBlock07_lower

theorem ThreeHalvesBlock07_upper :
    (∑ n ∈ Finset.Ico (229 : ℕ) 256, logPowerTerm n) ≤ ((3942857 / 100000000) : ℝ) := by
  have h229 := threeHalves_row_229.2
  have h230 := threeHalves_row_230.2
  have h231 := threeHalves_row_231.2
  have h232 := threeHalves_row_232.2
  have h233 := threeHalves_row_233.2
  have h234 := threeHalves_row_234.2
  have h235 := threeHalves_row_235.2
  have h236 := threeHalves_row_236.2
  have h237 := threeHalves_row_237.2
  have h238 := threeHalves_row_238.2
  have h239 := threeHalves_row_239.2
  have h240 := threeHalves_row_240.2
  have h241 := threeHalves_row_241.2
  have h242 := threeHalves_row_242.2
  have h243 := threeHalves_row_243.2
  have h244 := threeHalves_row_244.2
  have h245 := threeHalves_row_245.2
  have h246 := threeHalves_row_246.2
  have h247 := threeHalves_row_247.2
  have h248 := threeHalves_row_248.2
  have h249 := threeHalves_row_249.2
  have h250 := threeHalves_row_250.2
  have h251 := threeHalves_row_251.2
  have h252 := threeHalves_row_252.2
  have h253 := threeHalves_row_253.2
  have h254 := threeHalves_row_254.2
  have h255 := threeHalves_row_255.2
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] at *
  linarith only [h229, h230, h231, h232, h233, h234, h235, h236, h237, h238, h239, h240, h241, h242, h243, h244, h245, h246, h247, h248, h249, h250, h251, h252, h253, h254, h255]

#print axioms ThreeHalvesBlock07_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
