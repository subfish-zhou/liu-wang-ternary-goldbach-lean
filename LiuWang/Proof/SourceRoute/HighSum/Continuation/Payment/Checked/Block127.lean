import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_480_0 : (660717346929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8470699930632870422417 / 76355595986402304000 : ℝ) := by
  apply lower_of_taylor (t := (1189523 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_480 : (48180102551 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 480 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (660717346929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_480_0
  · norm_num [gridPoint]

theorem exp_7_481_0 : (116950690381 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (27219108474537403417497 / 245085489967526912000 : ℝ) := by
  apply lower_of_taylor (t := (2381317 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_481 : (42640747077 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 481 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (116950690381 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_481_0
  · norm_num [gridPoint]

theorem exp_7_482_0 : (103497174789 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (27332304507319512261437 / 245834214693854208000 : ℝ) := by
  apply lower_of_taylor (t := (297949 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_482 : (75471069713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 482 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (103497174789 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_482_0
  · norm_num [gridPoint]

theorem exp_7_483_0 : (228961768881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (68614570939971110550019 / 616460203338673152000 : ℝ) := by
  apply lower_of_taylor (t := (238587 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_483 : (33392195789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 483 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (228961768881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_483_0
  · norm_num [gridPoint]

theorem exp_7_484_0 : (81037556371 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (13779840290080565814831 / 123667544946186035200 : ℝ) := by
  apply lower_of_taylor (t := (298519 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_484 : (59093314177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 484 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (81037556371 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_484_0
  · norm_num [gridPoint]

theorem exp_7_485_0 : (22406229461 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (138369308097272534134267 / 1240436201822813184000 : ℝ) := by
  apply lower_of_taylor (t := (2390437 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_485 : (13071059063 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 485 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (22406229461 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_485_0
  · norm_num [gridPoint]

theorem exp_7_486_0 : (15858436767 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5557674398697100429607 / 49768106550408192000 : ℝ) := by
  apply lower_of_taylor (t := (95709 / 40000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_486 : (23128229137 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 486 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (15858436767 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_486_0
  · norm_num [gridPoint]

theorem exp_7_487_0 : (140291484593 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1395160610093552496483 / 12479748352740352000 : ℝ) := by
  apply lower_of_taylor (t := (1197509 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_487 : (20460362199 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 487 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (140291484593 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_487_0
  · norm_num [gridPoint]

theorem exp_7_488_0 : (31024995161 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (35022978430285103135227 / 312938179091076096000 : ℝ) := by
  apply lower_of_taylor (t := (2397313 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_488 : (18098964169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 488 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (31024995161 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_488_0
  · norm_num [gridPoint]

theorem exp_7_489_0 : (54884754441 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (28133884120173532220053 / 251107261406202470400 : ℝ) := by
  apply lower_of_taylor (t := (2399613 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_489 : (16008982417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 489 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (54884754441 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_489_0
  · norm_num [gridPoint]

theorem exp_7_490_0 : (194174173891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (141248584146621657008637 / 1259325607274159104000 : ℝ) := by
  apply lower_of_taylor (t := (480383 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_490 : (14159355213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 490 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (194174173891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_490_0
  · norm_num [gridPoint]

theorem exp_7_491_0 : (171727992831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (14182940685648706194829 / 126312061709374464000 : ℝ) := by
  apply lower_of_taylor (t := (1202111 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_491 : (3130639881 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 491 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (171727992831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_491_0
  · norm_num [gridPoint]

theorem exp_7_492_0 : (18983257933 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (14241189122854853760149 / 126692133648976896000 : ℝ) := by
  apply lower_of_taylor (t := (2406531 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_492 : (22148419579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 492 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (18983257933 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_492_0
  · norm_num [gridPoint]

theorem exp_7_493_0 : (67146059467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (142996039760890745650503 / 1270727765462232064000 : ℝ) := by
  apply lower_of_taylor (t := (481769 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_493 : (19585403931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 493 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (67146059467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_493_0
  · norm_num [gridPoint]

theorem exp_7_494_0 : (29685926561 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (28716370990319669555519 / 254907980802226790400 : ℝ) := by
  apply lower_of_taylor (t := (2411161 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_494 : (8658897743 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 494 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (29685926561 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_494_0
  · norm_num [gridPoint]

theorem exp_7_495_0 : (20997669007 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (18021167412344500708129 / 159794719017059328000 : ℝ) := by
  apply lower_of_taylor (t := (1206741 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_495 : (1531168889 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 495 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (20997669007 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_495_0
  · norm_num [gridPoint]

theorem exp_7_496_0 : (92820120573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3618962382511209524877 / 32054532745956352000 : ℝ) := by
  apply lower_of_taylor (t := (1207903 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_496 : (1353705317 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 496 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (92820120573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_496_0
  · norm_num [gridPoint]

theorem exp_7_497_0 : (41028331057 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (29069865090952027090001 / 257202115423294464000 : ℝ) := by
  apply lower_of_taylor (t := (2418133 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_497 : (1495911381 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 497 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (41028331057 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_497_0
  · norm_num [gridPoint]

theorem exp_7_498_0 : (36268231641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (145941832259775930712073 / 1289845553971129344000 : ℝ) := by
  apply lower_of_taylor (t := (151279 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_498 : (661178009 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 498 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (36268231641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_498_0
  · norm_num [gridPoint]

theorem exp_7_499_0 : (1602912649 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (94539366589406728041 / 834636284130467840 : ℝ) := by
  apply lower_of_taylor (t := (1211399 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_499 : (4675433219 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 499 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1602912649 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_499_0
  · norm_num [gridPoint]

theorem exp_7_500_0 : (56670153461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2373094932488036941721 / 20927945748544512000 : ℝ) := by
  apply lower_of_taylor (t := (151571 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_500 : (8264877009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 500 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (56670153461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_500_0
  · norm_num [gridPoint]

theorem exp_7_501_0 : (25042641327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (29545887511978835632759 / 260276948398746624000 : ℝ) := by
  apply lower_of_taylor (t := (2427477 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_501 : (7304527619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 501 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (25042641327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_501_0
  · norm_num [gridPoint]

theorem exp_7_502_0 : (11065657013 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (29665735189714550695419 / 261048511430829056000 : ℝ) := by
  apply lower_of_taylor (t := (1214911 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_502 : (6455341209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 502 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (11065657013 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_502_0
  · norm_num [gridPoint]

theorem exp_7_503_0 : (2444644621 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (37232400869594669502217 / 327276520472749056000 : ℝ) := by
  apply lower_of_taylor (t := (2432171 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_503 : (5704501827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 503 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2444644621 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_503_0
  · norm_num [gridPoint]

theorem exp_7_504_0 : (17281276643 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7476611132369830672069 / 65648765810214297600 : ℝ) := by
  apply lower_of_taylor (t := (2434523 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_504 : (40325319 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 504 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (17281276643 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_504_0
  · norm_num [gridPoint]

theorem exp_7_505_0 : (1526924731 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (150136535953711221456897 / 1316850260094014464000 : ℝ) := by
  apply lower_of_taylor (t := (1218439 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_505 : (4453788929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 505 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1526924731 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_505_0
  · norm_num [gridPoint]

theorem exp_7_506_0 : (26981200053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (30148509179081432747537 / 264146182712036352000 : ℝ) := by
  apply lower_of_taylor (t := (2439237 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_506 : (3934986697 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 506 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (26981200053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_506_0
  · norm_num [gridPoint]

theorem exp_7_507_0 : (4767347937 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (15135025497056910196601 / 132461727660278784000 : ℝ) := by
  apply lower_of_taylor (t := (1526 / 625 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_507 : (3476392947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 507 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (4767347937 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_507_0
  · norm_num [gridPoint]

theorem exp_7_508_0 : (421147783 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (75979832838640848912069 / 664254674610916352000 : ℝ) := by
  apply lower_of_taylor (t := (1221983 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_508 : (3071047471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 508 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (421147783 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_508_0
  · norm_num [gridPoint]

theorem exp_7_509_0 : (4650229659 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (30514156102725922598867 / 266481426283463270400 : ℝ) := by
  apply lower_of_taylor (t := (489267 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_509 : (2712791397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 509 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (4650229659 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_509_0
  · norm_num [gridPoint]

theorem exp_7_510_0 : (16429962997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (153183601977697509158867 / 1336310623189238784000 : ℝ) := by
  apply lower_of_taylor (t := (612177 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_510 : (1198087663 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 510 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (16429962997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_510_0
  · norm_num [gridPoint]

theorem exp_7_511_0 : (2902292749 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1201547910684141 / 10470467379200 : ℝ) := by
  apply lower_of_taylor (t := (490217 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_511 : (2116377947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 511 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2902292749 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_511_0
  · norm_num [gridPoint]

theorem sum_7_480_2 : (22705212407 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 480 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_480) (by simpa only [blockSum_one] using cell_7_481) (by norm_num)

theorem sum_7_482_2 : (142255461291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 482 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_482) (by simpa only [blockSum_one] using cell_7_483) (by norm_num)

theorem sum_7_480_4 : (323897160547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 480 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_480_2 sum_7_482_2 (by norm_num)

theorem sum_7_484_2 : (111377550429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 484 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_484) (by simpa only [blockSum_one] using cell_7_485) (by norm_num)

theorem sum_7_486_2 : (5448573917 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 486 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_486) (by simpa only [blockSum_one] using cell_7_487) (by norm_num)

theorem sum_7_484_4 : (198554733101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 484 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_484_2 sum_7_486_2 (by norm_num)

theorem sum_7_480_8 : (32653243353 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 480 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_480_4 sum_7_484_4 (by norm_num)

theorem sum_7_488_2 : (17053973293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 488 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_488) (by simpa only [blockSum_one] using cell_7_489) (by norm_num)

theorem sum_7_490_2 : (26681914737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 490 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_490) (by simpa only [blockSum_one] using cell_7_491) (by norm_num)

theorem sum_7_488_4 : (60789861323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 488 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_488_2 sum_7_490_2 (by norm_num)

theorem sum_7_492_2 : (4173382351 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 492 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_492) (by simpa only [blockSum_one] using cell_7_493) (by norm_num)

theorem sum_7_494_2 : (4078685547 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 494 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_494) (by simpa only [blockSum_one] using cell_7_495) (by norm_num)

theorem sum_7_492_4 : (37181653943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 492 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_492_2 sum_7_494_2 (by norm_num)

theorem sum_7_488_8 : (48985757633 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 488 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_488_4 sum_7_492_4 (by norm_num)

theorem sum_7_480_16 : (35919746209 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 480 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_480_8 sum_7_488_8 (by norm_num)

theorem sum_7_496_2 : (12752172109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 496 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_496) (by simpa only [blockSum_one] using cell_7_497) (by norm_num)

theorem sum_7_498_2 : (9964857291 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 498 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_498) (by simpa only [blockSum_one] using cell_7_499) (by norm_num)

theorem sum_7_496_4 : (113585147 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 496 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_496_2 sum_7_498_2 (by norm_num)

theorem sum_7_500_2 : (3892351157 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 500 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_500) (by simpa only [blockSum_one] using cell_7_501) (by norm_num)

theorem sum_7_502_2 : (3039960759 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 502 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_502) (by simpa only [blockSum_one] using cell_7_503) (by norm_num)

theorem sum_7_500_4 : (1733077979 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 500 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_500_2 sum_7_502_2 (by norm_num)

theorem sum_7_496_8 : (2286353327 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 496 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_496_4 sum_7_500_4 (by norm_num)

theorem sum_7_504_2 : (2373613451 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 504 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_504) (by simpa only [blockSum_one] using cell_7_505) (by norm_num)

theorem sum_7_506_2 : (1852844911 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 506 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_506) (by simpa only [blockSum_one] using cell_7_507) (by norm_num)

theorem sum_7_504_4 : (2113229181 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 504 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_504_2 sum_7_506_2 (by norm_num)

theorem sum_7_508_2 : (1445959717 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 508 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_508) (by simpa only [blockSum_one] using cell_7_509) (by norm_num)

theorem sum_7_510_2 : (4512553273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 510 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_510) (by simpa only [blockSum_one] using cell_7_511) (by norm_num)

theorem sum_7_508_4 : (10296392141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 508 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_508_2 sum_7_510_2 (by norm_num)

theorem sum_7_504_8 : (27202225589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 504 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_504_4 sum_7_508_4 (by norm_num)

theorem sum_7_496_16 : (100365532053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 496 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_496_8 sum_7_504_8 (by norm_num)

theorem sum_7_480_32 : (818760456233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 480 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_480_16 sum_7_496_16 (by norm_num)

#print axioms sum_7_480_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
