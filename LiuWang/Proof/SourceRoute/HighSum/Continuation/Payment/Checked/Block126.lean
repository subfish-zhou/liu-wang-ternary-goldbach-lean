import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_448_0 : (3161658062261 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3697544583189599498289 / 34534091949243392000 : ℝ) := by
  apply lower_of_taylor (t := (577057 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_448 : (1152754732261 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 448 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3161658062261 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_448_0
  · norm_num [gridPoint]

theorem exp_7_449_0 : (28051582108869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (950677722641176944017 / 8869169199879561216 : ℝ) := by
  apply lower_of_taylor (t := (1155193 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_449 : (511386642493 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 449 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (28051582108869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_449_0
  · norm_num [gridPoint]

theorem exp_7_450_0 : (24886473261049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (119349560740867332117377 / 1112207067170540544000 : ℝ) := by
  apply lower_of_taylor (t := (578137 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_450 : (3629487978273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 450 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (24886473261049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_450_0
  · norm_num [gridPoint]

theorem exp_7_451_0 : (11038322126061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11986596539231248797327 / 111577369393257472000 : ℝ) := by
  apply lower_of_taylor (t := (2314713 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_451 : (3219697466699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 451 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (11038322126061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_451_0
  · norm_num [gridPoint]

theorem exp_7_452_0 : (783297312673 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (12038393178256724725207 / 111934603027104768000 : ℝ) := by
  apply lower_of_taylor (t := (1158441 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_452 : (2855937189189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 452 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (783297312673 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_452_0
  · norm_num [gridPoint]

theorem exp_7_453_0 : (17368578909803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (120903462409716271636043 / 1122924076185959424000 : ℝ) := by
  apply lower_of_taylor (t := (463811 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_453 : (253306475737 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 453 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (17368578909803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_453_0
  · norm_num [gridPoint]

theorem exp_7_454_0 : (308074781603 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (24284911954368844561491 / 225301566335461990400 : ℝ) := by
  apply lower_of_taylor (t := (2321231 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_454 : (1123254493021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 454 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (308074781603 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_454_0
  · norm_num [gridPoint]

theorem exp_7_455_0 : (13660054068857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (30486806591758940612143 / 282524324186274816000 : ℝ) := by
  apply lower_of_taylor (t := (2323411 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_455 : (1992206830811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 455 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (13660054068857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_455_0
  · norm_num [gridPoint]

theorem exp_7_456_0 : (12112763836557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6123573234668777612083 / 56684623569466368000 : ℝ) := by
  apply lower_of_taylor (t := (1162797 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_456 : (353309448609 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 456 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (12112763836557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_456_0
  · norm_num [gridPoint]

theorem exp_7_457_0 : (268496621367 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (24599455449789650773797 / 227458671121998848000 : ℝ) := by
  apply lower_of_taylor (t := (116389 / 50000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_457 : (1566321188601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 457 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (268496621367 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_457_0
  · norm_num [gridPoint]

theorem exp_7_458_0 : (1190225631489 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (123524666531838529012813 / 1140899949407099904000 : ℝ) := by
  apply lower_of_taylor (t := (2329971 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_458 : (173584644783 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 458 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1190225631489 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_458_0
  · norm_num [gridPoint]

theorem exp_7_459_0 : (8441212306567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (12405363504013103935541 / 114451225278064435200 : ℝ) := by
  apply lower_of_taylor (t := (583041 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_459 : (1231081570593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 459 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (8441212306567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_459_0
  · norm_num [gridPoint]

theorem exp_7_460_0 : (3741326410379 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (62292092635955223289521 / 574065132865313792000 : ℝ) := by
  apply lower_of_taylor (t := (1167181 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_460 : (1091283532771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 460 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3741326410379 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_460_0
  · norm_num [gridPoint]

theorem exp_7_461_0 : (1326483221911 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5004652789010456494639 / 46070159530281984000 : ℝ) := by
  apply lower_of_taylor (t := (1168281 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_461 : (6045521769 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 461 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1326483221911 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_461_0
  · norm_num [gridPoint]

theorem exp_7_462_0 : (2939161846467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5026001635930743935939 / 46215336814396416000 : ℝ) := by
  apply lower_of_taylor (t := (2338767 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_462 : (85730528999 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 462 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2939161846467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_462_0
  · norm_num [gridPoint]

theorem exp_7_463_0 : (2604779447361 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (15773168911127083294851 / 144877320254901248000 : ℝ) := by
  apply lower_of_taylor (t := (93639 / 40000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_463 : (189942857533 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 463 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2604779447361 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_463_0
  · norm_num [gridPoint]

theorem exp_7_464_0 : (9016631709 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3168056334889756948231 / 29066485332373708800 : ℝ) := by
  apply lower_of_taylor (t := (1171593 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_464 : (336640453171 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 464 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (9016631709 / 1953125000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_464_0
  · norm_num [gridPoint]

theorem exp_7_465_0 : (4090662754329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (127260749716074094792037 / 1166305974127125504000 : ℝ) := by
  apply lower_of_taylor (t := (2345401 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_465 : (1193179213 / 2000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 465 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (4090662754329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_465_0
  · norm_num [gridPoint]

theorem exp_7_466_0 : (362442623253 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (25560168549710555725893 / 233991648907148288000 : ℝ) := by
  apply lower_of_taylor (t := (2347619 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_466 : (528592834393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 466 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (362442623253 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_466_0
  · norm_num [gridPoint]

theorem exp_7_467_0 : (50173135399 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (12834253499111099112379 / 117361622452079616000 : ℝ) := by
  apply lower_of_taylor (t := (2349841 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_467 : (117077443543 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 467 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (50173135399 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_467_0
  · norm_num [gridPoint]

theorem exp_7_468_0 : (28446555419 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2078803692610216031569 / 18988385711004672000 : ℝ) := by
  apply lower_of_taylor (t := (1176033 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_468 : (414869675721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 468 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (28446555419 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_468_0
  · norm_num [gridPoint]

theorem exp_7_469_0 : (2519850820283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (835036949024546121369 / 7619027827227238400 : ℝ) := by
  apply lower_of_taylor (t := (470859 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_469 : (367499571487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 469 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2519850820283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_469_0
  · norm_num [gridPoint]

theorem exp_7_470_0 : (2231962051033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (129977231960109417370807 / 1184624421934593024000 : ℝ) := by
  apply lower_of_taylor (t := (147283 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_470 : (325513356079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 470 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2231962051033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_470_0
  · norm_num [gridPoint]

theorem exp_7_471_0 : (1976813811609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6526267301191618065769 / 59415262011270144000 : ℝ) := by
  apply lower_of_taylor (t := (589691 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_471 : (72075519593 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 471 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1976813811609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_471_0
  · norm_num [gridPoint]

theorem exp_7_472_0 : (1750700538457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6553753589402907116409 / 59599588404632576000 : ℝ) := by
  apply lower_of_taylor (t := (2361003 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_472 : (127662656159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 472 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1750700538457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_472_0
  · norm_num [gridPoint]

theorem exp_7_473_0 : (1550333938499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (131626411750871422091473 / 1195684005536338944000 : ℝ) := by
  apply lower_of_taylor (t := (1181623 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_473 : (113051743673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 473 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1550333938499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_473_0
  · norm_num [gridPoint]

theorem exp_7_474_0 : (686398126509 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5287174736414274491501 / 47975278102258606080 : ℝ) := by
  apply lower_of_taylor (t := (2365493 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_474 : (200211072283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 474 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (686398126509 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_474_0
  · norm_num [gridPoint]

theorem exp_7_475_0 : (607749363289 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (66366972132299562299301 / 601542804576515072000 : ℝ) := by
  apply lower_of_taylor (t := (2367743 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_475 : (177270518383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 475 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (607749363289 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_475_0
  · norm_num [gridPoint]

theorem exp_7_476_0 : (43045788191 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (13329014181168287070697 / 120679497532603392000 : ℝ) := by
  apply lower_of_taylor (t := (2369997 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_476 : (156946877441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 476 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (43045788191 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_476_0
  · norm_num [gridPoint]

theorem exp_7_477_0 : (119087105997 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (26769592709938552458979 / 242102010215095296000 : ℝ) := by
  apply lower_of_taylor (t := (1186127 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_477 : (27788604037 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 477 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (119087105997 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_477_0
  · norm_num [gridPoint]

theorem exp_7_478_0 : (168669600937 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (134407411976713461044643 / 1214230836401357824000 : ℝ) := by
  apply lower_of_taylor (t := (1187257 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_478 : (61497694197 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 478 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (168669600937 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_478_0
  · norm_num [gridPoint]

theorem exp_7_479_0 : (746495338439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1687106119885370357981 / 15224466641295974400 : ℝ) := by
  apply lower_of_taylor (t := (1188389 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_479 : (27217555379 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 479 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (746495338439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_479_0
  · norm_num [gridPoint]

theorem sum_7_448_2 : (2175528017247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 448 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_448) (by simpa only [blockSum_one] using cell_7_449) (by norm_num)

theorem sum_7_450_2 : (1712296361243 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 450 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_450) (by simpa only [blockSum_one] using cell_7_451) (by norm_num)

theorem sum_7_448_4 : (388782437849 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 448 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_448_2 sum_7_450_2 (by norm_num)

theorem sum_7_452_2 : (5389001946559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 452 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_452) (by simpa only [blockSum_one] using cell_7_453) (by norm_num)

theorem sum_7_454_2 : (4238715816853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 454 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_454) (by simpa only [blockSum_one] using cell_7_455) (by norm_num)

theorem sum_7_452_4 : (2406929440853 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 452 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_452_2 sum_7_454_2 (by norm_num)

theorem sum_7_448_8 : (6294753819343 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 448 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_448_4 sum_7_452_4 (by norm_num)

theorem sum_7_456_2 : (1666434215823 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 456 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_456) (by simpa only [blockSum_one] using cell_7_457) (by norm_num)

theorem sum_7_458_2 : (2619758728857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 458 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_458) (by simpa only [blockSum_one] using cell_7_459) (by norm_num)

theorem sum_7_456_4 : (5952627160503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 456 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_456_2 sum_7_458_2 (by norm_num)

theorem sum_7_460_2 : (2058567015811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 460 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_460) (by simpa only [blockSum_one] using cell_7_461) (by norm_num)

theorem sum_7_462_2 : (808538360061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 462 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_462) (by simpa only [blockSum_one] using cell_7_463) (by norm_num)

theorem sum_7_460_4 : (3675643735933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 460 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_460_2 sum_7_462_2 (by norm_num)

theorem sum_7_456_8 : (2407067724109 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 456 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_456_4 sum_7_460_4 (by norm_num)

theorem sum_7_448_16 : (2175455385863 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 448 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_448_8 sum_7_456_8 (by norm_num)

theorem sum_7_464_2 : (634935256421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 464 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_464) (by simpa only [blockSum_one] using cell_7_465) (by norm_num)

theorem sum_7_466_2 : (199380521713 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 466 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_466) (by simpa only [blockSum_one] using cell_7_467) (by norm_num)

theorem sum_7_464_4 : (2266773121407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 464 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_464_2 sum_7_466_2 (by norm_num)

theorem sum_7_468_2 : (97796155901 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 468 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_468) (by simpa only [blockSum_one] using cell_7_469) (by norm_num)

theorem sum_7_470_2 : (613815434451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 470 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_470) (by simpa only [blockSum_one] using cell_7_471) (by norm_num)

theorem sum_7_468_4 : (1396184681659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 468 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_468_2 sum_7_470_2 (by norm_num)

theorem sum_7_464_8 : (1831478901533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 464 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_464_4 sum_7_468_4 (by norm_num)

theorem sum_7_472_2 : (30089299979 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 472 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_472) (by simpa only [blockSum_one] using cell_7_473) (by norm_num)

theorem sum_7_474_2 : (188740795333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 474 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_474) (by simpa only [blockSum_one] using cell_7_475) (by norm_num)

theorem sum_7_472_4 : (85891039033 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 472 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_472_2 sum_7_474_2 (by norm_num)

theorem sum_7_476_2 : (147944948813 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 476 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_476) (by simpa only [blockSum_one] using cell_7_477) (by norm_num)

theorem sum_7_478_2 : (23186560991 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 478 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_478) (by simpa only [blockSum_one] using cell_7_479) (by norm_num)

theorem sum_7_476_4 : (32984719221 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 476 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_476_2 sum_7_478_2 (by norm_num)

theorem sum_7_472_8 : (693332948933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 472 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_472_4 sum_7_476_4 (by norm_num)

theorem sum_7_464_16 : (1262405925233 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 464 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_464_8 sum_7_472_8 (by norm_num)

theorem sum_7_448_32 : (1992845493737 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 448 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_448_16 sum_7_464_16 (by norm_num)

#print axioms sum_7_448_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
