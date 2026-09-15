import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_416_0 : (13873705937587 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5371506321075400537 / 52005175483392000 : ℝ) := by
  apply lower_of_taylor (t := (2241033 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_416 : (25292077540663 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 416 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (13873705937587 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_416_0
  · norm_num [gridPoint]

theorem exp_7_417_0 : (617264739882953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (86333048327409203927 / 834904984439808000 : ℝ) := by
  apply lower_of_taylor (t := (1121539 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_417 : (90022998812109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 417 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (617264739882953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_417_0
  · norm_num [gridPoint]

theorem exp_7_418_0 : (549209112687843 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (103634261447477445343953 / 1001089667145124864000 : ℝ) := by
  apply lower_of_taylor (t := (1122563 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_418 : (80097643854519 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 418 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (549209112687843 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_418_0
  · norm_num [gridPoint]

theorem exp_7_419_0 : (61076130460519 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (10410200944571665990327 / 100447358746111795200 : ℝ) := by
  apply lower_of_taylor (t := (1123589 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_419 : (4453726306267 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 419 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (61076130460519 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_419_0
  · norm_num [gridPoint]

theorem exp_7_420_0 : (869306604343099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (52285619622028152026491 / 503931608676774912000 : ℝ) := by
  apply lower_of_taylor (t := (2249233 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_420 : (63390618606351 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 420 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (869306604343099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_420_0
  · norm_num [gridPoint]

theorem exp_7_421_0 : (773236578423281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (21008390668116207895071 / 202251711364484096000 : ℝ) := by
  apply lower_of_taylor (t := (562823 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_421 : (14096276500841 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 421 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (773236578423281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_421_0
  · norm_num [gridPoint]

theorem exp_7_422_0 : (34385864443089 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (21102830846675105570531 / 202931921173545984000 : ℝ) := by
  apply lower_of_taylor (t := (1126677 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_422 : (20059585029921 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 422 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (34385864443089 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_422_0
  · norm_num [gridPoint]

theorem exp_7_423_0 : (122319540535319 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (26496961105131107716787 / 254516591122369536000 : ℝ) := by
  apply lower_of_taylor (t := (112771 / 50000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_423 : (2787390872593 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 423 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (122319540535319 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_423_0
  · norm_num [gridPoint]

theorem exp_7_424_0 : (33990716995009 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1064630264001124102011 / 10214788326876651520 : ℝ) := by
  apply lower_of_taylor (t := (225749 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_424 : (79316275897947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 424 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (33990716995009 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_424_0
  · norm_num [gridPoint]

theorem exp_7_425_0 : (15111360285609 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (106939702670224127536777 / 1024897010462290944000 : ℝ) := by
  apply lower_of_taylor (t := (2259563 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_425 : (70523773992919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 425 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (15111360285609 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_425_0
  · norm_num [gridPoint]

theorem exp_7_426_0 : (429918112270211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (21483575145788848911289 / 205664179562671104000 : ℝ) := by
  apply lower_of_taylor (t := (2261639 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_426 : (12540006000519 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 426 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (429918112270211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_426_0
  · norm_num [gridPoint]

theorem exp_7_427_0 : (38218806785743 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (10789754807435742294237 / 103175049474085888000 : ℝ) := by
  apply lower_of_taylor (t := (56593 / 25000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_427 : (108865223751 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 427 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (38218806785743 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_427_0
  · norm_num [gridPoint]

theorem exp_7_428_0 : (339725297321031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (54189361102274162188409 / 517592900622400512000 : ℝ) := by
  apply lower_of_taylor (t := (566451 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_428 : (6193268475649 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 428 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (339725297321031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_428_0
  · norm_num [gridPoint]

theorem exp_7_429_0 : (30195222516563 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (21772280123520322108411 / 207725363465036390400 : ℝ) := by
  apply lower_of_taylor (t := (2267891 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_429 : (550465688607 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 429 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (30195222516563 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_429_0
  · norm_num [gridPoint]

theorem exp_7_430_0 : (268354180747207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (109345585811601943120347 / 1042073542982001664000 : ℝ) := by
  apply lower_of_taylor (t := (1134991 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_430 : (39137255919091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 430 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (268354180747207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_430_0
  · norm_num [gridPoint]

theorem exp_7_431_0 : (23847259659887 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2745782007115849594849 / 26138149455381504000 : ℝ) := by
  apply lower_of_taylor (t := (2272077 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_431 : (17389635996713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 431 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (23847259659887 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_431_0
  · norm_num [gridPoint]

theorem exp_7_432_0 : (105949468261763 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2757962163369559856129 / 26224603075623936000 : ℝ) := by
  apply lower_of_taylor (t := (90967 / 40000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_432 : (7725930414623 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 432 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (105949468261763 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_432_0
  · norm_num [gridPoint]

theorem exp_7_433_0 : (5883414868857 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (110807207060131836156213 / 1052447977411093504000 : ℝ) := by
  apply lower_of_taylor (t := (569069 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_433 : (13728764739763 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 433 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5883414868857 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_433_0
  · norm_num [gridPoint]

theorem exp_7_434_0 : (16725946406507 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (22259488871753394241877 / 211183508274733670400 : ℝ) := by
  apply lower_of_taylor (t := (1139191 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_434 : (24393420783599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 434 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (16725946406507 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_434_0
  · norm_num [gridPoint]

theorem exp_7_435_0 : (148580808671439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (55894600464386230543471 / 529696407456340992000 : ℝ) := by
  apply lower_of_taylor (t := (228049 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_435 : (21669292117783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 435 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (148580808671439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_435_0
  · norm_num [gridPoint]

theorem exp_7_436_0 : (65988111539951 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2245649585364659349423 / 21257475960562688000 : ℝ) := by
  apply lower_of_taylor (t := (2282603 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_436 : (4811912379687 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 436 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (65988111539951 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_436_0
  · norm_num [gridPoint]

theorem exp_7_437_0 : (117216790483479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (145519073387397615541 / 1375949020283904000 : ℝ) := by
  apply lower_of_taylor (t := (2284719 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_437 : (1709510734803 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 437 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (117216790483479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_437_0
  · norm_num [gridPoint]

theorem exp_7_438_0 : (104098698315791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3653987459608312144793 / 34511383644785664000 : ℝ) := by
  apply lower_of_taylor (t := (1143419 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_438 : (15181941214723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 438 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (104098698315791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_438_0
  · norm_num [gridPoint]

theorem exp_7_439_0 : (369762015643 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5688573494209560124317 / 53667550241656217600 : ℝ) := by
  apply lower_of_taylor (t := (2288961 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_439 : (6740844597187 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 439 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (369762015643 / 4000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_439_0
  · norm_num [gridPoint]

theorem exp_7_440_0 : (82080695823579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (28567715070579597929953 / 269213706563582976000 : ℝ) := by
  apply lower_of_taylor (t := (143193 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_440 : (11970796167661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 440 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (82080695823579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_440_0
  · norm_num [gridPoint]

theorem exp_7_441_0 : (18218879773007 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (22954356988064781174253 / 216072871450395648000 : ℝ) := by
  apply lower_of_taylor (t := (1146609 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_441 : (10628296652579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 441 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (18218879773007 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_441_0
  · norm_num [gridPoint]

theorem exp_7_442_0 : (64697036091479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (23054849271258481324593 / 216775919565212672000 : ℝ) := by
  apply lower_of_taylor (t := (2295351 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_442 : (2358882999017 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 442 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (64697036091479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_442_0
  · norm_num [gridPoint]

theorem exp_7_443_0 : (57431397656829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (57889123514154277828589 / 543700273988293632000 : ℝ) := by
  apply lower_of_taylor (t := (143593 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_443 : (4187949115657 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 443 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (57431397656829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_443_0
  · norm_num [gridPoint]

theorem exp_7_444_0 : (1274432546109 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11628378945445701465617 / 109092720770354995200 : ℝ) := by
  apply lower_of_taylor (t := (2299629 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_444 : (371731065041 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 444 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1274432546109 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_444_0
  · norm_num [gridPoint]

theorem exp_7_445_0 : (45244620121873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (116790876132822445302207 / 1094459577006951424000 : ℝ) := by
  apply lower_of_taylor (t := (2301773 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_445 : (2639422679 / 400000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 445 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (45244620121873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_445_0
  · norm_num [gridPoint]

theorem exp_7_446_0 : (5019146616861 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (23459901912297901855511 / 219599531177358336000 : ℝ) := by
  apply lower_of_taylor (t := (2303921 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_446 : (366000680691 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 446 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5019146616861 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_446_0
  · norm_num [gridPoint]

theorem exp_7_447_0 : (35631638527509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (736310576490892926653 / 6884634027144192000 : ℝ) := by
  apply lower_of_taylor (t := (2306073 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_447 : (1299145547113 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 447 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (35631638527509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_447_0
  · norm_num [gridPoint]

theorem sum_7_416_2 : (191191308974761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 416 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_416) (by simpa only [blockSum_one] using cell_7_417) (by norm_num)

theorem sum_7_418_2 : (151357264754791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 418 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_418) (by simpa only [blockSum_one] using cell_7_419) (by norm_num)

theorem sum_7_416_4 : (21409285858097 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 416 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_416_2 sum_7_418_2 (by norm_num)

theorem sum_7_420_2 : (23955144921943 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 420 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_420) (by simpa only [blockSum_one] using cell_7_421) (by norm_num)

theorem sum_7_422_2 : (189494433072581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 422 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_422) (by simpa only [blockSum_one] using cell_7_423) (by norm_num)

theorem sum_7_420_4 : (429045882292011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 420 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_420_2 sum_7_422_2 (by norm_num)

theorem sum_7_416_8 : (222828605950223 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 416 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_416_4 sum_7_420_4 (by norm_num)

theorem sum_7_424_2 : (74920024945433 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 424 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_424) (by simpa only [blockSum_one] using cell_7_425) (by norm_num)

theorem sum_7_426_2 : (118439024563107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 426 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_426) (by simpa only [blockSum_one] using cell_7_427) (by norm_num)

theorem sum_7_424_4 : (268279074453973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 424 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_424_2 sum_7_426_2 (by norm_num)

theorem sum_7_428_2 : (11697925361719 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 428 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_428) (by simpa only [blockSum_one] using cell_7_429) (by norm_num)

theorem sum_7_430_2 : (73916527912517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 430 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_430) (by simpa only [blockSum_one] using cell_7_431) (by norm_num)

theorem sum_7_428_4 : (167499930806269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 428 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_428_2 sum_7_430_2 (by norm_num)

theorem sum_7_424_8 : (217889502630121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 424 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_424_4 sum_7_428_4 (by norm_num)

theorem sum_7_416_16 : (1549922035011357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 416 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_416_8 sum_7_424_8 (by norm_num)

theorem sum_7_432_2 : (29180625569009 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 432 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_432) (by simpa only [blockSum_one] using cell_7_433) (by norm_num)

theorem sum_7_434_2 : (23031356450691 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 434 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_434) (by simpa only [blockSum_one] using cell_7_435) (by norm_num)

theorem sum_7_432_4 : (522119820197 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 432 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_432_2 sum_7_434_2 (by norm_num)

theorem sum_7_436_2 : (18171378433389 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 436 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_436) (by simpa only [blockSum_one] using cell_7_437) (by norm_num)

theorem sum_7_438_2 : (28663630409097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 438 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_438) (by simpa only [blockSum_one] using cell_7_439) (by norm_num)

theorem sum_7_436_4 : (520051098207 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 436 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_436_2 sum_7_438_2 (by norm_num)

theorem sum_7_432_8 : (6777214052611 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 432 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_432_4 sum_7_436_4 (by norm_num)

theorem sum_7_440_2 : (282488660253 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 440 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_440) (by simpa only [blockSum_one] using cell_7_441) (by norm_num)

theorem sum_7_442_2 : (8905715113691 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 442 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_442) (by simpa only [blockSum_one] using cell_7_443) (by norm_num)

theorem sum_7_440_4 : (20205261523811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 440 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_440_2 sum_7_442_2 (by norm_num)

theorem sum_7_444_2 : (175414724979 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 444 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_444) (by simpa only [blockSum_one] using cell_7_445) (by norm_num)

theorem sum_7_446_2 : (2763148269877 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 446 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_446) (by simpa only [blockSum_one] using cell_7_447) (by norm_num)

theorem sum_7_444_4 : (6271442769457 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 444 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_444_2 sum_7_446_2 (by norm_num)

theorem sum_7_440_8 : (1309925882509 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 440 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_440_4 sum_7_444_4 (by norm_num)

theorem sum_7_432_16 : (9397065817629 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 432 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_432_8 sum_7_440_8 (by norm_num)

theorem sum_7_416_32 : (892424340226041 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 416 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_416_16 sum_7_432_16 (by norm_num)

#print axioms sum_7_416_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
