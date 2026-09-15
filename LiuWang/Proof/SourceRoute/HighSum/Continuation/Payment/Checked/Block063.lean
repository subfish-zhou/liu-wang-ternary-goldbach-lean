import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_480_0 : expNegUpper (16793043043819261981041 / 152711281184936464000 : ℝ) ≤ (874567437703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (73783 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_480_1 : expNegUpper (537980845392249487812271 / 4886760997917966848000 : ℝ) ≤ (772969061339 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (472667 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_480 : rowCell 3 480 ≤ (120139841719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (874567437703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (772969061339 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_480_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_480_1
  · norm_num [gridPoint]

theorem exp_3_481_0 : expNegUpper (59958540575026442980271 / 544634739348750848000 : ℝ) ≤ (1545938082429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (472667 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_481_1 : expNegUpper (6002583486018673207123 / 54463473934875084800 : ℝ) ≤ (273250704103 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2365617 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_481 : rowCell 3 481 ≤ (212359628109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1545938082429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (273250704103 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_481_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_481_1
  · norm_num [gridPoint]

theorem exp_3_482_0 : expNegUpper (54188289800826763136027 / 491668714866530355200 : ℝ) ≤ (1366253485161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2365617 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_482_1 : expNegUpper (542490730481899279488261 / 4916687148665303552000 : ℝ) ≤ (1207371741421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2367903 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_482 : rowCell 3 482 ≤ (46917765941 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1366253485161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1207371741421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_482_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_482_1
  · norm_num [gridPoint]

theorem exp_3_483_0 : expNegUpper (544145485893643963735869 / 4931684481497604608000 : ℝ) ≤ (37730365949 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2367903 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_483_1 : expNegUpper (136188876401311051770727 / 1232921120374401152000 : ℝ) ≤ (53344713197 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (148137 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_483 : rowCell 3 483 ≤ (165841518133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (37730365949 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (53344713197 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_483_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_483_1
  · norm_num [gridPoint]

theorem exp_3_484_0 : expNegUpper (19584754079702710777 / 177301242029952000 : ℝ) ≤ (533447118333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (148137 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_484_1 : expNegUpper (78426788402014912997 / 709204968119808000 : ℝ) ≤ (58918619799 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (474497 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_484 : rowCell 3 484 ≤ (146541265323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (533447118333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (58918619799 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_484_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_484_1
  · norm_num [gridPoint]

theorem exp_3_485_0 : expNegUpper (548690366790791278916627 / 4961747662079472128000 : ℝ) ≤ (29459309151 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (474497 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_485_1 : expNegUpper (274652385485333679715413 / 2480873831039736064000 : ℝ) ≤ (4164517061 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2374781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_485 : rowCell 3 485 ≤ (12947844243 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29459309151 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4164517061 / 5000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_485_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_485_1
  · norm_num [gridPoint]

theorem exp_3_486_0 : expNegUpper (275486339893619777589957 / 2488406754914519296000 : ℝ) ≤ (166580678233 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2374781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_486_1 : expNegUpper (22063571247896915105689 / 199072540393161543680 : ℝ) ≤ (183961864521 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2377081 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_486 : rowCell 3 486 ≤ (14299340169 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (166580678233 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (183961864521 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_486_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_486_1
  · norm_num [gridPoint]

theorem exp_3_487_0 : expNegUpper (2458940390246173805321 / 22186231981708267520 : ℝ) ≤ (735847439613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2377081 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_487_1 : expNegUpper (7692783191342489159963 / 69331974942838336000 : ℝ) ≤ (650058043907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (297423 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_487 : rowCell 3 487 ≤ (6316342063 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (735847439613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (650058043907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_487_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_487_1
  · norm_num [gridPoint]

theorem exp_3_488_0 : expNegUpper (69444637604697322337203 / 625876715030679616000 : ℝ) ≤ (81257253461 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (297423 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_488_1 : expNegUpper (556178106700715031785223 / 5007013720245436928000 : ℝ) ≤ (287116270523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2381691 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_488 : rowCell 3 488 ≤ (89276368221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (81257253461 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (287116270523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_488_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_488_1
  · norm_num [gridPoint]

theorem exp_3_489_0 : expNegUpper (22314369155045864776407 / 200885923316490752000 : ℝ) ≤ (143558131701 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2381691 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_489_1 : expNegUpper (11169648839238579223499 / 100442961658245376000 : ℝ) ≤ (507218298629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2384001 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_489 : rowCell 3 489 ≤ (78860365807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (143558131701 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (507218298629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_489_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_489_1
  · norm_num [gridPoint]

theorem exp_3_490_0 : expNegUpper (31120443439635104170219 / 279850293549158656000 : ℝ) ≤ (4057746289 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2384001 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_490_1 : expNegUpper (62310378394737739379509 / 559700587098317312000 : ℝ) ≤ (223997725961 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (477263 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_490 : rowCell 3 490 ≤ (69655043979 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4057746289 / 8000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (223997725961 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_490_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_490_1
  · norm_num [gridPoint]

theorem exp_3_491_0 : expNegUpper (562483369941772992387989 / 5052485323163197952000 : ℝ) ≤ (89599088189 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (477263 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_491_1 : expNegUpper (28155550373259287911809 / 252624266158159897600 : ℝ) ≤ (15826467689 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (298579 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_491 : rowCell 3 491 ≤ (15380059031 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (89599088189 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15826467689 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_491_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_491_1
  · norm_num [gridPoint]

theorem exp_3_492_0 : expNegUpper (28240270147675430905569 / 253384410037364761600 : ℝ) ≤ (395661682589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (298579 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_492_1 : expNegUpper (565435257691905919365811 / 5067688200747295232000 : ℝ) ≤ (174709387781 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (298869 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_492 : rowCell 3 492 ≤ (54331936417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (395661682589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (174709387781 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_492_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_492_1
  · norm_num [gridPoint]

theorem exp_3_493_0 : expNegUpper (63014898993441933218131 / 564768212959683072000 : ℝ) ≤ (174709383551 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (298869 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_493_1 : expNegUpper (31542564790285488029641 / 282384106479841536000 : ℝ) ≤ (4821258947 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (598319 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_493 : rowCell 3 493 ≤ (9596088921 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (174709383551 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4821258947 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_493_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_493_1
  · norm_num [gridPoint]

theorem exp_3_494_0 : expNegUpper (11389388877930359633449 / 101963249416655104000 : ℝ) ≤ (308560565181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (598319 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_494_1 : expNegUpper (22804149722288920018737 / 203926498833310208000 : ℝ) ≤ (272462484651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (598901 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_494 : rowCell 3 494 ≤ (42368722807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (308560565181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (272462484651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_494_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_494_1
  · norm_num [gridPoint]

theorem exp_3_495_0 : expNegUpper (571811471812469012968257 / 5113433863334117888000 : ℝ) ≤ (272462478133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (598901 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_495_1 : expNegUpper (35777999886281075868721 / 319589616458382368000 : ℝ) ≤ (30071508771 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (479587 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_495 : rowCell 3 495 ≤ (1169091881 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (272462478133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (30071508771 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_495_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_495_1
  · norm_num [gridPoint]

theorem exp_3_496_0 : expNegUpper (3987223504730341247081 / 35616167320425248000 : ℝ) ≤ (240572064447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (479587 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_496_1 : expNegUpper (12773309813051112701243 / 113971735425360793600 : ℝ) ≤ (106200372099 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2400269 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_496 : rowCell 3 496 ≤ (1321247367 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (240572064447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (106200372099 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_496_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_496_1
  · norm_num [gridPoint]

theorem exp_3_497_0 : expNegUpper (115303118498991401647147 / 1028809032650821734400 : ℝ) ≤ (212400739177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2400269 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_497_1 : expNegUpper (288578291634985110083343 / 2572022581627054336000 : ℝ) ≤ (93758214167 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2402607 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_497 : rowCell 3 497 ≤ (7290579789 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (212400739177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (93758214167 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_497_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_497_1
  · norm_num [gridPoint]

theorem exp_3_498_0 : expNegUpper (289438852623085632832767 / 2579692535336368384000 : ℝ) ≤ (23439552991 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2402607 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_498_1 : expNegUpper (579520933220846306460853 / 5159385070672736768000 : ℝ) ≤ (41384260737 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (601237 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_498 : rowCell 3 498 ≤ (12872488001 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23439552991 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41384260737 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_498_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_498_1
  · norm_num [gridPoint]

theorem exp_3_499_0 : expNegUpper (103332716964826765973 / 919955167359488000 : ℝ) ≤ (165537039081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (601237 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_499_1 : expNegUpper (25861866730322976763 / 229988791839872000 : ℝ) ≤ (146124745609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2407293 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_499 : rowCell 3 499 ≤ (22726657349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (165537039081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (146124745609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_499_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_499_1
  · norm_num [gridPoint]

theorem exp_3_500_0 : expNegUpper (145905521382558383440643 / 1297533350106814592000 : ℝ) ≤ (18265592777 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2407293 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_500_1 : expNegUpper (584269797896570879015691 / 5190133400427258368000 : ℝ) ≤ (12898083053 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2409641 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_500 : rowCell 3 500 ≤ (2006094553 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18265592777 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12898083053 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_500_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_500_1
  · norm_num [gridPoint]

theorem exp_3_501_0 : expNegUpper (586004373047758837887939 / 5205541822763151872000 : ℝ) ≤ (4030650861 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2409641 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_501_1 : expNegUpper (58665433260609665873449 / 520554182276315187200 : ℝ) ≤ (22768242707 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2411993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_501 : rowCell 3 501 ≤ (17706801397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4030650861 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22768242707 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_501_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_501_1
  · norm_num [gridPoint]

theorem exp_3_502_0 : expNegUpper (6537704505245167974481 / 58010812037831116800 : ℝ) ≤ (56920605461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2411993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_502_1 : expNegUpper (65449512839242551450329 / 580108120378311168000 : ℝ) ≤ (100472435667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (603587 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_502 : rowCell 3 502 ≤ (15627943657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (56920605461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (100472435667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_502_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_502_1
  · norm_num [gridPoint]

theorem exp_3_503_0 : expNegUpper (590789192795491019937689 / 5236427182352204288000 : ℝ) ≤ (803779467 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (603587 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_503_1 : expNegUpper (73930457091271054837521 / 654553397794025536000 : ℝ) ≤ (8866812611 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1208353 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_503 : rowCell 3 503 ≤ (13792299529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (803779467 / 8000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8866812611 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_503_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_503_1
  · norm_num [gridPoint]

theorem exp_3_504_0 : expNegUpper (2965958725051875956601 / 26259520598026816000 : ℝ) ≤ (88668124099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1208353 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_504_1 : expNegUpper (23753938645175669296207 / 210076164784214528000 : ℝ) ≤ (78245871881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (604767 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_504 : rowCell 3 504 ≤ (12171518549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (88668124099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (78245871881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_504_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_504_1
  · norm_num [gridPoint]

theorem exp_3_505_0 : expNegUpper (66177896901006253175543 / 585267099462697472000 : ℝ) ≤ (78245870117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (604767 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_505_1 : expNegUpper (33125558541288416160947 / 292633549731348736000 : ℝ) ≤ (4315277983 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1210717 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_505 : rowCell 3 505 ≤ (10740542309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (78245870117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4315277983 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_505_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_505_1
  · norm_num [gridPoint]

theorem exp_3_506_0 : expNegUpper (299008592041936464222907 / 2641463254514473216000 : ℝ) ≤ (3452222309 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1210717 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_506_1 : expNegUpper (119735685912781272180969 / 1056585301805789286400 : ℝ) ≤ (60921364961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2423803 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_506 : rowCell 3 506 ≤ (1895444743 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3452222309 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (60921364961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_506_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_506_1
  · norm_num [gridPoint]

theorem exp_3_507_0 : expNegUpper (120088018185432757529409 / 1059694392239874150400 : ℝ) ≤ (15230340901 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2423803 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_507_1 : expNegUpper (150275900895968747289409 / 1324617990299842688000 : ℝ) ≤ (53750702669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (97047 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_507 : rowCell 3 507 ≤ (8361990099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15230340901 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (53750702669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_507_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_507_1
  · norm_num [gridPoint]

theorem exp_3_508_0 : expNegUpper (16746383406424097303129 / 147612229213209728000 : ℝ) ≤ (53750701479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (97047 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_508_1 : expNegUpper (67059509532826224709387 / 590448916852838912000 : ℝ) ≤ (23710594463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2428551 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_508 : rowCell 3 508 ≤ (1475509029 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (53750701479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23710594463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_508_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_508_1
  · norm_num [gridPoint]

theorem exp_3_509_0 : expNegUpper (24212253167540908838867 / 213185255218299392000 : ℝ) ≤ (23710593941 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2428551 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_509_1 : expNegUpper (12119487723818562146289 / 106592627609149696000 : ℝ) ≤ (8366900659 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2430931 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_509 : rowCell 3 509 ≤ (813575649 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23710593941 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8366900659 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_509_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_509_1
  · norm_num [gridPoint]

theorem exp_3_510_0 : expNegUpper (303874840295634044276601 / 2672622673772587264000 : ℝ) ≤ (41834502379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2430931 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_510_1 : expNegUpper (608420014762689890676601 / 5345245347545174528000 : ℝ) ≤ (36903775239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2433313 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_510 : rowCell 3 510 ≤ (2870832973 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (41834502379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36903775239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_510_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_510_1
  · norm_num [gridPoint]

theorem exp_3_511_0 : expNegUpper (67799985203538028042921 / 595653572548735488000 : ℝ) ≤ (9225943609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2433313 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_511_1 : expNegUpper (132567812826184900 / 1163385883884249 : ℝ) ≤ (16276127947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (24357 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_511 : rowCell 3 511 ≤ (2532398067 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9225943609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16276127947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_511_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_511_1
  · norm_num [gridPoint]

theorem sum_3_480_2 : blockSum (rowCell 3) 480 2 ≤ (452639311547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_480) (by simpa only [blockSum_one] using cell_3_481) (by norm_num)

theorem sum_3_482_2 : blockSum (rowCell 3) 482 2 ≤ (353512581897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_482) (by simpa only [blockSum_one] using cell_3_483) (by norm_num)

theorem sum_3_480_4 : blockSum (rowCell 3) 480 4 ≤ (201537973361 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_480_2 sum_3_482_2 (by norm_num)

theorem sum_3_484_2 : blockSum (rowCell 3) 484 2 ≤ (276019707753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_484) (by simpa only [blockSum_one] using cell_3_485) (by norm_num)

theorem sum_3_486_2 : blockSum (rowCell 3) 486 2 ≤ (5386404859 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_486) (by simpa only [blockSum_one] using cell_3_487) (by norm_num)

theorem sum_3_484_4 : blockSum (rowCell 3) 484 4 ≤ (491475902113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_484_2 sum_3_486_2 (by norm_num)

theorem sum_3_480_8 : blockSum (rowCell 3) 480 8 ≤ (1297627795557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_480_4 sum_3_484_4 (by norm_num)

theorem sum_3_488_2 : blockSum (rowCell 3) 488 2 ≤ (42034183507 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_488) (by simpa only [blockSum_one] using cell_3_489) (by norm_num)

theorem sum_3_490_2 : blockSum (rowCell 3) 490 2 ≤ (131175280103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_490) (by simpa only [blockSum_one] using cell_3_491) (by norm_num)

theorem sum_3_488_4 : blockSum (rowCell 3) 488 4 ≤ (299312014131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_488_2 sum_3_490_2 (by norm_num)

theorem sum_3_492_2 : blockSum (rowCell 3) 492 2 ≤ (51156190511 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_492) (by simpa only [blockSum_one] using cell_3_493) (by norm_num)

theorem sum_3_494_2 : blockSum (rowCell 3) 494 2 ≤ (79779662999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_494) (by simpa only [blockSum_one] using cell_3_495) (by norm_num)

theorem sum_3_492_4 : blockSum (rowCell 3) 492 4 ≤ (182092044021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_492_2 sum_3_494_2 (by norm_num)

theorem sum_3_488_8 : blockSum (rowCell 3) 488 8 ≤ (60175507269 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_488_4 sum_3_492_4 (by norm_num)

theorem sum_3_480_16 : blockSum (rowCell 3) 480 16 ≤ (1779031853709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_480_8 sum_3_488_8 (by norm_num)

theorem sum_3_496_2 : blockSum (rowCell 3) 496 2 ≤ (62193503331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_496) (by simpa only [blockSum_one] using cell_3_497) (by norm_num)

theorem sum_3_498_2 : blockSum (rowCell 3) 498 2 ≤ (48471633351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_498) (by simpa only [blockSum_one] using cell_3_499) (by norm_num)

theorem sum_3_496_4 : blockSum (rowCell 3) 496 4 ≤ (55332568341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_496_2 sum_3_498_2 (by norm_num)

theorem sum_3_500_2 : blockSum (rowCell 3) 500 2 ≤ (37767746927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_500) (by simpa only [blockSum_one] using cell_3_501) (by norm_num)

theorem sum_3_502_2 : blockSum (rowCell 3) 502 2 ≤ (14710121593 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_502) (by simpa only [blockSum_one] using cell_3_503) (by norm_num)

theorem sum_3_500_4 : blockSum (rowCell 3) 500 4 ≤ (67187990113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_500_2 sum_3_502_2 (by norm_num)

theorem sum_3_496_8 : blockSum (rowCell 3) 496 8 ≤ (35570625359 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_496_4 sum_3_500_4 (by norm_num)

theorem sum_3_504_2 : blockSum (rowCell 3) 504 2 ≤ (11456030429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_504) (by simpa only [blockSum_one] using cell_3_505) (by norm_num)

theorem sum_3_506_2 : blockSum (rowCell 3) 506 2 ≤ (8919606907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_506) (by simpa only [blockSum_one] using cell_3_507) (by norm_num)

theorem sum_3_504_4 : blockSum (rowCell 3) 504 4 ≤ (2546954667 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_504_2 sum_3_506_2 (by norm_num)

theorem sum_3_508_2 : blockSum (rowCell 3) 508 2 ≤ (13886150337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_508) (by simpa only [blockSum_one] using cell_3_509) (by norm_num)

theorem sum_3_510_2 : blockSum (rowCell 3) 510 2 ≤ (16885097 / 1562500000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_510) (by simpa only [blockSum_one] using cell_3_511) (by norm_num)

theorem sum_3_508_4 : blockSum (rowCell 3) 508 4 ≤ (24692612417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_508_2 sum_3_510_2 (by norm_num)

theorem sum_3_504_8 : blockSum (rowCell 3) 504 8 ≤ (65443887089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_504_4 sum_3_508_4 (by norm_num)

theorem sum_3_496_16 : blockSum (rowCell 3) 496 16 ≤ (60824253471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_496_8 sum_3_504_8 (by norm_num)

theorem sum_3_480_32 : blockSum (rowCell 3) 480 32 ≤ (2022328867593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_480_16 sum_3_496_16 (by norm_num)

#print axioms sum_3_480_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
