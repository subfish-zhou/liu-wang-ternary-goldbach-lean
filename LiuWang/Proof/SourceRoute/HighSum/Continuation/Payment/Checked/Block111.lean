import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_480_0 : expNegUpper (16917187984383741981041 / 152711281184936464000 : ℝ) ≤ (193958327471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2376099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_480_1 : expNegUpper (541947415378379407812271 / 4886760997917966848000 : ℝ) ≤ (343278431431 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2378369 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_480 : rowCell 6 480 ≤ (106638805263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (193958327471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (343278431431 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_480_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_480_1
  · norm_num [gridPoint]

theorem exp_6_481_0 : expNegUpper (543605571385234786822439 / 4901712654138757632000 : ℝ) ≤ (137311368799 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2378369 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_481_1 : expNegUpper (54420515183974394864107 / 490171265413875763200 : ℝ) ≤ (75938733597 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2380643 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_481 : rowCell 6 481 ≤ (47182253667 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (137311368799 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (75938733597 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_481_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_481_1
  · norm_num [gridPoint]

theorem exp_6_482_0 : expNegUpper (54586767233019787136027 / 491668714866530355200 : ℝ) ≤ (607509852183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2380643 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_482_1 : expNegUpper (546469436691896079488261 / 4916687148665303552000 : ℝ) ≤ (268762736633 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2382921 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_482 : rowCell 6 482 ≤ (3339880187 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (607509852183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (268762736633 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_482_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_482_1
  · norm_num [gridPoint]

theorem exp_6_483_0 : expNegUpper (548136328327507643735869 / 4931684481497604608000 : ℝ) ≤ (537525458673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2382921 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_483_1 : expNegUpper (137185069981793611770727 / 1232921120374401152000 : ℝ) ≤ (47556928051 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2385201 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_483 : rowCell 6 483 ≤ (9234472323 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (537525458673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47556928051 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_483_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_483_1
  · norm_num [gridPoint]

theorem exp_6_484_0 : expNegUpper (177552112699839596993 / 1595711178269568000 : ℝ) ≤ (475569267677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2385201 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_484_1 : expNegUpper (710990569726345416973 / 6382844713078272000 : ℝ) ≤ (420724408163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1193743 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_484 : rowCell 6 484 ≤ (65358540107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (475569267677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (420724408163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_484_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_484_1
  · norm_num [gridPoint]

theorem exp_6_485_0 : expNegUpper (552693345448521838916627 / 4961747662079472128000 : ℝ) ≤ (210362198439 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1193743 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_485_1 : expNegUpper (276650840758232239715413 / 2480873831039736064000 : ℝ) ≤ (74435640561 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1194887 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_485 : rowCell 6 485 ≤ (57819169943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (210362198439 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (74435640561 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_485_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_485_1
  · norm_num [gridPoint]

theorem exp_6_486_0 : expNegUpper (14604782277813251452103 / 130968776574448384000 : ℝ) ≤ (372178192883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1194887 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_486_1 : expNegUpper (1169667915484533552931 / 10477502125955870720 : ℝ) ≤ (32921044937 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (478413 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_486 : rowCell 6 486 ≤ (51145889947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (372178192883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32921044937 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_486_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_486_1
  · norm_num [gridPoint]

theorem exp_6_487_0 : expNegUpper (22291068107479461847889 / 199676087835374407680 : ℝ) ≤ (41151305081 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (478413 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_487_1 : expNegUpper (69736179568290402439667 / 623987774485545024000 : ℝ) ≤ (291182907473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (59859 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_487 : rowCell 6 487 ≤ (4523964033 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (41151305081 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (291182907473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_487_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_487_1
  · norm_num [gridPoint]

theorem exp_6_488_0 : expNegUpper (69947285478888682337203 / 625876715030679616000 : ℝ) ≤ (291182899803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (59859 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_488_1 : expNegUpper (560193221582312471785223 / 5007013720245436928000 : ℝ) ≤ (64382506527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2396659 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_488 : rowCell 6 488 ≤ (20006319771 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (291182899803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64382506527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_488_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_488_1
  · norm_num [gridPoint]

theorem exp_6_489_0 : expNegUpper (22475459199264437576407 / 200885923316490752000 : ℝ) ≤ (128765009683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2396659 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_489_1 : expNegUpper (11250072499109196823499 / 100442961658245376000 : ℝ) ≤ (227750704751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2398961 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_489 : rowCell 6 489 ≤ (17693553199 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (128765009683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (227750704751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_489_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_489_1
  · norm_num [gridPoint]

theorem exp_6_490_0 : expNegUpper (282100650565414817531971 / 2518652641942427904000 : ℝ) ≤ (28468837353 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2398961 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_490_1 : expNegUpper (564820656658103974415581 / 5037305283884855808000 : ℝ) ≤ (201400983563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1200633 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_490 : rowCell 6 490 ≤ (15647063123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28468837353 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (201400983563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_490_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_490_1
  · norm_num [gridPoint]

theorem exp_6_491_0 : expNegUpper (566522757271104192387989 / 5052485323163197952000 : ℝ) ≤ (100700489177 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1200633 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_491_1 : expNegUpper (28357216334129175911809 / 252624266158159897600 : ℝ) ≤ (35617511697 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (96143 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_491 : rowCell 6 491 ≤ (13836322527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (100700489177 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35617511697 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_491_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_491_1
  · norm_num [gridPoint]

theorem exp_6_492_0 : expNegUpper (28442542919738662905569 / 253384410037364761600 : ℝ) ≤ (178087553907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (96143 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_492_1 : expNegUpper (569474645021237119365811 / 5067688200747295232000 : ℝ) ≤ (157462028629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (37592 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_492 : rowCell 6 492 ≤ (24468577029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (178087553907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (157462028629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_492_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_492_1
  · norm_num [gridPoint]

theorem exp_6_493_0 : expNegUpper (571185614494175478963179 / 5082913916637147648000 : ℝ) ≤ (31492404921 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (37592 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_493_1 : expNegUpper (285905810833201712266769 / 2541456958318573824000 : ℝ) ≤ (139215793709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (602051 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_493 : rowCell 6 493 ≤ (10817006529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31492404921 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (139215793709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_493_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_493_1
  · norm_num [gridPoint]

theorem exp_6_494_0 : expNegUpper (11470540711232990033449 / 101963249416655104000 : ℝ) ≤ (139215790173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (602051 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_494_1 : expNegUpper (22966210664416843218737 / 203926498833310208000 : ℝ) ≤ (123075528453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2410523 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_494 : rowCell 6 494 ≤ (19126518607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (139215790173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (123075528453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_494_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_494_1
  · norm_num [gridPoint]

theorem exp_6_495_0 : expNegUpper (575875131589533972968257 / 5113433863334117888000 : ℝ) ≤ (24615105069 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2410523 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_495_1 : expNegUpper (36031599365351795868721 / 319589616458382368000 : ℝ) ≤ (108799169067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1206423 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_495 : rowCell 6 495 ≤ (8454255521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24615105069 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (108799169067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_495_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_495_1
  · norm_num [gridPoint]

theorem exp_6_496_0 : expNegUpper (36139369535635471223729 / 320545505883827232000 : ℝ) ≤ (849993487 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1206423 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_496_1 : expNegUpper (115772520272873006311187 / 1025745618828247142400 : ℝ) ≤ (96172354143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2415173 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_496 : rowCell 6 496 ≤ (3736676857 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (849993487 / 7812500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (96172354143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_496_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_496_1
  · norm_num [gridPoint]

theorem exp_6_497_0 : expNegUpper (116118277699177769647147 / 1028809032650821734400 : ℝ) ≤ (375673249 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2415173 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_497_1 : expNegUpper (290613155579484310083343 / 2572022581627054336000 : ℝ) ≤ (42502634401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2417503 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_497 : rowCell 6 497 ≤ (13211634867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (375673249 / 3906250000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42502634401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_497_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_497_1
  · norm_num [gridPoint]

theorem exp_6_498_0 : expNegUpper (291479784679518272832767 / 2579692535336368384000 : ℝ) ≤ (42502633347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2417503 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_498_1 : expNegUpper (583596729221778146460853 / 5159385070672736768000 : ℝ) ≤ (75129846623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (604959 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_498 : rowCell 6 498 ≤ (2335439267 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42502633347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (75129846623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_498_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_498_1
  · norm_num [gridPoint]

theorem exp_6_499_0 : expNegUpper (936535144243118845757 / 8279596506235392000 : ℝ) ≤ (7512984477 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (604959 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_499_1 : expNegUpper (234389546218052902867 / 2069899126558848000 : ℝ) ≤ (13279457801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1211087 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_499 : rowCell 6 499 ≤ (10320285749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7512984477 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13279457801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_499_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_499_1
  · norm_num [gridPoint]

theorem exp_6_500_0 : expNegUpper (146929021466741423440643 / 1297533350106814592000 : ℝ) ≤ (66397287377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1211087 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_500_1 : expNegUpper (588357730121369599015691 / 5190133400427258368000 : ℝ) ≤ (14668966531 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1212257 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_500 : rowCell 6 500 ≤ (2280111681 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (66397287377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14668966531 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_500_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_500_1
  · norm_num [gridPoint]

theorem exp_6_501_0 : expNegUpper (590104441496424437887939 / 5205541822763151872000 : ℝ) ≤ (11735172939 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1212257 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_501_1 : expNegUpper (59074833294282881873449 / 520554182276315187200 : ℝ) ≤ (51848967691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1213429 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_501 : rowCell 6 501 ≤ (4029785039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11735172939 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51848967691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_501_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_501_1
  · norm_num [gridPoint]

theorem exp_6_502_0 : expNegUpper (59249954203266415770329 / 522097308340480051200 : ℝ) ≤ (12962241609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1213429 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_502_1 : expNegUpper (593145684001848563052961 / 5220973083404800512000 : ℝ) ≤ (45813375261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1214603 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_502 : rowCell 6 502 ≤ (7121625701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12962241609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45813375261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_502_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_502_1
  · norm_num [gridPoint]

theorem exp_6_503_0 : expNegUpper (594901397468023499937689 / 5236427182352204288000 : ℝ) ≤ (22906687079 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1214603 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_503_1 : expNegUpper (74443724161345934837521 / 654553397794025536000 : ℝ) ≤ (40477731047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2431557 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_503 : rowCell 6 503 ≤ (6292424919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22906687079 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40477731047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_503_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_503_1
  · norm_num [gridPoint]

theorem exp_6_504_0 : expNegUpper (2986550088974205556601 / 26259520598026816000 : ℝ) ≤ (20238865039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2431557 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_504_1 : expNegUpper (23918426832076968496207 / 210076164784214528000 : ℝ) ≤ (8940295249 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2433911 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_504 : rowCell 6 504 ≤ (1389852473 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20238865039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8940295249 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_504_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_504_1
  · norm_num [gridPoint]

theorem exp_6_505_0 : expNegUpper (31564495421339770451573 / 277231783956014592000 : ℝ) ≤ (7152236029 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2433911 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_505_1 : expNegUpper (15799429645464668707817 / 138615891978007296000 : ℝ) ≤ (7898043097 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (243627 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_505 : rowCell 6 505 ≤ (245573349 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7152236029 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7898043097 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_505_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_505_1
  · norm_num [gridPoint]

theorem exp_6_506_0 : expNegUpper (301073796546102864222907 / 2641463254514473216000 : ℝ) ≤ (15796085821 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (243627 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_506_1 : expNegUpper (120560554092061144180969 / 1056585301805789286400 : ℝ) ≤ (27907388451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2438631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_506 : rowCell 6 506 ≤ (4338761379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15796085821 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27907388451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_506_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_506_1
  · norm_num [gridPoint]

theorem exp_6_507_0 : expNegUpper (120915313609486005529409 / 1059694392239874150400 : ℝ) ≤ (5581477559 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2438631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_507_1 : expNegUpper (151308503148051947289409 / 1324617990299842688000 : ℝ) ≤ (493016089 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (610249 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_507 : rowCell 6 507 ≤ (3832590599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5581477559 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (493016089 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_507_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_507_1
  · norm_num [gridPoint]

theorem exp_6_508_0 : expNegUpper (151753086965866795728161 / 1328510062918887552000 : ℝ) ≤ (24650803873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (610249 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_508_1 : expNegUpper (607672062915702262384483 / 5314040251675550208000 : ℝ) ≤ (4354570293 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (488673 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_508 : rowCell 6 508 ≤ (13223651 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24650803873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4354570293 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_508_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_508_1
  · norm_num [gridPoint]

theorem exp_6_509_0 : expNegUpper (24378197701306233638867 / 213185255218299392000 : ℝ) ≤ (21772850959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (488673 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_509_1 : expNegUpper (12202338628462555746289 / 106592627609149696000 : ℝ) ≤ (3845935129 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2445737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_509 : rowCell 6 509 ≤ (2989941079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21772850959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3845935129 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_509_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_509_1
  · norm_num [gridPoint]

theorem exp_6_510_0 : expNegUpper (305952181023667324276601 / 2672622673772587264000 : ℝ) ≤ (12018547 / 625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2445737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_510_1 : expNegUpper (612568628106823010676601 / 5345245347545174528000 : ℝ) ≤ (16982482059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2448113 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_510 : rowCell 6 510 ≤ (1320311521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12018547 / 625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16982482059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_510_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_510_1
  · norm_num [gridPoint]

theorem exp_6_511_0 : expNegUpper (614360616399842252386289 / 5360882152938619392000 : ℝ) ≤ (16982481669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2448113 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_511_1 : expNegUpper (1201224927654544100 / 10470472954958241 : ℝ) ≤ (374923839 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (612623 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_511 : rowCell 6 511 ≤ (2331969149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16982481669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (374923839 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_511_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_511_1
  · norm_num [gridPoint]

theorem sum_6_480_2 : blockSum (rowCell 6) 480 2 ≤ (201003312597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_480) (by simpa only [blockSum_one] using cell_6_481) (by norm_num)

theorem sum_6_482_2 : blockSum (rowCell 6) 482 2 ≤ (157372783259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_482) (by simpa only [blockSum_one] using cell_6_483) (by norm_num)

theorem sum_6_480_4 : blockSum (rowCell 6) 480 4 ≤ (22398505991 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_480_2 sum_6_482_2 (by norm_num)

theorem sum_6_484_2 : blockSum (rowCell 6) 484 2 ≤ (2463554201 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_484) (by simpa only [blockSum_one] using cell_6_485) (by norm_num)

theorem sum_6_486_2 : blockSum (rowCell 6) 486 2 ≤ (96385530277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_486) (by simpa only [blockSum_one] using cell_6_487) (by norm_num)

theorem sum_6_484_4 : blockSum (rowCell 6) 484 4 ≤ (219563240327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_484_2 sum_6_486_2 (by norm_num)

theorem sum_6_480_8 : blockSum (rowCell 6) 480 8 ≤ (577939336183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_480_4 sum_6_484_4 (by norm_num)

theorem sum_6_488_2 : blockSum (rowCell 6) 488 2 ≤ (3769987297 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_488) (by simpa only [blockSum_one] using cell_6_489) (by norm_num)

theorem sum_6_490_2 : blockSum (rowCell 6) 490 2 ≤ (589667713 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_490) (by simpa only [blockSum_one] using cell_6_491) (by norm_num)

theorem sum_6_488_4 : blockSum (rowCell 6) 488 4 ≤ (3359162931 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_488_2 sum_6_490_2 (by norm_num)

theorem sum_6_492_2 : blockSum (rowCell 6) 492 2 ≤ (46102590087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_492) (by simpa only [blockSum_one] using cell_6_493) (by norm_num)

theorem sum_6_494_2 : blockSum (rowCell 6) 494 2 ≤ (36035029649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_494) (by simpa only [blockSum_one] using cell_6_495) (by norm_num)

theorem sum_6_492_4 : blockSum (rowCell 6) 492 4 ≤ (10267202467 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_492_2 sum_6_494_2 (by norm_num)

theorem sum_6_488_8 : blockSum (rowCell 6) 488 8 ≤ (13531508561 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_488_4 sum_6_492_4 (by norm_num)

theorem sum_6_480_16 : blockSum (rowCell 6) 480 16 ≤ (794443473159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_480_8 sum_6_488_8 (by norm_num)

theorem sum_6_496_2 : blockSum (rowCell 6) 496 2 ≤ (5631668459 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_496) (by simpa only [blockSum_one] using cell_6_497) (by norm_num)

theorem sum_6_498_2 : blockSum (rowCell 6) 498 2 ≤ (5499370521 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_498) (by simpa only [blockSum_one] using cell_6_499) (by norm_num)

theorem sum_6_496_4 : blockSum (rowCell 6) 496 4 ≤ (50155824379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_496_2 sum_6_498_2 (by norm_num)

theorem sum_6_500_2 : blockSum (rowCell 6) 500 2 ≤ (8590008401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_500) (by simpa only [blockSum_one] using cell_6_501) (by norm_num)

theorem sum_6_502_2 : blockSum (rowCell 6) 502 2 ≤ (670702531 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_502) (by simpa only [blockSum_one] using cell_6_503) (by norm_num)

theorem sum_6_500_4 : blockSum (rowCell 6) 500 4 ≤ (15297033711 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_500_2 sum_6_502_2 (by norm_num)

theorem sum_6_496_8 : blockSum (rowCell 6) 496 8 ≤ (80749891801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_496_4 sum_6_500_4 (by norm_num)

theorem sum_6_504_2 : blockSum (rowCell 6) 504 2 ≤ (1308859609 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_504) (by simpa only [blockSum_one] using cell_6_505) (by norm_num)

theorem sum_6_506_2 : blockSum (rowCell 6) 506 2 ≤ (4085675989 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_506) (by simpa only [blockSum_one] using cell_6_507) (by norm_num)

theorem sum_6_504_4 : blockSum (rowCell 6) 504 4 ≤ (372844577 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_504_2 sum_6_506_2 (by norm_num)

theorem sum_6_508_2 : blockSum (rowCell 6) 508 2 ≤ (1275039147 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_508) (by simpa only [blockSum_one] using cell_6_509) (by norm_num)

theorem sum_6_510_2 : blockSum (rowCell 6) 510 2 ≤ (4972592191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_510) (by simpa only [blockSum_one] using cell_6_511) (by norm_num)

theorem sum_6_508_4 : blockSum (rowCell 6) 508 4 ≤ (5673893963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_508_2 sum_6_510_2 (by norm_num)

theorem sum_6_504_8 : blockSum (rowCell 6) 504 8 ≤ (3748752097 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_504_4 sum_6_508_4 (by norm_num)

theorem sum_6_496_16 : blockSum (rowCell 6) 496 16 ≤ (110739908577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_496_8 sum_6_504_8 (by norm_num)

theorem sum_6_480_32 : blockSum (rowCell 6) 480 32 ≤ (113147922717 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_480_16 sum_6_496_16 (by norm_num)

#print axioms sum_6_480_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
