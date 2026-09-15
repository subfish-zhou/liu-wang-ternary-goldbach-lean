import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_480_0 : expNegUpper (16644069115141885981041 / 152711281184936464000 : ℝ) ≤ (4639692005023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (234313 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_480_1 : expNegUpper (533220961408893583812271 / 4886760997917966848000 : ℝ) ≤ (255912109883 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2345419 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_480 : rowCell 2 480 ≤ (636911965059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4639692005023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (255912109883 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_480_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_480_1
  · norm_num [gridPoint]

theorem exp_2_481_0 : expNegUpper (25469162748725801277259 / 233414888292321792000 : ℝ) ≤ (4094593658631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2345419 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_481_1 : expNegUpper (2549834990590497888767 / 23341488829232179200 : ℝ) ≤ (144532273253 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2347711 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_481 : rowCell 2 481 ≤ (112413405759 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4094593658631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (144532273253 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_481_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_481_1
  · norm_num [gridPoint]

theorem exp_2_482_0 : expNegUpper (53710116882195134336027 / 491668714866530355200 : ℝ) ≤ (1806653372029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2347711 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_482_1 : expNegUpper (537716283029903119488261 / 4916687148665303552000 : ℝ) ≤ (3188389388279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2350007 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_482 : rowCell 2 482 ≤ (495985792869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1806653372029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3188389388279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_482_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_482_1
  · norm_num [gridPoint]

theorem exp_2_483_0 : expNegUpper (539356474973007547735869 / 4931684481497604608000 : ℝ) ≤ (1594194655871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2350007 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_483_1 : expNegUpper (134993444104731979770727 / 1232921120374401152000 : ℝ) ≤ (703315992579 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1176153 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_483 : rowCell 2 483 ≤ (437645949439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1594194655871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (703315992579 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_483_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_483_1
  · norm_num [gridPoint]

theorem exp_2_484_0 : expNegUpper (58238531846102052331 / 531903726089856000 : ℝ) ≤ (1406631951597 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1176153 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_484_1 : expNegUpper (233220575562760258991 / 2127614904359424000 : ℝ) ≤ (496423520387 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2354609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_484 : rowCell 2 484 ≤ (96535994231 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1406631951597 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (496423520387 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_484_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_484_1
  · norm_num [gridPoint]

theorem exp_2_485_0 : expNegUpper (543886792401514606916627 / 4961747662079472128000 : ℝ) ≤ (2482117543073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2354609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_485_1 : expNegUpper (272254239157855407715413 / 2480873831039736064000 : ℝ) ≤ (2189813301913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (471383 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_485 : rowCell 2 485 ≤ (68136278931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2482117543073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2189813301913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_485_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_485_1
  · norm_num [gridPoint]

theorem exp_2_486_0 : expNegUpper (273080911831821377589957 / 2488406754914519296000 : ℝ) ≤ (273726656287 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (471383 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_486_1 : expNegUpper (21871428272325848225689 / 199072540393161543680 : ℝ) ≤ (193181179273 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (294903 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_486 : rowCell 2 486 ≤ (7513815029 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (273726656287 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (193181179273 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_486_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_486_1
  · norm_num [gridPoint]

theorem exp_2_487_0 : expNegUpper (7312579332632962375963 / 66558695945124802560 : ℝ) ≤ (193181174747 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (294903 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_487_1 : expNegUpper (22877897235544267479889 / 207995924828515008000 : ℝ) ≤ (1704102238327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2361537 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_487 : rowCell 2 487 ≤ (132567057243 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (193181174747 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1704102238327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_487_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_487_1
  · norm_num [gridPoint]

theorem exp_2_488_0 : expNegUpper (9834494307952527191029 / 89410959290097088000 : ℝ) ≤ (1704102198643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2361537 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_488_1 : expNegUpper (78765709834685443397889 / 715287674320776704000 : ℝ) ≤ (75157048687 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2363853 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_488 : rowCell 2 488 ≤ (116937526819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1704102198643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (75157048687 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_488_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_488_1
  · norm_num [gridPoint]

theorem exp_2_489_0 : expNegUpper (22121061101983577416407 / 200885923316490752000 : ℝ) ≤ (751570469473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2363853 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_489_1 : expNegUpper (11073140447393838103499 / 100442961658245376000 : ℝ) ≤ (331449327159 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2366173 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_489 : rowCell 2 489 ≤ (103144359319 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (751570469473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (331449327159 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_489_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_489_1
  · norm_num [gridPoint]

theorem exp_2_490_0 : expNegUpper (92554666475425760510657 / 839550880647475968000 : ℝ) ≤ (331449319533 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2366173 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_490_1 : expNegUpper (185320234742027490138527 / 1679101761294951936000 : ℝ) ≤ (1169305591671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (148031 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_490 : rowCell 2 490 ≤ (181945142961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (331449319533 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1169305591671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_490_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_490_1
  · norm_num [gridPoint]

theorem exp_2_491_0 : expNegUpper (557636105146575552387989 / 5052485323163197952000 : ℝ) ≤ (1169305564929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (148031 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_491_1 : expNegUpper (27913551220215422311809 / 252624266158159897600 : ℝ) ≤ (1031222815619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1185411 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_491 : rowCell 2 491 ≤ (160464506547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1169305564929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1031222815619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_491_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_491_1
  · norm_num [gridPoint]

theorem exp_2_492_0 : expNegUpper (27997542821199552505569 / 253384410037364761600 : ℝ) ≤ (1031222792177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1185411 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_492_1 : expNegUpper (560587992896708479365811 / 5067688200747295232000 : ℝ) ≤ (28418472677 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (74161 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_492 : rowCell 2 492 ≤ (14151131041 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1031222792177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28418472677 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_492_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_492_1
  · norm_num [gridPoint]

theorem exp_2_493_0 : expNegUpper (187424087559046567654393 / 1694304638879049216000 : ℝ) ≤ (181878221023 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (74161 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_493_1 : expNegUpper (93818603282603536088923 / 847152319439524608000 : ℝ) ≤ (801904666243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (475097 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_493 : rowCell 2 493 ≤ (6239461257 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (181878221023 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (801904666243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_493_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_493_1
  · norm_num [gridPoint]

theorem exp_2_494_0 : expNegUpper (11292006677967203153449 / 101963249416655104000 : ℝ) ≤ (801904648231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (475097 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_494_1 : expNegUpper (22609676591735412178737 / 203926498833310208000 : ℝ) ≤ (141416053319 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1188911 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_494 : rowCell 2 494 ≤ (55018267859 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (801904648231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (141416053319 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_494_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_494_1
  · norm_num [gridPoint]

theorem exp_2_495_0 : expNegUpper (80990725725713008709751 / 730490551904873984000 : ℝ) ≤ (707080250807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1188911 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_495_1 : expNegUpper (5067668644485173124103 / 45655659494054624000 : ℝ) ≤ (311715761217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1190081 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_495 : rowCell 2 495 ≤ (97022113887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (707080250807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (311715761217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_495_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_495_1
  · norm_num [gridPoint]

theorem exp_2_496_0 : expNegUpper (11859927316966063741243 / 106848501961275744000 : ℝ) ≤ (623431508597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1190081 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_496_1 : expNegUpper (37994836656988141303729 / 341915206276082380800 : ℝ) ≤ (549645882017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (476501 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_496 : rowCell 2 496 ≤ (85541857261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (623431508597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (549645882017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_496_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_496_1
  · norm_num [gridPoint]

theorem exp_2_497_0 : expNegUpper (114324927458767760047147 / 1028809032650821734400 : ℝ) ≤ (54964586989 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (476501 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_497_1 : expNegUpper (286136454901586070083343 / 2572022581627054336000 : ℝ) ≤ (242282194907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (596213 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_497 : rowCell 2 497 ≤ (75415541311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (54964586989 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (242282194907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_497_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_497_1
  · norm_num [gridPoint]

theorem exp_2_498_0 : expNegUpper (286989734155366464832767 / 2579692535336368384000 : ℝ) ≤ (242282189593 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (596213 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_498_1 : expNegUpper (574629978019728098460853 / 5159385070672736768000 : ℝ) ≤ (427163780867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2387203 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_498 : rowCell 2 498 ≤ (33242018281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (242282189593 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (427163780867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_498_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_498_1
  · norm_num [gridPoint]

theorem exp_2_499_0 : expNegUpper (307381874270609117119 / 2759865502078464000 : ℝ) ≤ (85432754311 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2387203 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_499_1 : expNegUpper (76932501932910485489 / 689966375519616000 : ℝ) ≤ (47067581773 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (597389 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_499 : rowCell 2 499 ≤ (14651712201 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (85432754311 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47067581773 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_499_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_499_1
  · norm_num [gridPoint]

theorem exp_2_500_0 : expNegUpper (144677321281538735440643 / 1297533350106814592000 : ℝ) ≤ (47067580753 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (597389 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_500_1 : expNegUpper (579364279226812415015691 / 5190133400427258368000 : ℝ) ≤ (165948742397 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2391913 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_500 : rowCell 2 500 ≤ (51659944987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47067580753 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (165948742397 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_500_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_500_1
  · norm_num [gridPoint]

theorem exp_2_501_0 : expNegUpper (581084290909360117887939 / 5205541822763151872000 : ℝ) ≤ (82974369411 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2391913 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_501_1 : expNegUpper (58174153220201806673449 / 520554182276315187200 : ℝ) ≤ (292530261739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1197137 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_501 : rowCell 2 501 ≤ (22766915883 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (82974369411 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (292530261739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_501_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_501_1
  · norm_num [gridPoint]

theorem exp_2_502_0 : expNegUpper (2778409721901648903349 / 24861776587641907200 : ℝ) ≤ (146265127737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1197137 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_502_1 : expNegUpper (27815501591180202050141 / 248617765876419072000 : ℝ) ≤ (257817563789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1198319 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_502 : rowCell 2 502 ≤ (20065928717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (146265127737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (257817563789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_502_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_502_1
  · norm_num [gridPoint]

theorem exp_2_503_0 : expNegUpper (585854547188452043937689 / 5236427182352204288000 : ℝ) ≤ (257817558301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1198319 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_503_1 : expNegUpper (73314536607181198837521 / 654553397794025536000 : ℝ) ≤ (113605453183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (479801 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_503 : rowCell 2 503 ≤ (8842177853 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (257817558301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (113605453183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_503_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_503_1
  · norm_num [gridPoint]

theorem exp_2_504_0 : expNegUpper (2941249088345080436601 / 26259520598026816000 : ℝ) ≤ (227210901557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (479801 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_504_1 : expNegUpper (23556552820894110256207 / 210076164784214528000 : ℝ) ≤ (10011310617 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (75043 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_504 : rowCell 2 504 ≤ (31169098371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (227210901557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10011310617 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_504_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_504_1
  · norm_num [gridPoint]

theorem exp_2_505_0 : expNegUpper (196883954344459015526629 / 1755801298388092416000 : ℝ) ≤ (100113104063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (75043 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_505_1 : expNegUpper (98553021066972064482841 / 877900649194046208000 : ℝ) ≤ (88218138201 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1923 / 800 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_505 : rowCell 2 505 ≤ (1373328339 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (100113104063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (88218138201 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_505_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_505_1
  · norm_num [gridPoint]

theorem exp_2_506_0 : expNegUpper (296530346636936784222907 / 2641463254514473216000 : ℝ) ≤ (22054534089 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1923 / 800 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_506_1 : expNegUpper (118745844097645425780969 / 1056585301805789286400 : ℝ) ≤ (155464107723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (150383 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_506 : rowCell 2 506 ≤ (12101236967 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22054534089 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (155464107723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_506_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_506_1
  · norm_num [gridPoint]

theorem exp_2_507_0 : expNegUpper (119095263676568859929409 / 1059694392239874150400 : ℝ) ≤ (155464104491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (150383 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_507_1 : expNegUpper (149036778193468907289409 / 1324617990299842688000 : ℝ) ≤ (136977048949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2408509 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_507 : rowCell 2 507 ≤ (21325071649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (155464104491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (136977048949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_507_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_507_1
  · norm_num [gridPoint]

theorem exp_2_508_0 : expNegUpper (49824895696052323909387 / 442836687639629184000 : ℝ) ≤ (136977046117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2408509 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_508_1 : expNegUpper (199523937750372178128161 / 1771346750558516736000 : ℝ) ≤ (1508519767 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2410893 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_508 : rowCell 2 508 ≤ (9394349303 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (136977046117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1508519767 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_508_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_508_1
  · norm_num [gridPoint]

theorem exp_2_509_0 : expNegUpper (3430445675288931296981 / 30455036459757056000 : ℝ) ≤ (120681578879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2410893 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_509_1 : expNegUpper (1717152376892252832327 / 15227518229878528000 : ℝ) ≤ (106318736463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2413281 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_509 : rowCell 2 509 ≤ (16553066941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (120681578879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (106318736463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_509_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_509_1
  · norm_num [gridPoint]

theorem exp_2_510_0 : expNegUpper (301382031421994108276601 / 2672622673772587264000 : ℝ) ≤ (10631873429 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2413281 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_510_1 : expNegUpper (603441678749730146676601 / 5345245347545174528000 : ℝ) ≤ (2926876359 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (301959 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_510 : rowCell 2 510 ≤ (2916526429 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10631873429 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2926876359 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_510_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_510_1
  · norm_num [gridPoint]

theorem exp_2_511_0 : expNegUpper (201735655783414084128763 / 1786960717646206464000 : ℝ) ≤ (46830020793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (301959 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_511_1 : expNegUpper (394457593591002700 / 3490157651652747 : ℝ) ≤ (82503950453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2418067 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_511 : rowCell 2 511 ≤ (3211509143 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (46830020793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (82503950453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_511_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_511_1
  · norm_num [gridPoint]

theorem sum_2_480_2 : blockSum (rowCell 2) 480 2 ≤ (599489496927 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_480) (by simpa only [blockSum_one] using cell_2_481) (by norm_num)

theorem sum_2_482_2 : blockSum (rowCell 2) 482 2 ≤ (233407935577 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_482) (by simpa only [blockSum_one] using cell_2_483) (by norm_num)

theorem sum_2_480_4 : blockSum (rowCell 2) 480 4 ≤ (1066305368081 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_480_2 sum_2_482_2 (by norm_num)

theorem sum_2_484_2 : blockSum (rowCell 2) 484 2 ≤ (726825371579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_484) (by simpa only [blockSum_one] using cell_2_485) (by norm_num)

theorem sum_2_486_2 : blockSum (rowCell 2) 486 2 ≤ (282843357823 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_486) (by simpa only [blockSum_one] using cell_2_487) (by norm_num)

theorem sum_2_484_4 : blockSum (rowCell 2) 484 4 ≤ (51700483489 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_484_2 sum_2_486_2 (by norm_num)

theorem sum_2_480_8 : blockSum (rowCell 2) 480 8 ≤ (3425122823387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_480_4 sum_2_484_4 (by norm_num)

theorem sum_2_488_2 : blockSum (rowCell 2) 488 2 ≤ (110040943069 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_488) (by simpa only [blockSum_one] using cell_2_489) (by norm_num)

theorem sum_2_490_2 : blockSum (rowCell 2) 490 2 ≤ (85602412377 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_490) (by simpa only [blockSum_one] using cell_2_491) (by norm_num)

theorem sum_2_488_4 : blockSum (rowCell 2) 488 4 ≤ (97821677723 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_488_2 sum_2_490_2 (by norm_num)

theorem sum_2_492_2 : blockSum (rowCell 2) 492 2 ≤ (5326010711 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_492) (by simpa only [blockSum_one] using cell_2_493) (by norm_num)

theorem sum_2_494_2 : blockSum (rowCell 2) 494 2 ≤ (41411729921 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_494) (by simpa only [blockSum_one] using cell_2_495) (by norm_num)

theorem sum_2_492_4 : blockSum (rowCell 2) 492 4 ≤ (94671837031 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_492_2 sum_2_494_2 (by norm_num)

theorem sum_2_488_8 : blockSum (rowCell 2) 488 8 ≤ (1255932606939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_488_4 sum_2_492_4 (by norm_num)

theorem sum_2_480_16 : blockSum (rowCell 2) 480 16 ≤ (2340527715163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_480_8 sum_2_488_8 (by norm_num)

theorem sum_2_496_2 : blockSum (rowCell 2) 496 2 ≤ (40239349643 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_496) (by simpa only [blockSum_one] using cell_2_497) (by norm_num)

theorem sum_2_498_2 : blockSum (rowCell 2) 498 2 ≤ (62545442683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_498) (by simpa only [blockSum_one] using cell_2_499) (by norm_num)

theorem sum_2_496_4 : blockSum (rowCell 2) 496 4 ≤ (143024141969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_496_2 sum_2_498_2 (by norm_num)

theorem sum_2_500_2 : blockSum (rowCell 2) 500 2 ≤ (97193776753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_500) (by simpa only [blockSum_one] using cell_2_501) (by norm_num)

theorem sum_2_502_2 : blockSum (rowCell 2) 502 2 ≤ (37750284423 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_502) (by simpa only [blockSum_one] using cell_2_503) (by norm_num)

theorem sum_2_500_4 : blockSum (rowCell 2) 500 4 ≤ (172694345599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_500_2 sum_2_502_2 (by norm_num)

theorem sum_2_496_8 : blockSum (rowCell 2) 496 8 ≤ (458742629537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_496_4 sum_2_500_4 (by norm_num)

theorem sum_2_504_2 : blockSum (rowCell 2) 504 2 ≤ (58635665151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_504) (by simpa only [blockSum_one] using cell_2_505) (by norm_num)

theorem sum_2_506_2 : blockSum (rowCell 2) 506 2 ≤ (45527545583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_506) (by simpa only [blockSum_one] using cell_2_507) (by norm_num)

theorem sum_2_504_4 : blockSum (rowCell 2) 504 4 ≤ (52081605367 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_504_2 sum_2_506_2 (by norm_num)

theorem sum_2_508_2 : blockSum (rowCell 2) 508 2 ≤ (35341765547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_508) (by simpa only [blockSum_one] using cell_2_509) (by norm_num)

theorem sum_2_510_2 : blockSum (rowCell 2) 510 2 ≤ (27428668717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_510) (by simpa only [blockSum_one] using cell_2_511) (by norm_num)

theorem sum_2_508_4 : blockSum (rowCell 2) 508 4 ≤ (7846304283 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_508_2 sum_2_510_2 (by norm_num)

theorem sum_2_504_8 : blockSum (rowCell 2) 504 8 ≤ (83466822499 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_504_4 sum_2_508_4 (by norm_num)

theorem sum_2_496_16 : blockSum (rowCell 2) 496 16 ≤ (125135254907 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_496_8 sum_2_504_8 (by norm_num)

theorem sum_2_480_32 : blockSum (rowCell 2) 480 32 ≤ (5306731704861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_480_16 sum_2_496_16 (by norm_num)

#print axioms sum_2_480_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
