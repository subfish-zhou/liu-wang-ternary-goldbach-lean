import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_480_0 : expNegUpper (16346121257787133981041 / 152711281184936464000 : ℝ) ≤ (6529062908541 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (461537 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_480_1 : expNegUpper (523701193442181775812271 / 4886760997917966848000 : ℝ) ≤ (448815939427 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2309993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_480 : rowCell 0 480 ≤ (4475121604539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6529062908541 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (448815939427 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_480_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_480_1
  · norm_num [gridPoint]

theorem exp_0_481_0 : expNegUpper (58367058091027722980271 / 544634739348750848000 : ℝ) ≤ (5744843905011 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2309993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_481_1 : expNegUpper (5843677962096138807123 / 54463473934875084800 : ℝ) ≤ (1263635861959 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (462461 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_481 : rowCell 0 481 ≤ (3937505141721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5744843905011 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1263635861959 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_481_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_481_1
  · norm_num [gridPoint]

theorem exp_0_482_0 : expNegUpper (52753771044931876736027 / 491668714866530355200 : ℝ) ≤ (25272716715999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (462461 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_482_1 : expNegUpper (528167388125910799488261 / 4916687148665303552000 : ℝ) ≤ (22234739781227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (115731 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_482 : rowCell 0 482 ≤ (3464286410259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25272716715999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22234739781227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_482_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_482_1
  · norm_num [gridPoint]

theorem exp_0_483_0 : expNegUpper (529778453131734715735869 / 4931684481497604608000 : ℝ) ≤ (11117369661867 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (115731 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_483_1 : expNegUpper (132602579511573835770727 / 1232921120374401152000 : ℝ) ≤ (9780446832571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1158469 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_483 : rowCell 0 483 ≤ (3047775108313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11117369661867 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9780446832571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_483_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_483_1
  · norm_num [gridPoint]

theorem exp_0_484_0 : expNegUpper (19069023686696630777 / 177301242029952000 : ℝ) ≤ (4890223316277 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1158469 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_484_1 : expNegUpper (76366998758730432997 / 709204968119808000 : ℝ) ≤ (17207666024023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2319259 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_484 : rowCell 0 484 ≤ (167574773601 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4890223316277 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17207666024023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_484_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_484_1
  · norm_num [gridPoint]

theorem exp_0_485_0 : expNegUpper (534279643622961262916627 / 4961747662079472128000 : ℝ) ≤ (8603832837123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2319259 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_485_1 : expNegUpper (267457946502898863715413 / 2480873831039736064000 : ℝ) ≤ (15136727272399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2321583 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_485 : rowCell 0 485 ≤ (471716438617 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8603832837123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15136727272399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_485_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_485_1
  · norm_num [gridPoint]

theorem exp_0_486_0 : expNegUpper (268270055708224577589957 / 2488406754914519296000 : ℝ) ≤ (15136726966579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2321583 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_486_1 : expNegUpper (21487142321183714465689 / 199072540393161543680 : ℝ) ≤ (13314315707813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2323911 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_486 : rowCell 0 486 ≤ (2074675593301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15136726966579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13314315707813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_486_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_486_1
  · norm_num [gridPoint]

theorem exp_0_487_0 : expNegUpper (2394698552140614765321 / 22186231981708267520 : ℝ) ≤ (13314315440437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2323911 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_487_1 : expNegUpper (7492330852859289159963 / 69331974942838336000 : ℝ) ≤ (11710694924691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2326243 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_487 : rowCell 0 487 ≤ (1824846239233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13314315440437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11710694924691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_487_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_487_1
  · norm_num [gridPoint]

theorem exp_0_488_0 : expNegUpper (67635105257608426337203 / 625876715030679616000 : ℝ) ≤ (5855347345469 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2326243 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_488_1 : expNegUpper (541723693126964247785223 / 5007013720245436928000 : ℝ) ≤ (2059935091357 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2328577 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_488 : rowCell 0 488 ≤ (802507983057 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5855347345469 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2059935091357 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_488_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_488_1
  · norm_num [gridPoint]

theorem exp_0_489_0 : expNegUpper (21734444995859002696407 / 200885923316490752000 : ℝ) ≤ (5149837626217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2328577 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_489_1 : expNegUpper (10880123663704355863499 / 100442961658245376000 : ℝ) ≤ (9058193072473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466183 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_489 : rowCell 0 489 ≤ (176449143761 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5149837626217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9058193072473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_489_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_489_1
  · norm_num [gridPoint]

theorem exp_0_490_0 : expNegUpper (30313779596155552170219 / 279850293549158656000 : ℝ) ≤ (2264548223459 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466183 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_490_1 : expNegUpper (60699477952552011379509 / 559700587098317312000 : ℝ) ≤ (7965937037463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (291657 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_490 : rowCell 0 490 ≤ (310353712427 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2264548223459 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7965937037463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_490_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_490_1
  · norm_num [gridPoint]

theorem exp_0_491_0 : expNegUpper (547941575556180672387989 / 5052485323163197952000 : ℝ) ≤ (7965936881309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (291657 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_491_1 : expNegUpper (27429552914127691111809 / 252624266158159897600 : ℝ) ≤ (1751255611331 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (5839 / 2500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_491 : rowCell 0 491 ≤ (109169580457 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7965936881309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1751255611331 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_491_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_491_1
  · norm_num [gridPoint]

theorem exp_0_492_0 : expNegUpper (27512088168247795705569 / 253384410037364761600 : ℝ) ≤ (700502230883 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (5839 / 2500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_492_1 : expNegUpper (550893463306313599365811 / 5067688200747295232000 : ℝ) ≤ (12030666817 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (584487 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_492 : rowCell 0 492 ≤ (959983481281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (700502230883 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12030666817 / 1953125000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_492_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_492_1
  · norm_num [gridPoint]

theorem exp_0_493_0 : expNegUpper (61394289572162701218131 / 564768212959683072000 : ℝ) ≤ (6159701291 / 1000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (584487 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_493_1 : expNegUpper (30733473702032560029641 / 282384106479841536000 : ℝ) ≤ (338506783091 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2340299 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_493 : rowCell 0 493 ≤ (3376473809 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6159701291 / 1000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (338506783091 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_493_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_493_1
  · norm_num [gridPoint]

theorem exp_0_494_0 : expNegUpper (11097242278040890193449 / 101963249416655104000 : ℝ) ≤ (5416108425181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2340299 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_494_1 : expNegUpper (22220730330628396498737 / 203926498833310208000 : ℝ) ≤ (1190509140489 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2342653 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_494 : rowCell 0 494 ≤ (74219947689 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5416108425181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1190509140489 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_494_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_494_1
  · norm_num [gridPoint]

theorem exp_0_495_0 : expNegUpper (557182296615035156968257 / 5113433863334117888000 : ℝ) ≤ (4762036470821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2342653 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_495_1 : expNegUpper (34865041761626483868721 / 319589616458382368000 : ℝ) ≤ (4186738750873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2345011 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_495 : rowCell 0 495 ≤ (326276364541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4762036470821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4186738750873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_495_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_495_1
  · norm_num [gridPoint]

theorem exp_0_496_0 : expNegUpper (3885480307505381247081 / 35616167320425248000 : ℝ) ≤ (2093369335613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2345011 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_496_1 : expNegUpper (12448217030885915901243 / 113971735425360793600 : ℝ) ≤ (736150926797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (586843 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_496 : rowCell 0 496 ≤ (143426170067 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2093369335613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (736150926797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_496_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_496_1
  · norm_num [gridPoint]

theorem exp_0_497_0 : expNegUpper (112368545378320476847147 / 1028809032650821734400 : ℝ) ≤ (3680754564379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (586843 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_497_1 : expNegUpper (281252781434787990083343 / 2572022581627054336000 : ℝ) ≤ (64715131243 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (293717 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_497 : rowCell 0 497 ≤ (2521791027 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3680754564379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64715131243 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_497_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_497_1
  · norm_num [gridPoint]

theorem exp_0_498_0 : expNegUpper (282091497219928128832767 / 2579692535336368384000 : ℝ) ≤ (3235756501323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (293717 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_498_1 : expNegUpper (564848067617491682460853 / 5159385070672736768000 : ℝ) ≤ (2844414471919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (294013 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_498 : rowCell 0 498 ≤ (443371530023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3235756501323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2844414471919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_498_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_498_1
  · norm_num [gridPoint]

theorem exp_0_499_0 : expNegUpper (100716440340955585173 / 919955167359488000 : ℝ) ≤ (568882883753 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (294013 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_499_1 : expNegUpper (25208768472264531963 / 229988791839872000 : ℝ) ≤ (2500276748687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94179 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_499 : rowCell 0 499 ≤ (194869840901 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (568882883753 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2500276748687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_499_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_499_1
  · norm_num [gridPoint]

theorem exp_0_500_0 : expNegUpper (142220921079499439440643 / 1297533350106814592000 : ℝ) ≤ (1250138351121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94179 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_500_1 : expNegUpper (569553241887295487015691 / 5190133400427258368000 : ℝ) ≤ (439533054449 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2356849 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_500 : rowCell 0 500 ≤ (342578149587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1250138351121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (439533054449 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_500_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_500_1
  · norm_num [gridPoint]

theorem exp_0_501_0 : expNegUpper (571244126632562677887939 / 5205541822763151872000 : ℝ) ≤ (1098832615831 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2356849 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_501_1 : expNegUpper (57191593139386088273449 / 520554182276315187200 : ℝ) ≤ (193158296207 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1179613 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_501 : rowCell 0 501 ≤ (301108488159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1098832615831 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (193158296207 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_501_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_501_1
  · norm_num [gridPoint]

theorem exp_0_502_0 : expNegUpper (6373459042821206374481 / 58010812037831116800 : ℝ) ≤ (482895731653 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1179613 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_502_1 : expNegUpper (63809485459776311450329 / 580108120378311168000 : ℝ) ≤ (1697632338637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2361607 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_502 : rowCell 0 502 ≤ (132322818883 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (482895731653 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1697632338637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_502_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_502_1
  · norm_num [gridPoint]

theorem exp_0_503_0 : expNegUpper (575985255974374091937689 / 5236427182352204288000 : ℝ) ≤ (1697632307657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2361607 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_503_1 : expNegUpper (72082695639001486837521 / 654553397794025536000 : ℝ) ≤ (1491943792529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2363991 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_503 : rowCell 0 503 ≤ (232586754861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1697632307657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1491943792529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_503_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_503_1
  · norm_num [gridPoint]

theorem exp_0_504_0 : expNegUpper (2891829814931489396601 / 26259520598026816000 : ℝ) ≤ (1491943765463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2363991 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_504_1 : expNegUpper (23161781172330992176207 / 210076164784214528000 : ℝ) ≤ (655556203973 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2366379 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_504 : rowCell 0 504 ≤ (25550171817 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1491943765463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (655556203973 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_504_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_504_1
  · norm_num [gridPoint]

theorem exp_0_505_0 : expNegUpper (64528160542446509175543 / 585267099462697472000 : ℝ) ≤ (1311112384301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2366379 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_505_1 : expNegUpper (32301903984395232160947 / 292633549731348736000 : ℝ) ≤ (1152142323789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2368769 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_505 : rowCell 0 505 ≤ (35924549279 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1311112384301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1152142323789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_505_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_505_1
  · norm_num [gridPoint]

theorem exp_0_506_0 : expNegUpper (291573855826937424222907 / 2641463254514473216000 : ℝ) ≤ (1152142303133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2368769 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_506_1 : expNegUpper (116766160467373732980969 / 1056585301805789286400 : ℝ) ≤ (506198867961 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2371163 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_506 : rowCell 0 506 ≤ (2466253193 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1152142303133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (506198867961 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_506_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_506_1
  · norm_num [gridPoint]

theorem exp_0_507_0 : expNegUpper (117109754658841064729409 / 1059694392239874150400 : ℝ) ≤ (506198858939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2371163 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_507_1 : expNegUpper (146558532788469227289409 / 1324617990299842688000 : ℝ) ≤ (222389937621 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2373561 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_507 : rowCell 0 507 ≤ (138692447383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (506198858939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (222389937621 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_507_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_507_1
  · norm_num [gridPoint]

theorem exp_0_508_0 : expNegUpper (16332128883204129303129 / 147612229213209728000 : ℝ) ≤ (889559734721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2373561 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_508_1 : expNegUpper (65404918684719728709387 / 590448916852838912000 : ℝ) ≤ (195397097947 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1187981 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_508 : rowCell 0 508 ≤ (15232702851 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (889559734721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (195397097947 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_508_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_508_1
  · norm_num [gridPoint]

theorem exp_0_509_0 : expNegUpper (23614852845985739558867 / 213185255218299392000 : ℝ) ≤ (781588378019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1187981 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_509_1 : expNegUpper (11821224467100185186289 / 106592627609149696000 : ℝ) ≤ (335297437 / 488281250000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1189183 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_509 : rowCell 0 509 ≤ (10706811657 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (781588378019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (335297437 / 488281250000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_509_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_509_1
  · norm_num [gridPoint]

theorem exp_0_510_0 : expNegUpper (296396413674714236276601 / 2672622673772587264000 : ℝ) ≤ (13733782779 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1189183 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_510_1 : expNegUpper (593485006723810658676601 / 5345245347545174528000 : ℝ) ≤ (301641767229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2380773 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_510 : rowCell 0 510 ≤ (18813193261 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13733782779 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (301641767229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_510_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_510_1
  · norm_num [gridPoint]

theorem exp_0_511_0 : expNegUpper (66135685376338028042921 / 595653572548735488000 : ℝ) ≤ (120656704791 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2380773 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_511_1 : expNegUpper (129321967938632900 / 1163385883884249 : ℝ) ≤ (529983135367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (148949 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_511 : rowCell 0 511 ≤ (10329852871 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (120656704791 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (529983135367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_511_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_511_1
  · norm_num [gridPoint]

theorem sum_0_480_2 : blockSum (rowCell 0) 480 2 ≤ (420631337313 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_480) (by simpa only [blockSum_one] using cell_0_481) (by norm_num)

theorem sum_0_482_2 : blockSum (rowCell 0) 482 2 ≤ (1628015379643 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_482) (by simpa only [blockSum_one] using cell_0_483) (by norm_num)

theorem sum_0_480_4 : blockSum (rowCell 0) 480 4 ≤ (116599127069 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_480_2 sum_0_482_2 (by norm_num)

theorem sum_0_484_2 : blockSum (rowCell 0) 484 2 ≤ (5039778570701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_484) (by simpa only [blockSum_one] using cell_0_485) (by norm_num)

theorem sum_0_486_2 : blockSum (rowCell 0) 486 2 ≤ (1949760916267 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_486) (by simpa only [blockSum_one] using cell_0_487) (by norm_num)

theorem sum_0_484_4 : blockSum (rowCell 0) 484 4 ≤ (1787860080647 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_484_2 sum_0_486_2 (by norm_num)

theorem sum_0_480_8 : blockSum (rowCell 0) 480 8 ≤ (23863988668067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_480_4 sum_0_484_4 (by norm_num)

theorem sum_0_488_2 : blockSum (rowCell 0) 488 2 ≤ (1508304558101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_488) (by simpa only [blockSum_one] using cell_0_489) (by norm_num)

theorem sum_0_490_2 : blockSum (rowCell 0) 490 2 ≤ (1166555327139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_490) (by simpa only [blockSum_one] using cell_0_491) (by norm_num)

theorem sum_0_488_4 : blockSum (rowCell 0) 488 4 ≤ (66871497131 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_488_2 sum_0_490_2 (by norm_num)

theorem sum_0_492_2 : blockSum (rowCell 0) 492 2 ≤ (1804101933531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_492) (by simpa only [blockSum_one] using cell_0_493) (by norm_num)

theorem sum_0_494_2 : blockSum (rowCell 0) 494 2 ≤ (348688051493 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_494) (by simpa only [blockSum_one] using cell_0_495) (by norm_num)

theorem sum_0_492_4 : blockSum (rowCell 0) 492 4 ≤ (3198854139503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_492_2 sum_0_494_2 (by norm_num)

theorem sum_0_488_8 : blockSum (rowCell 0) 488 8 ≤ (8548573909983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_488_4 sum_0_492_4 (by norm_num)

theorem sum_0_480_16 : blockSum (rowCell 0) 480 16 ≤ (648251251561 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_480_8 sum_0_488_8 (by norm_num)

theorem sum_0_496_2 : blockSum (rowCell 0) 496 2 ≤ (269515721417 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_496) (by simpa only [blockSum_one] using cell_0_497) (by norm_num)

theorem sum_0_498_2 : blockSum (rowCell 0) 498 2 ≤ (33324448473 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_498) (by simpa only [blockSum_one] using cell_0_499) (by norm_num)

theorem sum_0_496_4 : blockSum (rowCell 0) 496 4 ≤ (1911174097493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_496_2 sum_0_498_2 (by norm_num)

theorem sum_0_500_2 : blockSum (rowCell 0) 500 2 ≤ (321843318873 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_500) (by simpa only [blockSum_one] using cell_0_501) (by norm_num)

theorem sum_0_502_2 : blockSum (rowCell 0) 502 2 ≤ (497232392627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_502) (by simpa only [blockSum_one] using cell_0_503) (by norm_num)

theorem sum_0_500_4 : blockSum (rowCell 0) 500 4 ≤ (1140919030373 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_500_2 sum_0_502_2 (by norm_num)

theorem sum_0_496_8 : blockSum (rowCell 0) 496 8 ≤ (1526046563933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_496_4 sum_0_500_4 (by norm_num)

theorem sum_0_504_2 : blockSum (rowCell 0) 504 2 ≤ (384024120931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_504) (by simpa only [blockSum_one] using cell_0_505) (by norm_num)

theorem sum_0_506_2 : blockSum (rowCell 0) 506 2 ≤ (59306530347 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_506) (by simpa only [blockSum_one] using cell_0_507) (by norm_num)

theorem sum_0_504_4 : blockSum (rowCell 0) 504 4 ≤ (340278386333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_504_2 sum_0_506_2 (by norm_num)

theorem sum_0_508_2 : blockSum (rowCell 0) 508 2 ≤ (114464869689 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_508) (by simpa only [blockSum_one] using cell_0_509) (by norm_num)

theorem sum_0_510_2 : blockSum (rowCell 0) 510 2 ≤ (176704789273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_510) (by simpa only [blockSum_one] using cell_0_511) (by norm_num)

theorem sum_0_508_4 : blockSum (rowCell 0) 508 4 ≤ (405634528651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_508_2 sum_0_510_2 (by norm_num)

theorem sum_0_504_8 : blockSum (rowCell 0) 504 8 ≤ (1086191301317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_504_4 sum_0_508_4 (by norm_num)

theorem sum_0_496_16 : blockSum (rowCell 0) 496 16 ≤ (4138284429183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_496_8 sum_0_504_8 (by norm_num)

theorem sum_0_480_32 : blockSum (rowCell 0) 480 32 ≤ (36550847007233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_480_16 sum_0_496_16 (by norm_num)

#print axioms sum_0_480_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
