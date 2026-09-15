import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_480_0 : expNegUpper (16495095186464509981041 / 152711281184936464000 : ℝ) ≤ (246141589241 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (116267 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_480_1 : expNegUpper (528461077425537679812271 / 4886760997917966848000 : ℝ) ≤ (2711249855049 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2327639 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_480 : rowCell 1 480 ≤ (168827039279 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (246141589241 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2711249855049 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_480_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_480_1
  · norm_num [gridPoint]

theorem exp_1_481_0 : expNegUpper (176692656757081888940813 / 1633904218046252544000 : ℝ) ≤ (2711249793873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2327639 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_481_1 : expNegUpper (17689939410210950821369 / 163390421804625254400 : ℝ) ≤ (1911209897907 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2329941 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_481 : rowCell 1 481 ≤ (1487662797721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2711249793873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1911209897907 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_481_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_481_1
  · norm_num [gridPoint]

theorem exp_1_482_0 : expNegUpper (53231943963563505536027 / 491668714866530355200 : ℝ) ≤ (9556049275227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2329941 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_482_1 : expNegUpper (532941835577906959488261 / 4916687148665303552000 : ℝ) ≤ (8419798594361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1166123 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_482 : rowCell 1 482 ≤ (1310814976827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9556049275227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8419798594361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_482_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_482_1
  · norm_num [gridPoint]

theorem exp_1_483_0 : expNegUpper (534567464052371131735869 / 4931684481497604608000 : ℝ) ≤ (8419798406681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1166123 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_483_1 : expNegUpper (133798011808152907770727 / 1232921120374401152000 : ℝ) ≤ (927277242247 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466911 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_483 : rowCell 1 483 ≤ (1154922381321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8419798406681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (927277242247 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_483_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_483_1
  · norm_num [gridPoint]

theorem exp_1_484_0 : expNegUpper (57722801453095972331 / 531903726089856000 : ℝ) ≤ (3709108886813 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466911 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_484_1 : expNegUpper (231160785919475778991 / 2127614904359424000 : ℝ) ≤ (6535399813817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2336867 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_484 : rowCell 1 484 ≤ (101751033093 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3709108886813 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6535399813817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_484_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_484_1
  · norm_num [gridPoint]

theorem exp_1_485_0 : expNegUpper (539083218012237934916627 / 4961747662079472128000 : ℝ) ≤ (6535399669903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2336867 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_485_1 : expNegUpper (269856092830377135715413 / 2480873831039736064000 : ℝ) ≤ (5757308983241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1169591 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_485 : rowCell 1 485 ≤ (448197679609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6535399669903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5757308983241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_485_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_485_1
  · norm_num [gridPoint]

theorem exp_1_486_0 : expNegUpper (20821191059232536737689 / 191415904224193792000 : ℝ) ≤ (1439327214307 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1169591 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_486_1 : expNegUpper (1667637330519598565053 / 15313272337935503360 : ℝ) ≤ (202862523287 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2341501 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_486 : rowCell 1 486 ≤ (394825535443 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1439327214307 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (202862523287 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_486_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_486_1
  · norm_num [gridPoint]

theorem exp_1_487_0 : expNegUpper (7248337494527403335963 / 66558695945124802560 : ℝ) ≤ (2535781485921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2341501 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_487_1 : expNegUpper (22677444897061067479889 / 207995924828515008000 : ℝ) ≤ (4467238681057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2343823 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_487 : rowCell 1 487 ≤ (695577986547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2535781485921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4467238681057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_487_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_487_1
  · norm_num [gridPoint]

theorem exp_1_488_0 : expNegUpper (68238282706638058337203 / 625876715030679616000 : ℝ) ≤ (4467238584457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2343823 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_488_1 : expNegUpper (546541830984881175785223 / 5007013720245436928000 : ℝ) ≤ (3934700013383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2346149 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_488 : rowCell 1 488 ≤ (153169227793 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4467238584457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3934700013383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_488_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_488_1
  · norm_num [gridPoint]

theorem exp_1_489_0 : expNegUpper (21927753048921290056407 / 200885923316490752000 : ℝ) ≤ (3934699928811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2346149 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_489_1 : expNegUpper (10976632055549096983499 / 100442961658245376000 : ℝ) ≤ (3465447733929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1174239 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_489 : rowCell 1 489 ≤ (269812708069 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3934699928811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3465447733929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_489_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_489_1
  · norm_num [gridPoint]

theorem exp_1_490_0 : expNegUpper (91748002631946208510657 / 839550880647475968000 : ℝ) ≤ (3465447659891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1174239 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_490_1 : expNegUpper (183709334299841762138527 / 1679101761294951936000 : ℝ) ≤ (1525992686811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (235081 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_490 : rowCell 1 490 ≤ (475257072311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3465447659891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1525992686811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_490_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_490_1
  · norm_num [gridPoint]

theorem exp_1_491_0 : expNegUpper (552788840351378112387989 / 5052485323163197952000 : ℝ) ≤ (3051985308809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (235081 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_491_1 : expNegUpper (27671552067171556711809 / 252624266158159897600 : ℝ) ≤ (1343850714323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470629 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_491 : rowCell 1 491 ≤ (209271556823 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3051985308809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1343850714323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_491_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_491_1
  · norm_num [gridPoint]

theorem exp_1_492_0 : expNegUpper (27754815494723674105569 / 253384410037364761600 : ℝ) ≤ (2687701371911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470629 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_492_1 : expNegUpper (555740728101511039365811 / 5067688200747295232000 : ℝ) ≤ (1183382630351 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (588871 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_492 : rowCell 1 492 ≤ (368576247973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2687701371911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1183382630351 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_492_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_492_1
  · norm_num [gridPoint]

theorem exp_1_493_0 : expNegUpper (185803478137767335654393 / 1694304638879049216000 : ℝ) ≤ (1183382605521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (588871 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_493_1 : expNegUpper (93009512194350608088923 / 847152319439524608000 : ℝ) ≤ (83361407883 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2357827 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_493 : rowCell 1 493 ≤ (162278182263 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1183382605521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (83361407883 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_493_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_493_1
  · norm_num [gridPoint]

theorem exp_1_494_0 : expNegUpper (11194624478004046673449 / 101963249416655104000 : ℝ) ≤ (260504394201 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2357827 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_494_1 : expNegUpper (22415203461181904338737 / 203926498833310208000 : ℝ) ≤ (14335760987 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (590043 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_494 : rowCell 1 494 ≤ (285777916859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (260504394201 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14335760987 / 7812500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_494_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_494_1
  · norm_num [gridPoint]

theorem exp_1_495_0 : expNegUpper (562058688347513108968257 / 5113433863334117888000 : ℝ) ≤ (458744342073 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (590043 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_495_1 : expNegUpper (35169361136511347868721 / 319589616458382368000 : ℝ) ≤ (403898572779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2362521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_495 : rowCell 1 495 ≤ (31452348191 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (458744342073 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (403898572779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_495_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_495_1
  · norm_num [gridPoint]

theorem exp_1_496_0 : expNegUpper (11758184119741103741243 / 106848501961275744000 : ℝ) ≤ (80779712891 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2362521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_496_1 : expNegUpper (37669743874822944503729 / 341915206276082380800 : ℝ) ≤ (711180642889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2364873 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_496 : rowCell 1 496 ≤ (221530447653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (80779712891 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (711180642889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_496_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_496_1
  · norm_num [gridPoint]

theorem exp_1_497_0 : expNegUpper (113346736418544118447147 / 1028809032650821734400 : ℝ) ≤ (1422361256639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2364873 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_497_1 : expNegUpper (283694618168187030083343 / 2572022581627054336000 : ℝ) ≤ (1252171076221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2367229 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_497 : rowCell 1 497 ≤ (195029300613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1422361256639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1252171076221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_497_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_497_1
  · norm_num [gridPoint]

theorem exp_1_498_0 : expNegUpper (284540615687647296832767 / 2579692535336368384000 : ℝ) ≤ (7826069067 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2367229 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_498_1 : expNegUpper (569739022818609890460853 / 5159385070672736768000 : ℝ) ≤ (68892773347 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (592397 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_498 : rowCell 1 498 ≤ (171689004869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7826069067 / 6250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (68892773347 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_498_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_498_1
  · norm_num [gridPoint]

theorem exp_1_499_0 : expNegUpper (23443507511287533563 / 212297346313728000 : ℝ) ≤ (551142175619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (592397 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_499_1 : expNegUpper (5867646436527080053 / 53074336578432000 : ℝ) ≤ (970286474497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2371951 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_499 : rowCell 1 499 ≤ (4722928959 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (551142175619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (970286474497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_499_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_499_1
  · norm_num [gridPoint]

theorem exp_1_500_0 : expNegUpper (143449121180519087440643 / 1297533350106814592000 : ℝ) ≤ (970286454971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2371951 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_500_1 : expNegUpper (574458760557053951015691 / 5190133400427258368000 : ℝ) ≤ (427024465423 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (593579 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_500 : rowCell 1 500 ≤ (66516087693 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (970286454971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (427024465423 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_500_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_500_1
  · norm_num [gridPoint]

theorem exp_1_501_0 : expNegUpper (576164208770961397887939 / 5205541822763151872000 : ℝ) ≤ (5337805711 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (593579 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_501_1 : expNegUpper (57682873179793947473449 / 520554182276315187200 : ℝ) ≤ (751695729311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1188343 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_501 : rowCell 1 501 ≤ (58546171017 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5337805711 / 6250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (751695729311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_501_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_501_1
  · norm_num [gridPoint]

theorem exp_1_502_0 : expNegUpper (19284622590887580723443 / 174032436113493350400 : ℝ) ≤ (375847857181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1188343 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_502_1 : expNegUpper (193068483758795174350987 / 1740324361134933504000 : ℝ) ≤ (82696681629 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1189529 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_502 : rowCell 1 502 ≤ (103056857421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (375847857181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (82696681629 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_502_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_502_1
  · norm_num [gridPoint]

theorem exp_1_503_0 : expNegUpper (580919901581413067937689 / 5236427182352204288000 : ℝ) ≤ (661573439953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1189529 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_503_1 : expNegUpper (72698616123091342837521 / 654553397794025536000 : ℝ) ≤ (582224957681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1190717 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_503 : rowCell 1 503 ≤ (90698896631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (661573439953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (582224957681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_503_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_503_1
  · norm_num [gridPoint]

theorem exp_1_504_0 : expNegUpper (2916539451638284916601 / 26259520598026816000 : ℝ) ≤ (291112473119 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1190717 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_504_1 : expNegUpper (23359166996612551216207 / 210076164784214528000 : ℝ) ≤ (102473229947 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2383813 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_504 : rowCell 1 504 ≤ (79818566141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (291112473119 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (102473229947 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_504_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_504_1
  · norm_num [gridPoint]

theorem exp_1_505_0 : expNegUpper (195234217985899271526629 / 1755801298388092416000 : ℝ) ≤ (20494645589 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2383813 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_505_1 : expNegUpper (97729366510078880482841 / 877900649194046208000 : ℝ) ≤ (225432751333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (596549 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_505 : rowCell 1 505 ≤ (70239716767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20494645589 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (225432751333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_505_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_505_1
  · norm_num [gridPoint]

theorem exp_1_506_0 : expNegUpper (294052101231937104222907 / 2641463254514473216000 : ℝ) ≤ (450865493909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (596549 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_506_1 : expNegUpper (117756002282509579380969 / 1056585301805789286400 : ℝ) ≤ (396725989413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1194291 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_506 : rowCell 1 506 ≤ (7725891559 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (450865493909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (396725989413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_506_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_506_1
  · norm_num [gridPoint]

theorem exp_1_507_0 : expNegUpper (118102509167704962329409 / 1059694392239874150400 : ℝ) ≤ (198362990877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1194291 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_507_1 : expNegUpper (147797655490969067289409 / 1324617990299842688000 : ℝ) ≤ (349069147139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2390971 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_507 : rowCell 1 507 ≤ (1087681017 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (198362990877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (349069147139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_507_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_507_1
  · norm_num [gridPoint]

theorem exp_1_508_0 : expNegUpper (49410641172832355909387 / 442836687639629184000 : ℝ) ≤ (349069140439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2390971 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_508_1 : expNegUpper (197869346902265682128161 / 1771346750558516736000 : ℝ) ≤ (307121023529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (598341 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_508 : rowCell 1 508 ≤ (47849976303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (349069140439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (307121023529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_508_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_508_1
  · norm_num [gridPoint]

theorem exp_1_509_0 : expNegUpper (23813986286504129318867 / 213185255218299392000 : ℝ) ≤ (76780254417 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (598341 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_509_1 : expNegUpper (11920645552672977506289 / 106592627609149696000 : ℝ) ≤ (270199783261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (29947 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_509 : rowCell 1 509 ≤ (42098751491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (76780254417 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (270199783261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_509_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_509_1
  · norm_num [gridPoint]

theorem exp_1_510_0 : expNegUpper (298889222548354172276601 / 2672622673772587264000 : ℝ) ≤ (54039955627 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (29947 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_510_1 : expNegUpper (598463342736770402676601 / 5345245347545174528000 : ℝ) ≤ (118852389619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2398159 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_510 : rowCell 1 510 ≤ (7407371329 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (54039955627 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (118852389619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_510_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_510_1
  · norm_num [gridPoint]

theorem exp_1_511_0 : expNegUpper (200071355956214084128763 / 1786960717646206464000 : ℝ) ≤ (47540954951 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2398159 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_511_1 : expNegUpper (391211748703450700 / 3490157651652747 : ℝ) ≤ (104553458027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1200281 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_511 : rowCell 1 511 ≤ (32581909927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47540954951 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (104553458027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_511_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_511_1
  · norm_num [gridPoint]

theorem sum_1_480_2 : blockSum (rowCell 1) 480 2 ≤ (3175933190511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_480) (by simpa only [blockSum_one] using cell_1_481) (by norm_num)

theorem sum_1_482_2 : blockSum (rowCell 1) 482 2 ≤ (616434339537 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_482) (by simpa only [blockSum_one] using cell_1_483) (by norm_num)

theorem sum_1_480_4 : blockSum (rowCell 1) 480 4 ≤ (5641670548659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_480_2 sum_1_482_2 (by norm_num)

theorem sum_1_484_2 : blockSum (rowCell 1) 484 2 ≤ (478476422537 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_484) (by simpa only [blockSum_one] using cell_1_485) (by norm_num)

theorem sum_1_486_2 : blockSum (rowCell 1) 486 2 ≤ (1485229057433 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_486) (by simpa only [blockSum_one] using cell_1_487) (by norm_num)

theorem sum_1_484_4 : blockSum (rowCell 1) 484 4 ≤ (3399134747581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_484_2 sum_1_486_2 (by norm_num)

theorem sum_1_480_8 : blockSum (rowCell 1) 480 8 ≤ (113010066203 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_480_4 sum_1_484_4 (by norm_num)

theorem sum_1_488_2 : blockSum (rowCell 1) 488 2 ≤ (115230232731 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_488) (by simpa only [blockSum_one] using cell_1_489) (by norm_num)

theorem sum_1_490_2 : blockSum (rowCell 1) 490 2 ≤ (893800185957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_490) (by simpa only [blockSum_one] using cell_1_491) (by norm_num)

theorem sum_1_488_4 : blockSum (rowCell 1) 488 4 ≤ (2046102513267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_488_2 sum_1_490_2 (by norm_num)

theorem sum_1_492_2 : blockSum (rowCell 1) 492 2 ≤ (693132612499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_492) (by simpa only [blockSum_one] using cell_1_493) (by norm_num)

theorem sum_1_494_2 : blockSum (rowCell 1) 494 2 ≤ (537396702387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_494) (by simpa only [blockSum_one] using cell_1_495) (by norm_num)

theorem sum_1_492_4 : blockSum (rowCell 1) 492 4 ≤ (615264657443 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_492_2 sum_1_494_2 (by norm_num)

theorem sum_1_488_8 : blockSum (rowCell 1) 488 8 ≤ (3276631828153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_488_4 sum_1_492_4 (by norm_num)

theorem sum_1_480_16 : blockSum (rowCell 1) 480 16 ≤ (12317437124393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_480_8 sum_1_488_8 (by norm_num)

theorem sum_1_496_2 : blockSum (rowCell 1) 496 2 ≤ (208279874133 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_496) (by simpa only [blockSum_one] using cell_1_497) (by norm_num)

theorem sum_1_498_2 : blockSum (rowCell 1) 498 2 ≤ (322822731557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_498) (by simpa only [blockSum_one] using cell_1_499) (by norm_num)

theorem sum_1_496_4 : blockSum (rowCell 1) 496 4 ≤ (739382479823 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_496_2 sum_1_498_2 (by norm_num)

theorem sum_1_500_2 : blockSum (rowCell 1) 500 2 ≤ (12506225871 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_500) (by simpa only [blockSum_one] using cell_1_501) (by norm_num)

theorem sum_1_502_2 : blockSum (rowCell 1) 502 2 ≤ (48438938513 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_502) (by simpa only [blockSum_one] using cell_1_503) (by norm_num)

theorem sum_1_500_4 : blockSum (rowCell 1) 500 4 ≤ (27742516967 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_500_2 sum_1_502_2 (by norm_num)

theorem sum_1_496_8 : blockSum (rowCell 1) 496 8 ≤ (236652550259 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_496_4 sum_1_500_4 (by norm_num)

theorem sum_1_504_2 : blockSum (rowCell 1) 504 2 ≤ (37514570727 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_504) (by simpa only [blockSum_one] using cell_1_505) (by norm_num)

theorem sum_1_506_2 : blockSum (rowCell 1) 506 2 ≤ (58095591661 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_506) (by simpa only [blockSum_one] using cell_1_507) (by norm_num)

theorem sum_1_504_4 : blockSum (rowCell 1) 504 4 ≤ (26624946623 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_504_2 sum_1_506_2 (by norm_num)

theorem sum_1_508_2 : blockSum (rowCell 1) 508 2 ≤ (44974363897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_508) (by simpa only [blockSum_one] using cell_1_509) (by norm_num)

theorem sum_1_510_2 : blockSum (rowCell 1) 510 2 ≤ (17404691643 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_510) (by simpa only [blockSum_one] using cell_1_511) (by norm_num)

theorem sum_1_508_4 : blockSum (rowCell 1) 508 4 ≤ (79783747183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_508_2 sum_1_510_2 (by norm_num)

theorem sum_1_504_8 : blockSum (rowCell 1) 504 8 ≤ (106454240149 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_504_4 sum_1_508_4 (by norm_num)

theorem sum_1_496_16 : blockSum (rowCell 1) 496 16 ≤ (1609079711891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_496_8 sum_1_504_8 (by norm_num)

theorem sum_1_480_32 : blockSum (rowCell 1) 480 32 ≤ (3481629209071 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_480_16 sum_1_496_16 (by norm_num)

#print axioms sum_1_480_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
