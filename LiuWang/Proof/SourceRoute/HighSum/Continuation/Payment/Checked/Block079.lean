import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_480_0 : expNegUpper (16842701020045053981041 / 152711281184936464000 : ℝ) ≤ (631787970541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2367061 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_480_1 : expNegUpper (539567473386701455812271 / 4886760997917966848000 : ℝ) ≤ (1117341345021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2369337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_480 : rowCell 4 480 ≤ (173618627609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (631787970541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1117341345021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_480_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_480_1
  · norm_num [gridPoint]

theorem exp_4_481_0 : expNegUpper (541218347659236706822439 / 4901712654138757632000 : ℝ) ≤ (223468263057 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2369337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_481_1 : expNegUpper (54182156898090593264107 / 490171265413875763200 : ℝ) ≤ (987961705863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (74113 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_481 : rowCell 4 481 ≤ (76760293893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (223468263057 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (987961705863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_481_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_481_1
  · norm_num [gridPoint]

theorem exp_4_482_0 : expNegUpper (54347680773703972736027 / 491668714866530355200 : ℝ) ≤ (98796167973 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (74113 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_482_1 : expNegUpper (544082212965897999488261 / 4916687148665303552000 : ℝ) ≤ (109187830597 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2373899 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_482 : rowCell 4 482 ≤ (135739650953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (98796167973 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (109187830597 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_482_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_482_1
  · norm_num [gridPoint]

theorem exp_4_483_0 : expNegUpper (545741822867189435735869 / 4931684481497604608000 : ℝ) ≤ (87350262181 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2373899 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_483_1 : expNegUpper (136587353833504075770727 / 1232921120374401152000 : ℝ) ≤ (77225076203 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (475237 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_483 : rowCell 4 483 ≤ (120009815357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (87350262181 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (77225076203 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_483_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_483_1
  · norm_num [gridPoint]

theorem exp_4_484_0 : expNegUpper (176778517110330476993 / 1595711178269568000 : ℝ) ≤ (15445014837 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (475237 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_484_1 : expNegUpper (707900885261418696973 / 6382844713078272000 : ℝ) ≤ (341344269283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1189237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_484 : rowCell 4 484 ≤ (212190959 / 2000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15445014837 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (341344269283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_484_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_484_1
  · norm_num [gridPoint]

theorem exp_4_485_0 : expNegUpper (550291558253883502916627 / 4961747662079472128000 : ℝ) ≤ (341344260417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1189237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_485_1 : expNegUpper (275451767594493103715413 / 2480873831039736064000 : ℝ) ≤ (18858501481 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2380767 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_485 : rowCell 4 485 ≤ (9378798417 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (341344260417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18858501481 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_485_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_485_1
  · norm_num [gridPoint]

theorem exp_4_486_0 : expNegUpper (276288149247552577589957 / 2488406754914519296000 : ℝ) ≤ (150868007953 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2380767 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_486_1 : expNegUpper (22127618906420604065689 / 199072540393161543680 : ℝ) ≤ (533411188599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (297883 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_486 : rowCell 4 486 ≤ (82902545851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (150868007953 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (533411188599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_486_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_486_1
  · norm_num [gridPoint]

theorem exp_4_487_0 : expNegUpper (22194705350321123287889 / 199676087835374407680 : ℝ) ≤ (1041818701 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (297883 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_487_1 : expNegUpper (69435501060565602439667 / 623987774485545024000 : ℝ) ≤ (117863040933 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2385363 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_487 : rowCell 4 487 ≤ (73275537461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1041818701 / 1953125000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (117863040933 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_487_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_487_1
  · norm_num [gridPoint]

theorem exp_4_488_0 : expNegUpper (69645696754373866337203 / 625876715030679616000 : ℝ) ≤ (471452151707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2385363 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_488_1 : expNegUpper (557784152653354007785223 / 5007013720245436928000 : ℝ) ≤ (2604137107 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2387667 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_488 : rowCell 4 488 ≤ (64762077273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (471452151707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2604137107 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_488_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_488_1
  · norm_num [gridPoint]

theorem exp_4_489_0 : expNegUpper (22378805172733293896407 / 200885923316490752000 : ℝ) ≤ (104165481639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2387667 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_489_1 : expNegUpper (11201818303186826263499 / 100442961658245376000 : ℝ) ≤ (184107230033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1194987 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_489 : rowCell 4 489 ≤ (2289355651 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (104165481639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (184107230033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_489_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_489_1
  · norm_num [gridPoint]

theorem exp_4_490_0 : expNegUpper (280890654800195489531971 / 2518652641942427904000 : ℝ) ≤ (92053612697 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1194987 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_490_1 : expNegUpper (562404305994825382415581 / 5037305283884855808000 : ℝ) ≤ (162689229457 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (598071 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_490 : rowCell 4 490 ≤ (25288709063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (92053612697 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (162689229457 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_490_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_490_1
  · norm_num [gridPoint]

theorem exp_4_491_0 : expNegUpper (564099124873505472387989 / 5052485323163197952000 : ℝ) ≤ (81344612691 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (598071 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_491_1 : expNegUpper (28236216757607243111809 / 252624266158159897600 : ℝ) ≤ (71876652589 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1197299 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_491 : rowCell 4 491 ≤ (2793258081 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (81344612691 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (71876652589 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_491_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_491_1
  · norm_num [gridPoint]

theorem exp_4_492_0 : expNegUpper (28321179256500723705569 / 253384410037364761600 : ℝ) ≤ (143753301599 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1197299 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_492_1 : expNegUpper (567051012623638399365811 / 5067688200747295232000 : ℝ) ≤ (127012973603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (479383 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_492 : rowCell 4 492 ≤ (39489040109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (143753301599 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (127012973603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_492_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_492_1
  · norm_num [gridPoint]

theorem exp_4_493_0 : expNegUpper (24728465233141592650573 / 220996257245093376000 : ℝ) ≤ (254025940919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (479383 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_493_1 : expNegUpper (12377920617427057402903 / 110498128622546688000 : ℝ) ≤ (224429355447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (599809 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_493 : rowCell 4 493 ≤ (17444695037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (254025940919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (224429355447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_493_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_493_1
  · norm_num [gridPoint]

theorem exp_4_494_0 : expNegUpper (11421849611251411793449 / 101963249416655104000 : ℝ) ≤ (112214674963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (599809 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_494_1 : expNegUpper (22868974099140089298737 / 203926498833310208000 : ℝ) ≤ (7930721563 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (60039 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_494 : rowCell 4 494 ≤ (15411736687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (112214674963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7930721563 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_494_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_494_1
  · norm_num [gridPoint]

theorem exp_4_495_0 : expNegUpper (573436935723294996968257 / 5113433863334117888000 : ℝ) ≤ (198268034227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (60039 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_495_1 : expNegUpper (35879439677909363868721 / 319589616458382368000 : ℝ) ≤ (175144843107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (150243 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_495 : rowCell 4 495 ≤ (3403700313 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (198268034227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (175144843107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_495_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_495_1
  · norm_num [gridPoint]

theorem exp_4_496_0 : expNegUpper (35986754739798031223729 / 320545505883827232000 : ℝ) ≤ (2736638107 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (150243 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_496_1 : expNegUpper (115284881099625211111187 / 1025745618828247142400 : ℝ) ≤ (154708337511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2406219 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_496 : rowCell 4 496 ≤ (24053189973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2736638107 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (154708337511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_496_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_496_1
  · norm_num [gridPoint]

theorem exp_4_497_0 : expNegUpper (115629182179065948847147 / 1028809032650821734400 : ℝ) ≤ (38677083443 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2406219 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_497_1 : expNegUpper (289392237212784790083343 / 2572022581627054336000 : ℝ) ≤ (34161893943 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1204277 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_497 : rowCell 4 497 ≤ (2124593469 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38677083443 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34161893943 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_497_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_497_1
  · norm_num [gridPoint]

theorem exp_4_498_0 : expNegUpper (290255225445658688832767 / 2579692535336368384000 : ℝ) ≤ (13664757249 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1204277 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_498_1 : expNegUpper (581151251621219042460853 / 5159385070672736768000 : ℝ) ≤ (188574143 / 1562500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (602723 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_498 : rowCell 4 498 ≤ (18765101151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13664757249 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (188574143 / 1562500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_498_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_498_1
  · norm_num [gridPoint]

theorem exp_4_499_0 : expNegUpper (932610729307312074557 / 8279596506235392000 : ℝ) ≤ (120687448639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (602723 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_499_1 : expNegUpper (233409898830965235667 / 2069899126558848000 : ℝ) ≤ (53292292661 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1206617 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_499 : rowCell 4 499 ≤ (16572880907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (120687448639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (53292292661 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_499_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_499_1
  · norm_num [gridPoint]

theorem exp_4_500_0 : expNegUpper (146314921416231599440643 / 1297533350106814592000 : ℝ) ≤ (13323072849 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1206617 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_500_1 : expNegUpper (585904970786490367015691 / 5190133400427258368000 : ℝ) ≤ (23530920347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2415579 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_500 : rowCell 4 500 ≤ (3658956737 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13323072849 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23530920347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_500_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_500_1
  · norm_num [gridPoint]

theorem exp_4_501_0 : expNegUpper (587644400427225077887939 / 5205541822763151872000 : ℝ) ≤ (94123679167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2415579 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_501_1 : expNegUpper (58829193274078952273449 / 520554182276315187200 : ℝ) ≤ (3324572031 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (302241 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_501 : rowCell 4 501 ≤ (2584870547 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (94123679167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3324572031 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_501_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_501_1
  · norm_num [gridPoint]

theorem exp_4_502_0 : expNegUpper (59003586009630473370329 / 522097308340480051200 : ℝ) ≤ (41557149413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (302241 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_502_1 : expNegUpper (590685642932649203052961 / 5220973083404800512000 : ℝ) ≤ (36694001839 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (60507 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_502 : rowCell 4 502 ≤ (11412288507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (41557149413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36694001839 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_502_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_502_1
  · norm_num [gridPoint]

theorem exp_4_503_0 : expNegUpper (592434074664504011937689 / 5236427182352204288000 : ℝ) ≤ (4586750123 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (60507 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_503_1 : expNegUpper (74135763919301006837521 / 654553397794025536000 : ℝ) ≤ (64795818813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (605659 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_503 : rowCell 4 503 ≤ (10076488361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4586750123 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64795818813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_503_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_503_1
  · norm_num [gridPoint]

theorem exp_4_504_0 : expNegUpper (2974195270620807796601 / 26259520598026816000 : ℝ) ≤ (2024869291 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (605659 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_504_1 : expNegUpper (23819733919936188976207 / 210076164784214528000 : ℝ) ≤ (14301500653 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (484999 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_504 : rowCell 4 504 ≤ (111206029 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2024869291 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14301500653 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_504_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_504_1
  · norm_num [gridPoint]

theorem exp_4_505_0 : expNegUpper (597250808467616022579887 / 5267403895164277248000 : ℝ) ≤ (28603000647 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (484999 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_505_1 : expNegUpper (298953681428488929448523 / 2633701947582138624000 : ℝ) ≤ (12625513801 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2427357 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_505 : rowCell 4 505 ≤ (7854168249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28603000647 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12625513801 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_505_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_505_1
  · norm_num [gridPoint]

theorem exp_4_506_0 : expNegUpper (299834673843603024222907 / 2641463254514473216000 : ℝ) ≤ (1578189189 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2427357 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_506_1 : expNegUpper (120065633184493220980969 / 1056585301805789286400 : ℝ) ≤ (2786310243 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2429723 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_506 : rowCell 4 506 ≤ (1386707819 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1578189189 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2786310243 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_506_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_506_1
  · norm_num [gridPoint]

theorem exp_4_507_0 : expNegUpper (120418936355054056729409 / 1059694392239874150400 : ℝ) ≤ (44580962873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2429723 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_507_1 : expNegUpper (150688941796802027289409 / 1324617990299842688000 : ℝ) ≤ (39351648129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2432093 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_507 : rowCell 4 507 ≤ (6120441403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (44580962873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39351648129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_507_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_507_1
  · norm_num [gridPoint]

theorem exp_4_508_0 : expNegUpper (151131705181036843728161 / 1328510062918887552000 : ℝ) ≤ (19675823619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2432093 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_508_1 : expNegUpper (605190176643542518384483 / 5314040251675550208000 : ℝ) ≤ (34733583071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1217233 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_508 : rowCell 4 508 ≤ (1350590389 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19675823619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34733583071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_508_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_508_1
  · norm_num [gridPoint]

theorem exp_4_509_0 : expNegUpper (24278630981047038758867 / 213185255218299392000 : ℝ) ≤ (34733582289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1217233 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_509_1 : expNegUpper (12152628085676159586289 / 106592627609149696000 : ℝ) ≤ (6131116231 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1218421 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_509 : rowCell 4 509 ≤ (4768236547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34733582289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6131116231 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_509_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_509_1
  · norm_num [gridPoint]

theorem exp_4_510_0 : expNegUpper (304705776586847356276601 / 2672622673772587264000 : ℝ) ≤ (30655580469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1218421 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_510_1 : expNegUpper (610079460100343138676601 / 5345245347545174528000 : ℝ) ≤ (27054713777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1219611 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_510 : rowCell 4 510 ≤ (2104143253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30655580469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27054713777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_510_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_510_1
  · norm_num [gridPoint]

theorem exp_4_511_0 : expNegUpper (611864166659042252386289 / 5360882152938619392000 : ℝ) ≤ (1082188527 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1219611 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_511_1 : expNegUpper (1196356160323216100 / 10470472954958241 : ℝ) ≤ (4775071389 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1220803 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_511 : rowCell 4 511 ≤ (3713866471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1082188527 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4775071389 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_511_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_511_1
  · norm_num [gridPoint]

theorem sum_4_480_2 : blockSum (rowCell 4) 480 2 ≤ (65427843079 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_480) (by simpa only [blockSum_one] using cell_4_481) (by norm_num)

theorem sum_4_482_2 : blockSum (rowCell 4) 482 2 ≤ (25574946631 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_482) (by simpa only [blockSum_one] using cell_4_483) (by norm_num)

theorem sum_4_480_4 : blockSum (rowCell 4) 480 4 ≤ (116577736341 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_480_2 sum_4_482_2 (by norm_num)

theorem sum_4_484_2 : blockSum (rowCell 4) 484 2 ≤ (19988346367 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_484) (by simpa only [blockSum_one] using cell_4_485) (by norm_num)

theorem sum_4_486_2 : blockSum (rowCell 4) 486 2 ≤ (9761130207 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_486) (by simpa only [blockSum_one] using cell_4_487) (by norm_num)

theorem sum_4_484_4 : blockSum (rowCell 4) 484 4 ≤ (178030773491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_484_2 sum_4_486_2 (by norm_num)

theorem sum_4_480_8 : blockSum (rowCell 4) 480 8 ≤ (938950228687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_480_4 sum_4_484_4 (by norm_num)

theorem sum_4_488_2 : blockSum (rowCell 4) 488 2 ≤ (30498992137 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_488) (by simpa only [blockSum_one] using cell_4_489) (by norm_num)

theorem sum_4_490_2 : blockSum (rowCell 4) 490 2 ≤ (47634773711 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_490) (by simpa only [blockSum_one] using cell_4_491) (by norm_num)

theorem sum_4_488_4 : blockSum (rowCell 4) 488 4 ≤ (21726551597 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_488_2 sum_4_490_2 (by norm_num)

theorem sum_4_492_2 : blockSum (rowCell 4) 492 2 ≤ (74378430183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_492) (by simpa only [blockSum_one] using cell_4_493) (by norm_num)

theorem sum_4_494_2 : blockSum (rowCell 4) 494 2 ≤ (29026537939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_494) (by simpa only [blockSum_one] using cell_4_495) (by norm_num)

theorem sum_4_492_4 : blockSum (rowCell 4) 492 4 ≤ (132431506061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_492_2 sum_4_494_2 (by norm_num)

theorem sum_4_488_8 : blockSum (rowCell 4) 488 8 ≤ (349697022031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_488_4 sum_4_492_4 (by norm_num)

theorem sum_4_480_16 : blockSum (rowCell 4) 480 16 ≤ (644323625359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_480_8 sum_4_488_8 (by norm_num)

theorem sum_4_496_2 : blockSum (rowCell 4) 496 2 ≤ (45299124663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_496) (by simpa only [blockSum_one] using cell_4_497) (by norm_num)

theorem sum_4_498_2 : blockSum (rowCell 4) 498 2 ≤ (17668991029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_498) (by simpa only [blockSum_one] using cell_4_499) (by norm_num)

theorem sum_4_496_4 : blockSum (rowCell 4) 496 4 ≤ (80637106721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_496_2 sum_4_498_2 (by norm_num)

theorem sum_4_500_2 : blockSum (rowCell 4) 500 2 ≤ (27560179683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_500) (by simpa only [blockSum_one] using cell_4_501) (by norm_num)

theorem sum_4_502_2 : blockSum (rowCell 4) 502 2 ≤ (5372194217 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_502) (by simpa only [blockSum_one] using cell_4_503) (by norm_num)

theorem sum_4_500_4 : blockSum (rowCell 4) 500 4 ≤ (49048956551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_500_2 sum_4_502_2 (by norm_num)

theorem sum_4_496_8 : blockSum (rowCell 4) 496 8 ≤ (16210757909 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_496_4 sum_4_500_4 (by norm_num)

theorem sum_4_504_2 : blockSum (rowCell 4) 504 2 ≤ (16750650569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_504) (by simpa only [blockSum_one] using cell_4_505) (by norm_num)

theorem sum_4_506_2 : blockSum (rowCell 4) 506 2 ≤ (6526990249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_506) (by simpa only [blockSum_one] using cell_4_507) (by norm_num)

theorem sum_4_504_4 : blockSum (rowCell 4) 504 4 ≤ (29804631067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_504_2 sum_4_506_2 (by norm_num)

theorem sum_4_508_2 : blockSum (rowCell 4) 508 2 ≤ (10170598103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_508) (by simpa only [blockSum_one] using cell_4_509) (by norm_num)

theorem sum_4_510_2 : blockSum (rowCell 4) 510 2 ≤ (7922152977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_510) (by simpa only [blockSum_one] using cell_4_511) (by norm_num)

theorem sum_4_508_4 : blockSum (rowCell 4) 508 4 ≤ (452318777 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_508_2 sum_4_510_2 (by norm_num)

theorem sum_4_504_8 : blockSum (rowCell 4) 504 8 ≤ (47897382147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_504_4 sum_4_508_4 (by norm_num)

theorem sum_4_496_16 : blockSum (rowCell 4) 496 16 ≤ (177583445419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_496_8 sum_4_504_8 (by norm_num)

theorem sum_4_480_32 : blockSum (rowCell 4) 480 32 ≤ (1466230696137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_480_16 sum_4_496_16 (by norm_num)

#print axioms sum_4_480_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
