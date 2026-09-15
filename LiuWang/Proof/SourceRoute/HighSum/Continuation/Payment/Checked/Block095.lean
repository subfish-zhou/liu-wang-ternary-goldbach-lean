import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_480_0 : expNegUpper (16892358996270845981041 / 152711281184936464000 : ℝ) ≤ (912807915119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1186541 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_480_1 : expNegUpper (541154101381153423812271 / 4886760997917966848000 : ℝ) ≤ (807568985447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (475071 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_480 : rowCell 5 480 ≤ (125451429241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (912807915119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (807568985447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_480_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_480_1
  · norm_num [gridPoint]

theorem exp_5_481_0 : expNegUpper (542809830143235426822439 / 4901712654138757632000 : ℝ) ≤ (807568963487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (475071 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_481_1 : expNegUpper (54341062422013127664107 / 490171265413875763200 : ℝ) ≤ (357206154493 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (237763 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_481 : rowCell 5 481 ≤ (55492120897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (807568963487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (357206154493 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_481_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_481_1
  · norm_num [gridPoint]

theorem exp_5_482_0 : expNegUpper (54507071746581182336027 / 491668714866530355200 : ℝ) ≤ (357206144839 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (237763 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_482_1 : expNegUpper (545673695449896719488261 / 4916687148665303552000 : ℝ) ≤ (631956873143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2379909 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_482 : rowCell 5 482 ≤ (49089224491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (357206144839 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (631956873143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_482_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_482_1
  · norm_num [gridPoint]

theorem exp_5_483_0 : expNegUpper (547338159840734907735869 / 4931684481497604608000 : ℝ) ≤ (631956856167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2379909 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_483_1 : expNegUpper (136985831265697099770727 / 1232921120374401152000 : ℝ) ≤ (22359150653 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (148887 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_483 : rowCell 5 483 ≤ (43422047787 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (631956856167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22359150653 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_483_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_483_1
  · norm_num [gridPoint]

theorem exp_5_484_0 : expNegUpper (177294247503336556993 / 1595711178269568000 : ℝ) ≤ (558978751401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (148887 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_484_1 : expNegUpper (709960674904703176973 / 6382844713078272000 : ℝ) ≤ (61799176649 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1192239 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_484 : rowCell 5 484 ≤ (9601605579 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (558978751401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (61799176649 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_484_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_484_1
  · norm_num [gridPoint]

theorem exp_5_485_0 : expNegUpper (551892749716975726916627 / 4961747662079472128000 : ℝ) ≤ (61799175009 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1192239 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_485_1 : expNegUpper (276251149703652527715413 / 2480873831039736064000 : ℝ) ≤ (437239788729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (149173 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_485 : rowCell 5 485 ≤ (33967764571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (61799175009 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (437239788729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_485_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_485_1
  · norm_num [gridPoint]

theorem exp_5_486_0 : expNegUpper (277089958601485377589957 / 2488406754914519296000 : ℝ) ≤ (437239777197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (149173 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_486_1 : expNegUpper (22191666564944293025689 / 199072540393161543680 : ℝ) ≤ (386666411627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2389061 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_486 : rowCell 5 486 ≤ (30039989759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (437239777197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (386666411627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_486_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_486_1
  · norm_num [gridPoint]

theorem exp_5_487_0 : expNegUpper (22258947188426682327889 / 199676087835374407680 : ℝ) ≤ (38666640149 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2389061 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_487_1 : expNegUpper (69635953399048802439667 / 623987774485545024000 : ℝ) ≤ (2671241543 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1195679 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_487 : rowCell 5 487 ≤ (1062581921 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38666640149 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2671241543 / 7812500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_487_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_487_1
  · norm_num [gridPoint]

theorem exp_5_488_0 : expNegUpper (69846755904050410337203 / 625876715030679616000 : ℝ) ≤ (170959454297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1195679 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_488_1 : expNegUpper (559390198605992983785223 / 5007013720245436928000 : ℝ) ≤ (37791129341 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1196829 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_488 : rowCell 5 488 ≤ (11744784711 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (170959454297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37791129341 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_488_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_488_1
  · norm_num [gridPoint]

theorem exp_5_489_0 : expNegUpper (22443241190420723016407 / 200885923316490752000 : ℝ) ≤ (302329026897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1196829 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_489_1 : expNegUpper (11233987767135073303499 / 100442961658245376000 : ℝ) ≤ (267304805383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2395961 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_489 : rowCell 5 489 ≤ (41538210831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (302329026897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (267304805383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_489_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_489_1
  · norm_num [gridPoint]

theorem exp_5_490_0 : expNegUpper (281697318643675041531971 / 2518652641942427904000 : ℝ) ≤ (267304798501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2395961 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_490_1 : expNegUpper (564015206437011110415581 / 5037305283884855808000 : ℝ) ≤ (236321911463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (599567 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_490 : rowCell 5 490 ≤ (4590614021 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (267304798501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (236321911463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_490_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_490_1
  · norm_num [gridPoint]

theorem exp_5_491_0 : expNegUpper (565714879805237952387989 / 5052485323163197952000 : ℝ) ≤ (47264381083 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (599567 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_491_1 : expNegUpper (28316883141955198311809 / 252624266158159897600 : ℝ) ≤ (208915982069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2400579 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_491 : rowCell 5 491 ≤ (16233573387 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47264381083 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (208915982069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_491_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_491_1
  · norm_num [gridPoint]

theorem exp_5_492_0 : expNegUpper (28402088365326016505569 / 253384410037364761600 : ℝ) ≤ (41783195351 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2400579 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_492_1 : expNegUpper (568666767555370879365811 / 5067688200747295232000 : ℝ) ≤ (92337885607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2402893 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_492 : rowCell 5 492 ≤ (717526597 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (41783195351 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (92337885607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_492_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_492_1
  · norm_num [gridPoint]

theorem exp_5_493_0 : expNegUpper (570375309783535862963179 / 5082913916637147648000 : ℝ) ≤ (36935153309 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2402893 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_493_1 : expNegUpper (285501265289075248266769 / 2541456958318573824000 : ℝ) ≤ (163237108231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2405211 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_493 : rowCell 5 493 ≤ (25370119407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36935153309 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (163237108231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_493_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_493_1
  · norm_num [gridPoint]

theorem exp_5_494_0 : expNegUpper (11454310344572463953449 / 101963249416655104000 : ℝ) ≤ (318822469 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2405211 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_494_1 : expNegUpper (22933798475991258578737 / 203926498833310208000 : ℝ) ≤ (144277533727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (601883 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_494 : rowCell 5 494 ≤ (5606060919 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (318822469 / 1953125000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (144277533727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_494_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_494_1
  · norm_num [gridPoint]

theorem exp_5_495_0 : expNegUpper (575062399634120980968257 / 5113433863334117888000 : ℝ) ≤ (72138765061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (601883 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_495_1 : expNegUpper (35980879469537651868721 / 319589616458382368000 : ℝ) ≤ (127511543819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2409857 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_495 : rowCell 5 495 ≤ (9909551729 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (72138765061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (127511543819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_495_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_495_1
  · norm_num [gridPoint]

theorem exp_5_496_0 : expNegUpper (36088497937022991223729 / 320545505883827232000 : ℝ) ≤ (31877885163 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2409857 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_496_1 : expNegUpper (115609973881790407911187 / 1025745618828247142400 : ℝ) ≤ (22537274797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (482437 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_496 : rowCell 5 496 ≤ (17515447739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31877885163 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22537274797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_496_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_496_1
  · norm_num [gridPoint]

theorem exp_5_497_0 : expNegUpper (115955245859140496047147 / 1028809032650821734400 : ℝ) ≤ (112686371203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (482437 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_497_1 : expNegUpper (290206182790584470083343 / 2572022581627054336000 : ℝ) ≤ (1991565233 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (603629 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_497 : rowCell 5 497 ≤ (3095705547 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (112686371203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1991565233 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_497_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_497_1
  · norm_num [gridPoint]

theorem exp_5_498_0 : expNegUpper (291071598268231744832767 / 2579692535336368384000 : ℝ) ≤ (99578259207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (603629 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_498_1 : expNegUpper (582781570021591778460853 / 5159385070672736768000 : ℝ) ≤ (439945667 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2416851 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_498 : rowCell 5 498 ≤ (13677582787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (99578259207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (439945667 / 5000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_498_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_498_1
  · norm_num [gridPoint]

theorem exp_5_499_0 : expNegUpper (935227005931183255357 / 8279596506235392000 : ℝ) ≤ (43994565627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2416851 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_499_1 : expNegUpper (234062997089023680467 / 2069899126558848000 : ℝ) ≤ (38871834407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (241919 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_499 : rowCell 5 499 ≤ (6042692341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43994565627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38871834407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_499_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_499_1
  · norm_num [gridPoint]

theorem exp_5_500_0 : expNegUpper (146724321449904815440643 / 1297533350106814592000 : ℝ) ≤ (4858979183 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (241919 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_500_1 : expNegUpper (587540143676409855015691 / 5190133400427258368000 : ℝ) ≤ (68686698339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (605383 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_500 : rowCell 5 500 ≤ (5338916897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4858979183 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (68686698339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_500_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_500_1
  · norm_num [gridPoint]

theorem exp_5_501_0 : expNegUpper (589284427806691317887939 / 5205541822763151872000 : ℝ) ≤ (68686696683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (605383 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_501_1 : expNegUpper (58992953287548238673449 / 520554182276315187200 : ℝ) ≤ (60680897357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1211939 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_501 : rowCell 5 501 ≤ (9433601187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (68686696683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (60680897357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_501_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_501_1
  · norm_num [gridPoint]

theorem exp_5_502_0 : expNegUpper (59167831472054434970329 / 522097308340480051200 : ℝ) ≤ (30340447951 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1211939 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_502_1 : expNegUpper (592325670312115443052961 / 5220973083404800512000 : ℝ) ≤ (10720948583 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2426227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_502 : rowCell 5 502 ≤ (4166905731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30340447951 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10720948583 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_502_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_502_1
  · norm_num [gridPoint]

theorem exp_5_503_0 : expNegUpper (594078956533517003937689 / 5236427182352204288000 : ℝ) ≤ (26802370819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2426227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_503_1 : expNegUpper (74341070747330958837521 / 654553397794025536000 : ℝ) ≤ (23675351673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2428579 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_503 : rowCell 5 503 ≤ (7361761751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26802370819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23675351673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_503_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_503_1
  · norm_num [gridPoint]

theorem exp_5_504_0 : expNegUpper (2982431816189739636601 / 26259520598026816000 : ℝ) ≤ (1894028089 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2428579 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_504_1 : expNegUpper (23885529194696708656207 / 210076164784214528000 : ℝ) ≤ (41823634349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (303867 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_504 : rowCell 5 504 ≤ (6502672741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1894028089 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41823634349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_504_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_504_1
  · norm_num [gridPoint]

theorem exp_5_505_0 : expNegUpper (598900544826175766579887 / 5267403895164277248000 : ℝ) ≤ (8364726673 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (303867 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_505_1 : expNegUpper (299777335985382113448523 / 2633701947582138624000 : ℝ) ≤ (36939358107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (486659 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_505 : rowCell 5 505 ≤ (2871734051 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8364726673 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36939358107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_505_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_505_1
  · norm_num [gridPoint]

theorem exp_5_506_0 : expNegUpper (300660755645269584222907 / 2641463254514473216000 : ℝ) ≤ (18469678621 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (486659 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_506_1 : expNegUpper (120395580456205169780969 / 1056585301805789286400 : ℝ) ≤ (16311702327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1217829 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_506 : rowCell 5 506 ≤ (634072387 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18469678621 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16311702327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_506_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_506_1
  · norm_num [gridPoint]

theorem exp_5_507_0 : expNegUpper (120749854524675355929409 / 1059694392239874150400 : ℝ) ≤ (4077925487 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1217829 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_507_1 : expNegUpper (151101982697635307289409 / 1324617990299842688000 : ℝ) ≤ (14404948527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (97521 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_507 : rowCell 5 507 ≤ (8959543 / 2000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4077925487 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14404948527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_507_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_507_1
  · norm_num [gridPoint]

theorem exp_5_508_0 : expNegUpper (151545959704256811728161 / 1328510062918887552000 : ℝ) ≤ (7202474097 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (97521 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_508_1 : expNegUpper (606844767491649014384483 / 5314040251675550208000 : ℝ) ≤ (25440564023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (488079 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_508 : rowCell 5 508 ≤ (1977996157 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7202474097 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25440564023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_508_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_508_1
  · norm_num [gridPoint]

theorem exp_5_509_0 : expNegUpper (24345008794553168678867 / 213185255218299392000 : ℝ) ≤ (25440563439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (488079 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_509_1 : expNegUpper (12185768447533757026289 / 106592627609149696000 : ℝ) ≤ (22463865517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2442769 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_509 : rowCell 5 509 ≤ (3493233999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25440563439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22463865517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_509_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_509_1
  · norm_num [gridPoint]

theorem exp_5_510_0 : expNegUpper (305536712878060668276601 / 2672622673772587264000 : ℝ) ≤ (22463865003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2442769 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_510_1 : expNegUpper (611738905437996386676601 / 5345245347545174528000 : ℝ) ≤ (19834218391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1222573 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_510 : rowCell 5 510 ≤ (771103561 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22463865003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19834218391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_510_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_510_1
  · norm_num [gridPoint]

theorem exp_5_511_0 : expNegUpper (613528466486242252386289 / 5360882152938619392000 : ℝ) ≤ (991710897 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1222573 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_511_1 : expNegUpper (1199602005210768100 / 10470472954958241 : ℝ) ≤ (17511310771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1223763 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_511 : rowCell 5 511 ≤ (2723269507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (991710897 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17511310771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_511_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_511_1
  · norm_num [gridPoint]

theorem sum_5_480_2 : blockSum (rowCell 5) 480 2 ≤ (47287134207 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_480) (by simpa only [blockSum_one] using cell_5_481) (by norm_num)

theorem sum_5_482_2 : blockSum (rowCell 5) 482 2 ≤ (46255636139 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_482) (by simpa only [blockSum_one] using cell_5_483) (by norm_num)

theorem sum_5_480_4 : blockSum (rowCell 5) 480 4 ≤ (421458215591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_480_2 sum_5_482_2 (by norm_num)

theorem sum_5_484_2 : blockSum (rowCell 5) 484 2 ≤ (72374186887 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_484) (by simpa only [blockSum_one] using cell_5_485) (by norm_num)

theorem sum_5_486_2 : blockSum (rowCell 5) 486 2 ≤ (7075567223 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_486) (by simpa only [blockSum_one] using cell_5_487) (by norm_num)

theorem sum_5_484_4 : blockSum (rowCell 5) 484 4 ≤ (128978724671 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_484_2 sum_5_486_2 (by norm_num)

theorem sum_5_480_8 : blockSum (rowCell 5) 480 8 ≤ (679415664933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_480_4 sum_5_484_4 (by norm_num)

theorem sum_5_488_2 : blockSum (rowCell 5) 488 2 ≤ (3540693987 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_488) (by simpa only [blockSum_one] using cell_5_489) (by norm_num)

theorem sum_5_490_2 : blockSum (rowCell 5) 490 2 ≤ (34596029471 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_490) (by simpa only [blockSum_one] using cell_5_491) (by norm_num)

theorem sum_5_488_4 : blockSum (rowCell 5) 488 4 ≤ (157709408617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_488_2 sum_5_490_2 (by norm_num)

theorem sum_5_492_2 : blockSum (rowCell 5) 492 2 ≤ (54071183287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_492) (by simpa only [blockSum_one] using cell_5_493) (by norm_num)

theorem sum_5_494_2 : blockSum (rowCell 5) 494 2 ≤ (21121673567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_494) (by simpa only [blockSum_one] using cell_5_495) (by norm_num)

theorem sum_5_492_4 : blockSum (rowCell 5) 492 4 ≤ (96314530421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_492_2 sum_5_494_2 (by norm_num)

theorem sum_5_488_8 : blockSum (rowCell 5) 488 8 ≤ (127011969519 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_488_4 sum_5_492_4 (by norm_num)

theorem sum_5_480_16 : blockSum (rowCell 5) 480 16 ≤ (933439603971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_480_8 sum_5_488_8 (by norm_num)

theorem sum_5_496_2 : blockSum (rowCell 5) 496 2 ≤ (16496987737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_496) (by simpa only [blockSum_one] using cell_5_497) (by norm_num)

theorem sum_5_498_2 : blockSum (rowCell 5) 498 2 ≤ (25762967469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_498) (by simpa only [blockSum_one] using cell_5_499) (by norm_num)

theorem sum_5_496_4 : blockSum (rowCell 5) 496 4 ≤ (58756942943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_496_2 sum_5_498_2 (by norm_num)

theorem sum_5_500_2 : blockSum (rowCell 5) 500 2 ≤ (20111434981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_500) (by simpa only [blockSum_one] using cell_5_501) (by norm_num)

theorem sum_5_502_2 : blockSum (rowCell 5) 502 2 ≤ (15695573213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_502) (by simpa only [blockSum_one] using cell_5_503) (by norm_num)

theorem sum_5_500_4 : blockSum (rowCell 5) 500 4 ≤ (17903504097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_500_2 sum_5_502_2 (by norm_num)

theorem sum_5_496_8 : blockSum (rowCell 5) 496 8 ≤ (94563951137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_496_4 sum_5_500_4 (by norm_num)

theorem sum_5_504_2 : blockSum (rowCell 5) 504 2 ≤ (12246140843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_504) (by simpa only [blockSum_one] using cell_5_505) (by norm_num)

theorem sum_5_506_2 : blockSum (rowCell 5) 506 2 ≤ (2388087649 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_506) (by simpa only [blockSum_one] using cell_5_507) (by norm_num)

theorem sum_5_504_4 : blockSum (rowCell 5) 504 4 ≤ (21798491439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_504_2 sum_5_506_2 (by norm_num)

theorem sum_5_508_2 : blockSum (rowCell 5) 508 2 ≤ (7449226313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_508) (by simpa only [blockSum_one] using cell_5_509) (by norm_num)

theorem sum_5_510_2 : blockSum (rowCell 5) 510 2 ≤ (5807683751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_510) (by simpa only [blockSum_one] using cell_5_511) (by norm_num)

theorem sum_5_508_4 : blockSum (rowCell 5) 508 4 ≤ (828556879 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_508_2 sum_5_510_2 (by norm_num)

theorem sum_5_504_8 : blockSum (rowCell 5) 504 8 ≤ (35055401503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_504_4 sum_5_508_4 (by norm_num)

theorem sum_5_496_16 : blockSum (rowCell 5) 496 16 ≤ (405060477 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_496_8 sum_5_504_8 (by norm_num)

theorem sum_5_480_32 : blockSum (rowCell 5) 480 32 ≤ (1063058956611 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_480_16 sum_5_496_16 (by norm_num)

#print axioms sum_5_480_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
