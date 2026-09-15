import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_448_0 : expNegUpper (813871121866855472809 / 7674247611616968000 : ℝ) ≤ (21901457938921 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2289957 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_448_1 : expNegUpper (52147246043537751586967 / 491151847143485952000 : ℝ) ≤ (7761149051473 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (18337 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_448 : rowCell 3 448 ≤ (12047795577397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21901457938921 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7761149051473 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_448_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_448_1
  · norm_num [gridPoint]

theorem exp_3_449_0 : expNegUpper (30133445632184224847 / 283813597102592000 : ℝ) ≤ (77611488045597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (18337 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_449_1 : expNegUpper (15083923526107950639 / 141906798551296000 : ℝ) ≤ (34375942025457 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (286787 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_449 : rowCell 3 449 ≤ (533647429581 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (77611488045597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34375942025457 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_449_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_449_1
  · norm_num [gridPoint]

theorem exp_3_450_0 : expNegUpper (236443317557809809954711 / 2224415561735190784000 : ℝ) ≤ (34375940938817 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (286787 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_450_1 : expNegUpper (473426234625858045343141 / 4448831123470381568000 : ℝ) ≤ (6089882818317 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2296471 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_450 : rowCell 3 450 ≤ (4727123130347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34375940938817 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6089882818317 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_450_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_450_1
  · norm_num [gridPoint]

theorem exp_3_451_0 : expNegUpper (52771601947318968788021 / 495899736724279808000 : ℝ) ≤ (15224706567607 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2296471 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_451_1 : expNegUpper (2641589431606289859083 / 24794986836213990400 : ℝ) ≤ (13484634928923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45973 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_451 : rowCell 3 451 ≤ (523377743869 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15224706567607 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13484634928923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_451_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_451_1
  · norm_num [gridPoint]

theorem exp_3_452_0 : expNegUpper (23850422261298522875587 / 223869348793620505600 : ℝ) ≤ (26969269016183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45973 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_452_1 : expNegUpper (477552209373034492073211 / 4477386975872410112000 : ℝ) ≤ (597125373267 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (71901 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_452 : rowCell 3 452 ≤ (3708340074801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26969269016183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (597125373267 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_452_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_452_1
  · norm_num [gridPoint]

theorem exp_3_453_0 : expNegUpper (15454152522847015545069 / 144893521275227648000 : ℝ) ≤ (9554005676007 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (71901 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_453_1 : expNegUpper (7735880317256510393339 / 72446760637613824000 : ℝ) ≤ (42303673608431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2303017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_453 : rowCell 3 453 ≤ (6568255274591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9554005676007 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42303673608431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_453_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_453_1
  · norm_num [gridPoint]

theorem exp_3_454_0 : expNegUpper (1069233947700156531061 / 10013409292216576000 : ℝ) ≤ (8460734460991 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2303017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_454_1 : expNegUpper (2140903193653681236913 / 20026818584433152000 : ℝ) ≤ (18729969054281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1152603 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_454 : rowCell 3 454 ≤ (5816434133973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8460734460991 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18729969054281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_454_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_454_1
  · norm_num [gridPoint]

theorem exp_3_455_0 : expNegUpper (483238099988747975481737 / 4520392041768616448000 : ℝ) ≤ (1872996848083 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1152603 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_455_1 : expNegUpper (60473517008987130069687 / 565049005221077056000 : ℝ) ≤ (33168252521547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2307399 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_455 : rowCell 3 455 ≤ (515027103213 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1872996848083 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33168252521547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_455_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_455_1
  · norm_num [gridPoint]

theorem exp_3_456_0 : expNegUpper (60665901096453592267383 / 566846592543191104000 : ℝ) ≤ (16584125756239 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2307399 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_456_1 : expNegUpper (97175868432339715574459 / 906954548069105766400 : ℝ) ≤ (5873200735843 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (461919 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_456 : rowCell 3 456 ≤ (4560054071699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16584125756239 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5873200735843 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_456_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_456_1
  · norm_num [gridPoint]

theorem exp_3_457_0 : expNegUpper (10831613617912252748411 / 101092806160626585600 : ℝ) ≤ (29366002791473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (461919 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_457_1 : expNegUpper (27109824824101196498827 / 252732015401566464000 : ℝ) ≤ (649941091203 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1155897 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_457 : rowCell 3 457 ≤ (252322927447 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29366002791473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (649941091203 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_457_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_457_1
  · norm_num [gridPoint]

theorem exp_3_458_0 : expNegUpper (244762161042177264414547 / 2281801326208309504000 : ℝ) ≤ (25997642867169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1155897 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_458_1 : expNegUpper (490080660080604564606333 / 4563602652416619008000 : ℝ) ≤ (11506948400281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2313997 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_458 : rowCell 3 458 ≤ (3573965506377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25997642867169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11506948400281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_458_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_458_1
  · norm_num [gridPoint]

theorem exp_3_459_0 : expNegUpper (19665293863955074012797 / 183122074636431872000 : ℝ) ≤ (23013896113603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2313997 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_459_1 : expNegUpper (4921907918943863074837 / 45780518659107968000 : ℝ) ≤ (4074211073297 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2316203 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_459 : rowCell 3 459 ≤ (790917410149 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23013896113603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4074211073297 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_459_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_459_1
  · norm_num [gridPoint]

theorem exp_3_460_0 : expNegUpper (13715186009498805135557 / 127570108825298048000 : ℝ) ≤ (20371054762243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2316203 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_460_1 : expNegUpper (54923028029722823593339 / 510280435301192192000 : ℝ) ≤ (2253794206609 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2318413 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_460 : rowCell 3 460 ≤ (175016575181 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20371054762243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2253794206609 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_460_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_460_1
  · norm_num [gridPoint]

theorem exp_3_461_0 : expNegUpper (495867381305933579238539 / 4607018807816417792000 : ℝ) ≤ (18030353121421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2318413 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_461_1 : expNegUpper (9928601023846010518089 / 92140376156328355840 : ℝ) ≤ (7978706099321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1160313 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_461 : rowCell 3 461 ≤ (1239209191511 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18030353121421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7978706099321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_461_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_461_1
  · norm_num [gridPoint]

theorem exp_3_462_0 : expNegUpper (9959888229662905602489 / 92430730724557219840 : ℝ) ≤ (3191482346249 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1160313 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_462_1 : expNegUpper (498559198661110294905961 / 4621536536227860992000 : ℝ) ≤ (7060872048029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2322843 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_462 : rowCell 3 462 ≤ (2193399067169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3191482346249 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7060872048029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_462_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_462_1
  · norm_num [gridPoint]

theorem exp_3_463_0 : expNegUpper (55569755207325637140761 / 515119678105006592000 : ℝ) ≤ (14121743685021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2322843 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_463_1 : expNegUpper (3477046560182453931067 / 32194979881562912000 : ℝ) ≤ (12496316567189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2325063 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_463 : rowCell 3 463 ≤ (388202573651 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14121743685021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12496316567189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_463_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_463_1
  · norm_num [gridPoint]

theorem exp_3_464_0 : expNegUpper (1255668868616571470987 / 11626601269920032000 : ℝ) ≤ (12496316205739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2325063 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_464_1 : expNegUpper (20113463168005135445463 / 186025620318720512000 : ℝ) ≤ (691072602971 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1163643 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_464 : rowCell 3 464 ≤ (1717540766389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12496316205739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (691072602971 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_464_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_464_1
  · norm_num [gridPoint]

theorem exp_3_465_0 : expNegUpper (504413673217577489237367 / 4665226751296721408000 : ℝ) ≤ (11057161329711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1163643 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_465_1 : expNegUpper (252492416127507000911903 / 2332613375648360704000 : ℝ) ≤ (2445757627159 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2329513 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_465 : rowCell 3 465 ≤ (1519685512463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11057161329711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2445757627159 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_465_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_465_1
  · norm_num [gridPoint]

theorem exp_3_466_0 : expNegUpper (28142565787284226862423 / 259990879607288064000 : ℝ) ≤ (9783030229189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2329513 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_466_1 : expNegUpper (11269766084961530219209 / 103996351842915225600 : ℝ) ≤ (1081885819573 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72867 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_466 : rowCell 3 466 ≤ (268904808303 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9783030229189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1081885819573 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_466_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_466_1
  · norm_num [gridPoint]

theorem exp_3_467_0 : expNegUpper (101745018059916603596521 / 938893550574280806400 : ℝ) ≤ (8655086310897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72867 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_467_1 : expNegUpper (127325128474307901746859 / 1173616938217851008000 : ℝ) ≤ (7656632981983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1166989 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_467 : rowCell 3 467 ≤ (594732612949 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8655086310897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7656632981983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_467_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_467_1
  · norm_num [gridPoint]

theorem exp_3_468_0 : expNegUpper (127722600398829234835851 / 1177280627779344512000 : ℝ) ≤ (765663276599 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1166989 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_468_1 : expNegUpper (511467962469240889921963 / 4709122511117378048000 : ℝ) ≤ (135457418323 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (467243 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_468 : rowCell 3 468 ≤ (1052212372509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (765663276599 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (135457418323 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_468_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_468_1
  · norm_num [gridPoint]

theorem exp_3_469_0 : expNegUpper (2280276124669584419267 / 20994667145196032000 : ℝ) ≤ (6772870726273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (467243 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_469_1 : expNegUpper (1141426287848078567549 / 10497333572598016000 : ℝ) ≤ (239627390999 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (292307 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_469 : rowCell 3 469 ≤ (116341241801 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6772870726273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (239627390999 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_469_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_469_1
  · norm_num [gridPoint]

theorem exp_3_470_0 : expNegUpper (257620139828970164843341 / 2369250271263295744000 : ℝ) ≤ (5990684608069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (292307 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_470_1 : expNegUpper (515822125076753650141761 / 4738500542526591488000 : ℝ) ≤ (5298451751351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2340701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_470 : rowCell 3 470 ≤ (823213965913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5990684608069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5298451751351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_470_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_470_1
  · norm_num [gridPoint]

theorem exp_3_471_0 : expNegUpper (517424866409507092127289 / 4753223815689830912000 : ℝ) ≤ (1059690320929 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2340701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_471_1 : expNegUpper (12950221477423360522129 / 118830595392245772800 : ℝ) ≤ (1171468188687 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2342949 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_471 : rowCell 3 471 ≤ (728065902579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1059690320929 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1171468188687 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_471_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_471_1
  · norm_num [gridPoint]

theorem exp_3_472_0 : expNegUpper (1443377495271376189961 / 13244360908774515200 : ℝ) ≤ (937174525161 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2342949 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_472_1 : expNegUpper (57800226842724034928479 / 529774436350980608000 : ℝ) ≤ (207191119847 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (5863 / 2500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_472 : rowCell 3 472 ≤ (160967323497 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (937174525161 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (207191119847 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_472_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_472_1
  · norm_num [gridPoint]

theorem exp_3_473_0 : expNegUpper (521813385314843985191759 / 4782738876933575168000 : ℝ) ≤ (129494446363 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (5863 / 2500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_473_1 : expNegUpper (261200841265918988642139 / 2391369438466787584000 : ℝ) ≤ (732843178011 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (469491 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_473 : rowCell 3 473 ≤ (569369158659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (129494446363 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (732843178011 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_473_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_473_1
  · norm_num [gridPoint]

theorem exp_3_474_0 : expNegUpper (419213869962633127419 / 3838024532011264000 : ℝ) ≤ (732843158093 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (469491 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_474_1 : expNegUpper (839372467089980890237 / 7676049064022528000 : ℝ) ≤ (1619945480399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2349713 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_474 : rowCell 3 474 ≤ (503453667211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (732843158093 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1619945480399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_474_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_474_1
  · norm_num [gridPoint]

theorem exp_3_475_0 : expNegUpper (58469751633930705262333 / 534705032377815552000 : ℝ) ≤ (3239890873283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2349713 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_475_1 : expNegUpper (14633899438195977734081 / 133676258094453888000 : ℝ) ≤ (1432251548007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1175987 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_475 : rowCell 3 475 ≤ (222568946329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3239890873283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1432251548007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_475_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_475_1
  · norm_num [gridPoint]

theorem exp_3_476_0 : expNegUpper (132111169265859361545641 / 1206795689023088768000 : ℝ) ≤ (2864503019113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1175987 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_476_1 : expNegUpper (105807891211125610019943 / 965436551218471014400 : ℝ) ≤ (2532432622753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (7357 / 3125 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_476 : rowCell 3 476 ≤ (78709879163 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2864503019113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2532432622753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_476_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_476_1
  · norm_num [gridPoint]

theorem exp_3_477_0 : expNegUpper (106133616903962670493503 / 968408611818025062400 : ℝ) ≤ (158277034699 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (7357 / 3125 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_477_1 : expNegUpper (265632515382647629072793 / 2421021529545062656000 : ℝ) ≤ (2238702293033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (589127 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_477 : rowCell 3 477 ≤ (347915439699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (158277034699 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2238702293033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_477_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_477_1
  · norm_num [gridPoint]

theorem exp_3_478_0 : expNegUpper (29605444281491261830273 / 269829233355202816000 : ℝ) ≤ (2238702233667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (589127 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_478_1 : expNegUpper (59277457099599496588177 / 539658466710405632000 : ℝ) ≤ (197890419213 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (117939 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_478 : rowCell 3 478 ≤ (12302065993 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2238702233667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (197890419213 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_478_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_478_1
  · norm_num [gridPoint]

theorem exp_3_479_0 : expNegUpper (21405376987874566973753 / 194873287200117248000 : ℝ) ≤ (79156165599 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (117939 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_479_1 : expNegUpper (669669644301584162841 / 6089790225003664000 : ℝ) ≤ (69965396849 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (73783 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_479 : rowCell 3 479 ≤ (271851957753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (79156165599 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (69965396849 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_479_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_479_1
  · norm_num [gridPoint]

theorem sum_3_448_2 : blockSum (rowCell 3) 448 2 ≤ (22720744169017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_448) (by simpa only [blockSum_one] using cell_3_449) (by norm_num)

theorem sum_3_450_2 : blockSum (rowCell 3) 450 2 ≤ (8914145081299 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_450) (by simpa only [blockSum_one] using cell_3_451) (by norm_num)

theorem sum_3_448_4 : blockSum (rowCell 3) 448 4 ≤ (8109806866323 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_448_2 sum_3_450_2 (by norm_num)

theorem sum_3_452_2 : blockSum (rowCell 3) 452 2 ≤ (13984935424193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_452) (by simpa only [blockSum_one] using cell_3_453) (by norm_num)

theorem sum_3_454_2 : blockSum (rowCell 3) 454 2 ≤ (10966705166103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_454) (by simpa only [blockSum_one] using cell_3_455) (by norm_num)

theorem sum_3_452_4 : blockSum (rowCell 3) 452 4 ≤ (3118955073787 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_452_2 sum_3_454_2 (by norm_num)

theorem sum_3_448_8 : blockSum (rowCell 3) 448 8 ≤ (65500674921911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_448_4 sum_3_452_4 (by norm_num)

theorem sum_3_456_2 : blockSum (rowCell 3) 456 2 ≤ (8597220910851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_456) (by simpa only [blockSum_one] using cell_3_457) (by norm_num)

theorem sum_3_458_2 : blockSum (rowCell 3) 458 2 ≤ (6737635146973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_458) (by simpa only [blockSum_one] using cell_3_459) (by norm_num)

theorem sum_3_456_4 : blockSum (rowCell 3) 456 4 ≤ (479214251807 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_456_2 sum_3_458_2 (by norm_num)

theorem sum_3_460_2 : blockSum (rowCell 3) 460 2 ≤ (2639341792959 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_460) (by simpa only [blockSum_one] using cell_3_461) (by norm_num)

theorem sum_3_462_2 : blockSum (rowCell 3) 462 2 ≤ (64600186491 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_462) (by simpa only [blockSum_one] using cell_3_463) (by norm_num)

theorem sum_3_460_4 : blockSum (rowCell 3) 460 4 ≤ (4706547760671 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_460_2 sum_3_462_2 (by norm_num)

theorem sum_3_456_8 : blockSum (rowCell 3) 456 8 ≤ (12373975789583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_456_4 sum_3_460_4 (by norm_num)

theorem sum_3_448_16 : blockSum (rowCell 3) 448 16 ≤ (90248626501077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_448_8 sum_3_456_8 (by norm_num)

theorem sum_3_464_2 : blockSum (rowCell 3) 464 2 ≤ (809306569713 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_464) (by simpa only [blockSum_one] using cell_3_465) (by norm_num)

theorem sum_3_466_2 : blockSum (rowCell 3) 466 2 ≤ (2533989267413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_466) (by simpa only [blockSum_one] using cell_3_467) (by norm_num)

theorem sum_3_464_4 : blockSum (rowCell 3) 464 4 ≤ (1154243109253 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_464_2 sum_3_466_2 (by norm_num)

theorem sum_3_468_2 : blockSum (rowCell 3) 468 2 ≤ (1982942306917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_468) (by simpa only [blockSum_one] using cell_3_469) (by norm_num)

theorem sum_3_470_2 : blockSum (rowCell 3) 470 2 ≤ (387819967123 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_470) (by simpa only [blockSum_one] using cell_3_471) (by norm_num)

theorem sum_3_468_4 : blockSum (rowCell 3) 468 4 ≤ (3534222175409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_468_2 sum_3_470_2 (by norm_num)

theorem sum_3_464_8 : blockSum (rowCell 3) 464 8 ≤ (4652718860837 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_464_4 sum_3_468_4 (by norm_num)

theorem sum_3_472_2 : blockSum (rowCell 3) 472 2 ≤ (1213238452647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_472) (by simpa only [blockSum_one] using cell_3_473) (by norm_num)

theorem sum_3_474_2 : blockSum (rowCell 3) 474 2 ≤ (948591559869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_474) (by simpa only [blockSum_one] using cell_3_475) (by norm_num)

theorem sum_3_472_4 : blockSum (rowCell 3) 472 4 ≤ (540457503129 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_472_2 sum_3_474_2 (by norm_num)

theorem sum_3_476_2 : blockSum (rowCell 3) 476 2 ≤ (370732417757 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_476) (by simpa only [blockSum_one] using cell_3_477) (by norm_num)

theorem sum_3_478_2 : blockSum (rowCell 3) 478 2 ≤ (289701803789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_478) (by simpa only [blockSum_one] using cell_3_479) (by norm_num)

theorem sum_3_476_4 : blockSum (rowCell 3) 476 4 ≤ (330217110773 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_476_2 sum_3_478_2 (by norm_num)

theorem sum_3_472_8 : blockSum (rowCell 3) 472 8 ≤ (435337306951 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_472_4 sum_3_476_4 (by norm_num)

theorem sum_3_464_16 : blockSum (rowCell 3) 464 16 ≤ (6394068088641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_464_8 sum_3_472_8 (by norm_num)

theorem sum_3_448_32 : blockSum (rowCell 3) 448 32 ≤ (103036762678359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_448_16 sum_3_464_16 (by norm_num)

#print axioms sum_3_448_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
