import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_448_0 : expNegUpper (790255756140647472809 / 7674247611616968000 : ℝ) ≤ (1900875497977601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2235561 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_448_1 : expNegUpper (50638289881833815586967 / 491151847143485952000 : ℝ) ≤ (1675716016290443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (559441 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_448 : rowCell 0 448 ≤ (52161653312873 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1900875497977601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1675716016290443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_448_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_448_1
  · norm_num [gridPoint]

theorem exp_0_449_0 : expNegUpper (29261490697063828559 / 283813597102592000 : ℝ) ≤ (1675715973641441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (559441 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_449_1 : expNegUpper (14648645105042484783 / 141906798551296000 : ℝ) ≤ (184641636194307 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (223997 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_449 : rowCell 0 449 ≤ (57477146581519 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1675715973641441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (184641636194307 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_449_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_449_1
  · norm_num [gridPoint]

theorem exp_0_450_0 : expNegUpper (229620247025701521954711 / 2224415561735190784000 : ℝ) ≤ (147713305220017 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (223997 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_450_1 : expNegUpper (459801938764601853343141 / 4448831123470381568000 : ℝ) ≤ (1302001351757909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112109 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_450 : rowCell 0 450 ≤ (20265697761519 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (147713305220017 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1302001351757909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_450_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_450_1
  · norm_num [gridPoint]

theorem exp_0_451_0 : expNegUpper (51252936806521528788021 / 495899736724279808000 : ℝ) ≤ (1302001319042747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112109 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_451_1 : expNegUpper (2565777536805086659083 / 24794986836213990400 : ℝ) ≤ (1147561518372243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (280549 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_451 : rowCell 0 451 ≤ (178624322883413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1302001319042747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1147561518372243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_451_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_451_1
  · norm_num [gridPoint]

theorem exp_0_452_0 : expNegUpper (23165930687791655675587 / 223869348793620505600 : ℝ) ≤ (286890372430391 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (280549 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_452_1 : expNegUpper (463884223105857532073211 / 4477386975872410112000 : ℝ) ≤ (1011377718390881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2246609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_452 : rowCell 0 452 ≤ (31486357345501 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (286890372430391 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1011377718390881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_452_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_452_1
  · norm_num [gridPoint]

theorem exp_0_453_0 : expNegUpper (15011840372101927545069 / 144893521275227648000 : ℝ) ≤ (1011377693301033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2246609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_453_1 : expNegUpper (7515076583867198393339 / 72446760637613824000 : ℝ) ≤ (445649870082259 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (562207 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_453 : rowCell 0 453 ≤ (27748989577013 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1011377693301033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (445649870082259 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_453_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_453_1
  · norm_num [gridPoint]

theorem exp_0_454_0 : expNegUpper (1038715010197805171061 / 10013409292216576000 : ℝ) ≤ (445649859097043 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (562207 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_454_1 : expNegUpper (2079962408439913556913 / 20026818584433152000 : ℝ) ≤ (392714832909269 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2251051 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_454 : rowCell 0 454 ≤ (122268613118757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (445649859097043 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (392714832909269 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_454_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_454_1
  · norm_num [gridPoint]

theorem exp_0_455_0 : expNegUpper (469482732909729479481737 / 4520392041768616448000 : ℝ) ≤ (785429646580683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2251051 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_455_1 : expNegUpper (58756826774479866069687 / 565049005221077056000 : ℝ) ≤ (138418477280449 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2253277 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_455 : rowCell 0 455 ≤ (107742234106317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (785429646580683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (138418477280449 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_455_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_455_1
  · norm_num [gridPoint]

theorem exp_0_456_0 : expNegUpper (58943749561206232267383 / 566846592543191104000 : ℝ) ≤ (692092369557967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2253277 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_456_1 : expNegUpper (94424795016536016374459 / 906954548069105766400 : ℝ) ≤ (609809548410641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1127753 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_456 : rowCell 0 456 ≤ (2966745547993 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (692092369557967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (609809548410641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_456_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_456_1
  · norm_num [gridPoint]

theorem exp_0_457_0 : expNegUpper (10524967896024713548411 / 101092806160626585600 : ℝ) ≤ (609809533662887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1127753 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_457_1 : expNegUpper (26344424141769036498827 / 252732015401566464000 : ℝ) ≤ (537276534107639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1128869 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_457 : rowCell 0 457 ≤ (41823273323483 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (609809533662887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (537276534107639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_457_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_457_1
  · norm_num [gridPoint]

theorem exp_0_458_0 : expNegUpper (237851709698227440414547 / 2281801326208309504000 : ℝ) ≤ (537276521196123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1128869 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_458_1 : expNegUpper (476281602595665300606333 / 4563602652416619008000 : ℝ) ≤ (59167765491103 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1129987 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_458 : rowCell 0 458 ≤ (73695219580201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (537276521196123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (59167765491103 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_458_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_458_1
  · norm_num [gridPoint]

theorem exp_0_459_0 : expNegUpper (19111583948320672732797 / 183122074636431872000 : ℝ) ≤ (473342112625489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1129987 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_459_1 : expNegUpper (4783698892064866594837 / 45780518659107968000 : ℝ) ≤ (416990529829733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2262213 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_459 : rowCell 0 459 ≤ (64923856196069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (473342112625489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (416990529829733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_459_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_459_1
  · norm_num [gridPoint]

theorem exp_0_460_0 : expNegUpper (13330058423559349135557 / 127570108825298048000 : ℝ) ≤ (208495259967387 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2262213 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_460_1 : expNegUpper (53384944930738375593339 / 510280435301192192000 : ℝ) ≤ (367325524372677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (283057 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_460 : rowCell 0 460 ≤ (28596515304923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (208495259967387 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (367325524372677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_460_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_460_1
  · norm_num [gridPoint]

theorem exp_0_461_0 : expNegUpper (481980943009152779238539 / 4607018807816417792000 : ℝ) ≤ (183662757855523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (283057 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_461_1 : expNegUpper (9651309161969602198089 / 92140376156328355840 : ℝ) ≤ (40444552767971 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2266701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_461 : rowCell 0 461 ≤ (10075946324523 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (183662757855523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40444552767971 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_461_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_461_1
  · norm_num [gridPoint]

theorem exp_0_462_0 : expNegUpper (9681722559668081922489 / 92430730724557219840 : ℝ) ≤ (8088910364053 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2266701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_462_1 : expNegUpper (484672760364329494905961 / 4621536536227860992000 : ℝ) ≤ (284985698234123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45379 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_462 : rowCell 0 462 ≤ (44375437602157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8088910364053 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (284985698234123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_462_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_462_1
  · norm_num [gridPoint]

theorem exp_0_463_0 : expNegUpper (54021963129247685140761 / 515119678105006592000 : ℝ) ≤ (284985691598129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45379 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_463_1 : expNegUpper (3380461258100917931067 / 32194979881562912000 : ℝ) ≤ (50199610684659 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2271203 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_463 : rowCell 0 463 ≤ (39084416234859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (284985691598129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (50199610684659 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_463_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_463_1
  · norm_num [gridPoint]

theorem exp_0_464_0 : expNegUpper (1220788933852416590987 / 11626601269920032000 : ℝ) ≤ (25099804761529 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2271203 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_464_1 : expNegUpper (19556258019897072725463 / 186025620318720512000 : ℝ) ≤ (1381567235873 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1136729 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_464 : rowCell 0 464 ≤ (34422222992833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25099804761529 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1381567235873 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_464_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_464_1
  · norm_num [gridPoint]

theorem exp_0_465_0 : expNegUpper (490439854108955153237367 / 4665226751296721408000 : ℝ) ≤ (110525376328303 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1136729 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_465_1 : expNegUpper (245516429174676024911903 / 2332613375648360704000 : ℝ) ≤ (194665123570409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2275717 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_465 : rowCell 0 465 ≤ (30314375189207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (110525376328303 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (194665123570409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_465_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_465_1
  · norm_num [gridPoint]

theorem exp_0_466_0 : expNegUpper (27365028881085186862423 / 259990879607288064000 : ℝ) ≤ (97332559561 / 500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2275717 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_466_1 : expNegUpper (10959236771436589419209 / 103996351842915225600 : ℝ) ≤ (171418976743039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2277979 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_466 : rowCell 0 466 ≤ (26695181174159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (97332559561 / 500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (171418976743039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_466_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_466_1
  · norm_num [gridPoint]

theorem exp_0_467_0 : expNegUpper (98941516157007982796521 / 938893550574280806400 : ℝ) ≤ (535684290157 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2277979 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_467_1 : expNegUpper (123826212396412221746859 / 1173616938217851008000 : ℝ) ≤ (150940009261233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (570061 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_467 : rowCell 0 467 ≤ (23506706594967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (535684290157 / 3125000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (150940009261233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_467_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_467_1
  · norm_num [gridPoint]

theorem exp_0_468_0 : expNegUpper (124212761719453362835851 / 1177280627779344512000 : ℝ) ≤ (75470002927407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (570061 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_468_1 : expNegUpper (497450452954697785921963 / 4709122511117378048000 : ℝ) ≤ (66449955437427 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2282513 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_468 : rowCell 0 468 ≤ (20697861740353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (75470002927407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (66449955437427 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_468_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_468_1
  · norm_num [gridPoint]

theorem exp_0_469_0 : expNegUpper (2217781902800856099267 / 20994667145196032000 : ℝ) ≤ (33224976973547 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2282513 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_469_1 : expNegUpper (1110227721809181927549 / 10497333572598016000 : ℝ) ≤ (11700918860393 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456957 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_469 : rowCell 0 469 ≤ (18223595844347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33224976973547 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11700918860393 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_469_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_469_1
  · norm_num [gridPoint]

theorem exp_0_470_0 : expNegUpper (250578617267258036843341 / 2369250271263295744000 : ℝ) ≤ (117009185995931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456957 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_470_1 : expNegUpper (501760925156289778141761 / 4738500542526591488000 : ℝ) ≤ (103012593895033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114353 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_470 : rowCell 0 470 ≤ (16044185865467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (117009185995931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (103012593895033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_470_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_470_1
  · norm_num [gridPoint]

theorem exp_0_471_0 : expNegUpper (503319976083122452127289 / 4753223815689830912000 : ℝ) ≤ (20602518322643 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114353 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_471_1 : expNegUpper (12598145349337754122129 / 118830595392245772800 : ℝ) ≤ (725480691411 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2289339 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_471 : rowCell 0 471 ≤ (2824921741581 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20602518322643 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (725480691411 / 8000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_471_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_471_1
  · norm_num [gridPoint]

theorem exp_0_472_0 : expNegUpper (1404136563245417789961 / 13244360908774515200 : ℝ) ≤ (45342542215019 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2289339 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_472_1 : expNegUpper (56233016806459074928479 / 529774436350980608000 : ℝ) ≤ (79828271835111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114581 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_472 : rowCell 0 472 ≤ (12433987134449 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45342542215019 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (79828271835111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_472_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_472_1
  · norm_num [gridPoint]

theorem exp_0_473_0 : expNegUpper (507664804582538577191759 / 4782738876933575168000 : ℝ) ≤ (3991413504431 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114581 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_473_1 : expNegUpper (254137473501246476642139 / 2391369438466787584000 : ℝ) ≤ (8783407242651 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1146953 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_473 : rowCell 0 473 ≤ (10945100755387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3991413504431 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8783407242651 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_473_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_473_1
  · norm_num [gridPoint]

theorem exp_0_474_0 : expNegUpper (407877529214420493819 / 3838024532011264000 : ℝ) ≤ (35133628206683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1146953 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_474_1 : expNegUpper (816734737918292237437 / 7676049064022528000 : ℝ) ≤ (154619701243 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1148097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_474 : rowCell 0 474 ≤ (1204244310089 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35133628206683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (154619701243 / 2500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_474_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_474_1
  · norm_num [gridPoint]

theorem exp_0_475_0 : expNegUpper (56892832618572241262333 / 534705032377815552000 : ℝ) ≤ (61847879160697 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1148097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_475_1 : expNegUpper (14240276495549705734081 / 133676258094453888000 : ℝ) ≤ (13608563799909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1149243 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_475 : rowCell 0 475 ≤ (4239698854893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (61847879160697 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13608563799909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_475_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_475_1
  · norm_num [gridPoint]

theorem exp_0_476_0 : expNegUpper (128557640180562721545641 / 1206795689023088768000 : ℝ) ≤ (54434254030563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1149243 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_476_1 : expNegUpper (102969436983480374819943 / 965436551218471014400 : ℝ) ≤ (47906617742461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2300781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_476 : rowCell 0 476 ≤ (3731394158283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (54434254030563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47906617742461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_476_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_476_1
  · norm_num [gridPoint]

theorem exp_0_477_0 : expNegUpper (103286424595133281693503 / 968408611818025062400 : ℝ) ≤ (47906616719891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2300781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_477_1 : expNegUpper (258525457212054349072793 / 2421021529545062656000 : ℝ) ≤ (42159418151447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2303079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_477 : rowCell 0 477 ≤ (3283848090761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47906616719891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42159418151447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_477_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_477_1
  · norm_num [gridPoint]

theorem exp_0_478_0 : expNegUpper (28813343906651965830273 / 269829233355202816000 : ℝ) ≤ (42159417257063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2303079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_478_1 : expNegUpper (57695683594694280588177 / 539658466710405632000 : ℝ) ≤ (7419927915931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (115269 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_478 : rowCell 0 478 ≤ (5779641633843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42159417257063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7419927915931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_478_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_478_1
  · norm_num [gridPoint]

theorem exp_0_479_0 : expNegUpper (20834190909871858493753 / 194873287200117248000 : ℝ) ≤ (37099638797423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (115269 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_479_1 : expNegUpper (651847385867700002841 / 6089790225003664000 : ℝ) ≤ (16322657613409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (461537 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_479 : rowCell 0 479 ≤ (508586470893 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (37099638797423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16322657613409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_479_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_479_1
  · norm_num [gridPoint]

theorem sum_0_448_2 : blockSum (rowCell 0) 448 2 ≤ (490716852890441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_448) (by simpa only [blockSum_one] using cell_0_449) (by norm_num)

theorem sum_0_450_2 : blockSum (rowCell 0) 450 2 ≤ (381281300498603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_450) (by simpa only [blockSum_one] using cell_0_451) (by norm_num)

theorem sum_0_448_4 : blockSum (rowCell 0) 448 4 ≤ (217999538347261 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_448_2 sum_0_450_2 (by norm_num)

theorem sum_0_452_2 : blockSum (rowCell 0) 452 2 ≤ (29617673461257 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_452) (by simpa only [blockSum_one] using cell_0_453) (by norm_num)

theorem sum_0_454_2 : blockSum (rowCell 0) 454 2 ≤ (115005423612537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_454) (by simpa only [blockSum_one] using cell_0_455) (by norm_num)

theorem sum_0_452_4 : blockSum (rowCell 0) 452 4 ≤ (131546895459411 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_452_2 sum_0_454_2 (by norm_num)

theorem sum_0_448_8 : blockSum (rowCell 0) 448 8 ≤ (21846652112917 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_448_4 sum_0_452_4 (by norm_num)

theorem sum_0_456_2 : blockSum (rowCell 0) 456 2 ≤ (89291202091371 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_456) (by simpa only [blockSum_one] using cell_0_457) (by norm_num)

theorem sum_0_458_2 : blockSum (rowCell 0) 458 2 ≤ (13861907577627 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_458) (by simpa only [blockSum_one] using cell_0_459) (by norm_num)

theorem sum_0_456_4 : blockSum (rowCell 0) 456 4 ≤ (79300369989753 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_456_2 sum_0_458_2 (by norm_num)

theorem sum_0_460_2 : blockSum (rowCell 0) 460 2 ≤ (107572762232461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_460) (by simpa only [blockSum_one] using cell_0_461) (by norm_num)

theorem sum_0_462_2 : blockSum (rowCell 0) 462 2 ≤ (10432481729627 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_462) (by simpa only [blockSum_one] using cell_0_463) (by norm_num)

theorem sum_0_460_4 : blockSum (rowCell 0) 460 4 ≤ (191032616069477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_460_2 sum_0_462_2 (by norm_num)

theorem sum_0_456_8 : blockSum (rowCell 0) 456 8 ≤ (508234096028489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_456_4 sum_0_460_4 (by norm_num)

theorem sum_0_448_16 : blockSum (rowCell 0) 448 16 ≤ (1906419831255177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_448_8 sum_0_456_8 (by norm_num)

theorem sum_0_464_2 : blockSum (rowCell 0) 464 2 ≤ (1618414954551 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_464) (by simpa only [blockSum_one] using cell_0_465) (by norm_num)

theorem sum_0_466_2 : blockSum (rowCell 0) 466 2 ≤ (25100943884563 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_466) (by simpa only [blockSum_one] using cell_0_467) (by norm_num)

theorem sum_0_464_4 : blockSum (rowCell 0) 464 4 ≤ (57469242975583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_464_2 sum_0_466_2 (by norm_num)

theorem sum_0_468_2 : blockSum (rowCell 0) 468 2 ≤ (389214575847 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_468) (by simpa only [blockSum_one] using cell_0_469) (by norm_num)

theorem sum_0_470_2 : blockSum (rowCell 0) 470 2 ≤ (7542198643343 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_470) (by simpa only [blockSum_one] using cell_0_471) (by norm_num)

theorem sum_0_468_4 : blockSum (rowCell 0) 468 4 ≤ (8636281519759 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_468_2 sum_0_470_2 (by norm_num)

theorem sum_0_464_8 : blockSum (rowCell 0) 464 8 ≤ (92014369054619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_464_4 sum_0_468_4 (by norm_num)

theorem sum_0_472_2 : blockSum (rowCell 0) 472 2 ≤ (5844771972459 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_472) (by simpa only [blockSum_one] using cell_0_473) (by norm_num)

theorem sum_0_474_2 : blockSum (rowCell 0) 474 2 ≤ (9056676095249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_474) (by simpa only [blockSum_one] using cell_0_475) (by norm_num)

theorem sum_0_472_4 : blockSum (rowCell 0) 472 4 ≤ (20746220040167 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_472_2 sum_0_474_2 (by norm_num)

theorem sum_0_476_2 : blockSum (rowCell 0) 476 2 ≤ (1753810562261 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_476) (by simpa only [blockSum_one] using cell_0_477) (by norm_num)

theorem sum_0_478_2 : blockSum (rowCell 0) 478 2 ≤ (10865506342773 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_478) (by simpa only [blockSum_one] using cell_0_479) (by norm_num)

theorem sum_0_476_4 : blockSum (rowCell 0) 476 4 ≤ (24895990840861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_476_2 sum_0_478_2 (by norm_num)

theorem sum_0_472_8 : blockSum (rowCell 0) 472 8 ≤ (13277686184239 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_472_4 sum_0_476_4 (by norm_num)

theorem sum_0_464_16 : blockSum (rowCell 0) 464 16 ≤ (250417169030433 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_464_8 sum_0_472_8 (by norm_num)

theorem sum_0_448_32 : blockSum (rowCell 0) 448 32 ≤ (215683700028561 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_448_16 sum_0_464_16 (by norm_num)

#print axioms sum_0_448_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
