import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_320_0 : expNegUpper (4028305866179207441363 / 43572709073712392000 : ℝ) ≤ (35382653524485053753 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (257387 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_320_1 : expNegUpper (258102983528639313500111 / 2788653380717593088000 : ℝ) ≤ (63743746501241957209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1030389 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_320 : rowCell 6 320 ≤ (4904260516429631389 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35382653524485053753 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (63743746501241957209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_320_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_320_1
  · norm_num [gridPoint]

theorem exp_6_321_0 : expNegUpper (259148623040907612628039 / 2799950908017562112000 : ℝ) ≤ (63743741127167373023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1030389 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_321_1 : expNegUpper (25944167878575932173051 / 279995090801756211200 : ℝ) ≤ (57409305087989120939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2062463 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_321 : rowCell 6 321 ≤ (883458897844917047 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (63743741127167373023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (57409305087989120939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_321_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_321_1
  · norm_num [gridPoint]

theorem exp_6_322_0 : expNegUpper (26049061693217051346731 / 281127127362328627200 : ℝ) ≤ (57409300286895487583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2062463 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_322_1 : expNegUpper (260785323659483443329061 / 2811271273623286272000 : ℝ) ≤ (51695767084458196469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2064153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_322 : rowCell 6 322 ≤ (1989009884200769273 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (57409300286895487583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51695767084458196469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_322_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_322_1
  · norm_num [gridPoint]

theorem exp_6_323_0 : expNegUpper (261837567101596625494109 / 2822614477534765568000 : ℝ) ≤ (1292394069897397743 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2064153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_323_1 : expNegUpper (65533482035537581256207 / 705653619383691392000 : ℝ) ≤ (23271592614282163261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2065847 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_323 : rowCell 6 323 ≤ (7163672351498506153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1292394069897397743 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23271592614282163261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_323_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_323_1
  · norm_num [gridPoint]

theorem exp_6_324_0 : expNegUpper (4211031736664393527 / 45343688316032000 : ℝ) ≤ (11635795349597074563 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2065847 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_324_1 : expNegUpper (16863200142470311267 / 181374753264128000 : ℝ) ≤ (1309290734124017519 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (413509 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_324 : rowCell 6 324 ≤ (6449159616452965829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11635795349597074563 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1309290734124017519 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_324_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_324_1
  · norm_num [gridPoint]

theorem exp_6_325_0 : expNegUpper (264546376244293070026547 / 2845369400274989568000 : ℝ) ≤ (20948650035844467223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (413509 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_325_1 : expNegUpper (132423027951833477812133 / 1422684700137494784000 : ℝ) ≤ (37709026885262294553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2069247 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_325 : rowCell 6 325 ≤ (1160992976602051801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20948650035844467223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37709026885262294553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_325_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_325_1
  · norm_num [gridPoint]

theorem exp_6_326_0 : expNegUpper (132954127601120347995157 / 1428390559551867136000 : ℝ) ≤ (37709023831461105707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2069247 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_326_1 : expNegUpper (53241919833438799597213 / 571356223820746854400 : ℝ) ≤ (6786787921296276543 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2070953 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_326 : rowCell 6 326 ≤ (5224269260619730033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (37709023831461105707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6786787921296276543 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_326_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_326_1
  · norm_num [gridPoint]

theorem exp_6_327_0 : expNegUpper (53455026081541224011573 / 573643135247646822400 : ℝ) ≤ (8483484220072141803 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2070953 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_327_1 : expNegUpper (33447267751127298420167 / 358526959529779264000 : ℝ) ≤ (30531867232832079677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2072663 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_327 : rowCell 6 327 ≤ (4700904354424640453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8483484220072141803 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (30531867232832079677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_327_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_327_1
  · norm_num [gridPoint]

theorem exp_6_328_0 : expNegUpper (33580876481628498619783 / 359959133959811136000 : ℝ) ≤ (30531864799454886433 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2072663 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_328_1 : expNegUpper (268951694421478770479143 / 2879673071678489088000 : ℝ) ≤ (27466479027033318703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2074377 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_328 : rowCell 6 328 ≤ (422929133971455153 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30531864799454886433 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27466479027033318703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_328_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_328_1
  · norm_num [gridPoint]

theorem exp_6_329_0 : expNegUpper (348417947781348321833 / 3730520394096128000 : ℝ) ≤ (1716654803458360219 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2074377 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_329_1 : expNegUpper (174406623481879867141 / 1865260197048064000 : ℝ) ≤ (24704926770208605883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (415219 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_329 : rowCell 6 329 ≤ (3804385625119994399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1716654803458360219 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24704926770208605883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_329_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_329_1
  · norm_num [gridPoint]

theorem exp_6_330_0 : expNegUpper (135702916716297824086931 / 1451328188738132224000 : ℝ) ≤ (24704924832324135499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (415219 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_330_1 : expNegUpper (271713867927662104858621 / 2902656377476264448000 : ℝ) ≤ (22217516845271241593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2077817 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_330 : rowCell 6 330 ≤ (3421626604011449613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24704924832324135499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22217516845271241593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_330_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_330_1
  · norm_num [gridPoint]

theorem exp_6_331_0 : expNegUpper (272792793551518731947189 / 2914182287833784832000 : ℝ) ≤ (22217515116274254127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2077817 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_331_1 : expNegUpper (13655125450303117478921 / 145709114391689241600 : ℝ) ≤ (9988706290263585419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2079543 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_331 : rowCell 6 331 ≤ (384611504644514063 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22217515116274254127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9988706290263585419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_331_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_331_1
  · norm_num [gridPoint]

theorem exp_6_332_0 : expNegUpper (13709239993982642373481 / 146286551824853017600 : ℝ) ≤ (4994352759529867479 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2079543 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_332_1 : expNegUpper (274496199624453174957011 / 2925731036497060352000 : ℝ) ≤ (17960364124885272827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2081273 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_332 : rowCell 6 332 ≤ (2766456649606178853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4994352759529867479 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17960364124885272827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_332_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_332_1
  · norm_num [gridPoint]

theorem exp_6_333_0 : expNegUpper (275581862409336641470219 / 2937302623466091008000 : ℝ) ≤ (3592072549824784557 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2081273 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_333_1 : expNegUpper (137947474887586613861729 / 1468651311733045504000 : ℝ) ≤ (4036115841392140779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1041503 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_333 : rowCell 6 333 ≤ (2486954561338088491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3592072549824784557 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4036115841392140779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_333_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_333_1
  · norm_num [gridPoint]

theorem exp_6_334_0 : expNegUpper (291562095929377642819 / 3104102156569344000 : ℝ) ≤ (807223106930998193 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1041503 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_334_1 : expNegUpper (583786883053812957067 / 6208204313138688000 : ℝ) ≤ (3627480404591189357 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (260593 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_334 : rowCell 6 334 ≤ (2235345204607232543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (807223106930998193 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3627480404591189357 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_334_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_334_1
  · norm_num [gridPoint]

theorem exp_6_335_0 : expNegUpper (278391196042707851822177 / 2960514312321417728000 : ℝ) ≤ (453435016383877341 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (260593 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_335_1 : expNegUpper (17419229290184725146011 / 185032144520088608000 : ℝ) ≤ (3259717005226185493 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1043243 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_335 : rowCell 6 335 ≤ (251110301447484637 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (453435016383877341 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3259717005226185493 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_335_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_335_1
  · norm_num [gridPoint]

theorem exp_6_336_0 : expNegUpper (17487717945692035101979 / 185759650887982112000 : ℝ) ≤ (6519433522719058153 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1043243 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_336_1 : expNegUpper (11204866293787808705623 / 118886176568308551680 : ℝ) ≤ (2343033348549441069 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (261029 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_336 : rowCell 6 336 ≤ (451271595946676307 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6519433522719058153 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2343033348549441069 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_336_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_336_1
  · norm_num [gridPoint]

theorem exp_6_337_0 : expNegUpper (11248834975613661473423 / 119352694175990599680 : ℝ) ≤ (1464395734144302083 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (261029 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_337_1 : expNegUpper (140770372774059323624543 / 1491908677199882496000 : ℝ) ≤ (526212564679579171 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2089981 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_337 : rowCell 6 337 ≤ (64868731221019163 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1464395734144302083 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (526212564679579171 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_337_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_337_1
  · norm_num [gridPoint]

theorem exp_6_338_0 : expNegUpper (141321683906426712081487 / 1497751566448785664000 : ℝ) ≤ (10524250518487088273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2089981 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_338_1 : expNegUpper (282964943245564537890773 / 2995503132897571328000 : ℝ) ≤ (4726487182021485417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (418347 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_338 : rowCell 6 338 ≤ (1456757186722072309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10524250518487088273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4726487182021485417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_338_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_338_1
  · norm_num [gridPoint]

theorem exp_6_339_0 : expNegUpper (11362839095637874813717 / 120288469988045312000 : ℝ) ≤ (9452973673253431611 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (418347 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_339_1 : expNegUpper (2843942604293715362947 / 30072117497011328000 : ℝ) ≤ (4244735886606110549 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (523373 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_339 : rowCell 6 339 ≤ (261675848424421241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9452973673253431611 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4244735886606110549 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_339_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_339_1
  · norm_num [gridPoint]

theorem exp_6_340_0 : expNegUpper (71375928279240130526123 / 754735801202612352000 : ℝ) ≤ (339578846305953601 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (523373 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_340_1 : expNegUpper (285828707091878289189931 / 3018943204810449408000 : ℝ) ≤ (3811519612578616369 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1047627 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_340 : rowCell 6 340 ≤ (1174938733197765879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (339578846305953601 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3811519612578616369 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_340_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_340_1
  · norm_num [gridPoint]

theorem exp_6_341_0 : expNegUpper (286941584983233026176739 / 3030697498225521152000 : ℝ) ≤ (3811519338350686141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1047627 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_341_1 : expNegUpper (28726829322542344330553 / 303069749822552115200 : ℝ) ≤ (273760827710973851 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2097019 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_341 : rowCell 6 341 ≤ (1054950966970821661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3811519338350686141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (273760827710973851 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_341_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_341_1
  · norm_num [gridPoint]

theorem exp_6_342_0 : expNegUpper (28838460298210302928873 / 304247462994634803200 : ℝ) ≤ (3422010102087535603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2097019 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_342_1 : expNegUpper (288713028822345645370561 / 3042474629946348032000 : ℝ) ≤ (383981709635452549 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (524697 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_342 : rowCell 6 342 ≤ (947076762215799589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3422010102087535603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (383981709635452549 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_342_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_342_1
  · norm_num [gridPoint]

theorem exp_6_343_0 : expNegUpper (289832777105909178169529 / 3054274599972930048000 : ℝ) ≤ (6143706918949555309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (524697 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_343_1 : expNegUpper (36270365484372942764261 / 381784324996616256000 : ℝ) ≤ (344640381475919943 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1050281 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_343 : rowCell 6 343 ≤ (2125271020868889 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6143706918949555309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (344640381475919943 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_343_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_343_1
  · norm_num [gridPoint]

theorem exp_6_344_0 : expNegUpper (1456430586734950597741 / 15330487041526336000 : ℝ) ≤ (5514245715997396869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1050281 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_344_1 : expNegUpper (11664719535027031210607 / 122643896332210688000 : ℝ) ≤ (2474278373909334059 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2102339 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_344 : rowCell 6 344 ≤ (190739238958889011 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5514245715997396869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2474278373909334059 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_344_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_344_1
  · norm_num [gridPoint]

theorem exp_6_345_0 : expNegUpper (292744633697684500153807 / 3077943054943359488000 : ℝ) ≤ (4948556402640684983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2102339 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_345_1 : expNegUpper (146539116158380503276443 / 1538971527471679744000 : ℝ) ≤ (2220128539432668609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (52603 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_345 : rowCell 6 345 ≤ (68464071433353143 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4948556402640684983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2220128539432668609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_345_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_345_1
  · norm_num [gridPoint]

theorem exp_6_346_0 : expNegUpper (147104168075165483357707 / 1544905769943603456000 : ℝ) ≤ (2220128385760008567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (52603 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_346_1 : expNegUpper (58908733138115573541257 / 617962307977441382400 : ℝ) ≤ (3983595088943615161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (131619 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_346 : rowCell 6 346 ≤ (614274845969413953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2220128385760008567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3983595088943615161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_346_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_346_1
  · norm_num [gridPoint]

theorem exp_6_347_0 : expNegUpper (59135446939453633192417 / 620340572627361894400 : ℝ) ≤ (1991797407659845383 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (131619 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_347_1 : expNegUpper (74003574622366252613609 / 775425715784202368000 : ℝ) ≤ (178669382947259801 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2107693 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_347 : rowCell 6 347 ≤ (551061951499837267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1991797407659845383 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (178669382947259801 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_347_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_347_1
  · norm_num [gridPoint]

theorem exp_6_348_0 : expNegUpper (74287834832708686155721 / 778404256173041792000 : ℝ) ≤ (1786693707687033273 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2107693 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_348_1 : expNegUpper (297490140705761081526403 / 3113617024692167168000 : ℝ) ≤ (640993022836986591 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421897 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_348 : rowCell 6 348 ≤ (24714177819077151 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1786693707687033273 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (640993022836986591 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_348_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_348_1
  · norm_num [gridPoint]

theorem exp_6_349_0 : expNegUpper (477809056069390959083 / 5000886439285248000 : ℝ) ≤ (320496489739347579 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421897 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_349_1 : expNegUpper (239176961865443782121 / 2500443219642624000 : ℝ) ≤ (179632568508769677 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1055641 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_349 : rowCell 6 349 ≤ (55411551540913291 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (320496489739347579 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (179632568508769677 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_349_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_349_1
  · norm_num [gridPoint]

theorem exp_6_350_0 : expNegUpper (150057603413605313551561 / 1568756931360073984000 : ℝ) ≤ (1437060451604336463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1055641 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_350_1 : expNegUpper (300457493359934595558041 / 3137513862720147968000 : ℝ) ≤ (51541344995781213 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1056541 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_350 : rowCell 6 350 ≤ (198752768834225471 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1437060451604336463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51541344995781213 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_350_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_350_1
  · norm_num [gridPoint]

theorem exp_6_351_0 : expNegUpper (301604989674697224380689 / 3149496539192771072000 : ℝ) ≤ (1288533539056443653 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1056541 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_351_1 : expNegUpper (1887181398640558324849 / 19684353369954819200 : ℝ) ≤ (577598068064018917 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1057443 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_351 : rowCell 6 351 ≤ (178198963452832439 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1288533539056443653 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (577598068064018917 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_351_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_351_1
  · norm_num [gridPoint]

theorem sum_6_320_2 : blockSum (rowCell 6) 320 2 ≤ (582597187853388539 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_320) (by simpa only [blockSum_one] using cell_6_321) (by norm_num)

theorem sum_6_322_2 : blockSum (rowCell 6) 322 2 ≤ (3023942377660316649 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_322) (by simpa only [blockSum_one] using cell_6_323) (by norm_num)

theorem sum_6_320_4 : blockSum (rowCell 6) 320 4 ≤ (33762821899610016493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_320_2 sum_6_322_2 (by norm_num)

theorem sum_6_324_2 : blockSum (rowCell 6) 324 2 ≤ (6127062249731612417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_324) (by simpa only [blockSum_one] using cell_6_325) (by norm_num)

theorem sum_6_326_2 : blockSum (rowCell 6) 326 2 ≤ (4962586807522185243 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_326) (by simpa only [blockSum_one] using cell_6_327) (by norm_num)

theorem sum_6_324_4 : blockSum (rowCell 6) 324 4 ≤ (554482452862689883 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_324_2 sum_6_326_2 (by norm_num)

theorem sum_6_320_8 : blockSum (rowCell 6) 320 8 ≤ (55942120014117611813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_320_4 sum_6_324_4 (by norm_num)

theorem sum_6_328_2 : blockSum (rowCell 6) 328 2 ≤ (8033676964834545929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_328) (by simpa only [blockSum_one] using cell_6_329) (by norm_num)

theorem sum_6_330_2 : blockSum (rowCell 6) 330 2 ≤ (6498518641167562117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_330) (by simpa only [blockSum_one] using cell_6_331) (by norm_num)

theorem sum_6_328_4 : blockSum (rowCell 6) 328 4 ≤ (7266097803001054023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_328_2 sum_6_330_2 (by norm_num)

theorem sum_6_332_2 : blockSum (rowCell 6) 332 2 ≤ (328338200684016709 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_332) (by simpa only [blockSum_one] using cell_6_333) (by norm_num)

theorem sum_6_334_2 : blockSum (rowCell 6) 334 2 ≤ (4244227616187109639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_334) (by simpa only [blockSum_one] using cell_6_335) (by norm_num)

theorem sum_6_332_4 : blockSum (rowCell 6) 332 4 ≤ (9497638827131376983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_332_2 sum_6_334_2 (by norm_num)

theorem sum_6_328_8 : blockSum (rowCell 6) 328 8 ≤ (24029834433133485029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_328_4 sum_6_332_4 (by norm_num)

theorem sum_6_320_16 : blockSum (rowCell 6) 320 16 ≤ (39985977223625548421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_320_8 sum_6_328_8 (by norm_num)

theorem sum_6_336_2 : blockSum (rowCell 6) 336 2 ≤ (3426804664312184303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_336) (by simpa only [blockSum_one] using cell_6_337) (by norm_num)

theorem sum_6_338_2 : blockSum (rowCell 6) 338 2 ≤ (1382568214422089257 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_338) (by simpa only [blockSum_one] using cell_6_339) (by norm_num)

theorem sum_6_336_4 : blockSum (rowCell 6) 336 4 ≤ (6191941093156362817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_336_2 sum_6_338_2 (by norm_num)

theorem sum_6_340_2 : blockSum (rowCell 6) 340 2 ≤ (111494485008429377 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_340) (by simpa only [blockSum_one] using cell_6_341) (by norm_num)

theorem sum_6_342_2 : blockSum (rowCell 6) 342 2 ≤ (1797185170563355189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_342) (by simpa only [blockSum_one] using cell_6_343) (by norm_num)

theorem sum_6_340_4 : blockSum (rowCell 6) 340 4 ≤ (4027074870731942729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_340_2 sum_6_342_2 (by norm_num)

theorem sum_6_336_8 : blockSum (rowCell 6) 336 8 ≤ (5109507981944152773 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_336_4 sum_6_340_4 (by norm_num)

theorem sum_6_344_2 : blockSum (rowCell 6) 344 2 ≤ (723798835084543737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_344) (by simpa only [blockSum_one] using cell_6_345) (by norm_num)

theorem sum_6_346_2 : blockSum (rowCell 6) 346 2 ≤ (58266839873462561 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_346) (by simpa only [blockSum_one] using cell_6_347) (by norm_num)

theorem sum_6_344_4 : blockSum (rowCell 6) 344 4 ≤ (1306467233819169347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_344_2 sum_6_346_2 (by norm_num)

theorem sum_6_348_2 : blockSum (rowCell 6) 348 2 ≤ (234393992177212337 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_348) (by simpa only [blockSum_one] using cell_6_349) (by norm_num)

theorem sum_6_350_2 : blockSum (rowCell 6) 350 2 ≤ (37695173228705791 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_350) (by simpa only [blockSum_one] using cell_6_351) (by norm_num)

theorem sum_6_348_4 : blockSum (rowCell 6) 348 4 ≤ (105717464580185323 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_348_2 sum_6_350_2 (by norm_num)

theorem sum_6_344_8 : blockSum (rowCell 6) 344 8 ≤ (2152206950460651931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_344_4 sum_6_348_4 (by norm_num)

theorem sum_6_336_16 : blockSum (rowCell 6) 336 16 ≤ (226928591637650147 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_336_8 sum_6_344_8 (by norm_num)

theorem sum_6_320_32 : blockSum (rowCell 6) 320 32 ≤ (15119261489929713 / 160000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_320_16 sum_6_336_16 (by norm_num)

#print axioms sum_6_320_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
