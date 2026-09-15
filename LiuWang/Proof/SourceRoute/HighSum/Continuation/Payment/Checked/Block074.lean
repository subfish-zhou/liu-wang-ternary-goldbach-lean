import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_320_0 : expNegUpper (4000164551910023441363 / 43572709073712392000 : ℝ) ≤ (67496040385918033739 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (512183 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_320_1 : expNegUpper (256305580282571601500111 / 2788653380717593088000 : ℝ) ≤ (121439079440967047283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2050427 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_320 : rowCell 4 320 ≤ (18699190590088106819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (67496040385918033739 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (121439079440967047283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_320_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_320_1
  · norm_num [gridPoint]

theorem exp_4_321_0 : expNegUpper (257343938060519772628039 / 2799950908017562112000 : ℝ) ≤ (121439069526056661193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2050427 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_321_1 : expNegUpper (25764063467253154573051 / 279995090801756211200 : ℝ) ≤ (54614561288816260371 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (16417 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_321 : rowCell 4 321 ≤ (3364106361830971661 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (121439069526056661193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (54614561288816260371 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_321_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_321_1
  · norm_num [gridPoint]

theorem exp_4_322_0 : expNegUpper (25868229108462260946731 / 281127127362328627200 : ℝ) ≤ (54614556865677562381 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (16417 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_322_1 : expNegUpper (258980638679095603329061 / 2811271273623286272000 : ℝ) ≤ (19646205507779200641 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2053827 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_322 : rowCell 4 322 ≤ (15128179891397384743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (54614556865677562381 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19646205507779200641 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_322_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_322_1
  · norm_num [gridPoint]

theorem exp_4_323_0 : expNegUpper (260025600386888657494109 / 2822614477534765568000 : ℝ) ≤ (49115509823606356691 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2053827 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_323_1 : expNegUpper (65081400573650605256207 / 705653619383691392000 : ℝ) ≤ (88326213452167477069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2055533 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_323 : rowCell 4 323 ≤ (13603921047620916213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (49115509823606356691 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (88326213452167477069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_323_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_323_1
  · norm_num [gridPoint]

theorem exp_4_324_0 : expNegUpper (836396403070901003 / 9068737663206400 : ℝ) ≤ (8832620641307829177 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2055533 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_324_1 : expNegUpper (3349446854545800263 / 36274950652825600 : ℝ) ≤ (127052033844604047 / 1600000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2057243 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_324 : rowCell 4 324 ≤ (12231294112380358517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8832620641307829177 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (127052033844604047 / 1600000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_324_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_324_1
  · norm_num [gridPoint]

theorem exp_4_325_0 : expNegUpper (262727127795264974026547 / 2845369400274989568000 : ℝ) ≤ (79407514875165321097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2057243 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_325_1 : expNegUpper (131515224160899461812133 / 1422684700137494784000 : ℝ) ≤ (71378132261442737431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2058957 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_325 : rowCell 4 325 ≤ (439816994427252357 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (79407514875165321097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (71378132261442737431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_325_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_325_1
  · norm_num [gridPoint]

theorem exp_4_326_0 : expNegUpper (132042682943026267995157 / 1428390559551867136000 : ℝ) ≤ (3568906333177329649 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2058957 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_326_1 : expNegUpper (52878070143633180397213 / 571356223820746854400 : ℝ) ≤ (64150588539369078531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (82427 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_326 : rowCell 4 326 ≤ (9882875676676675887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3568906333177329649 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64150588539369078531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_326_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_326_1
  · norm_num [gridPoint]

theorem exp_4_327_0 : expNegUpper (53089720044871579211573 / 573643135247646822400 : ℝ) ≤ (64150583548373856969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (82427 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_327_1 : expNegUpper (33219406586603778420167 / 358526959529779264000 : ℝ) ≤ (1441147560778567477 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2062397 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_327 : rowCell 4 327 ≤ (8881509184156719489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (64150583548373856969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1441147560778567477 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_327_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_327_1
  · norm_num [gridPoint]

theorem exp_4_328_0 : expNegUpper (33352105100314962619783 / 359959133959811136000 : ℝ) ≤ (28822948990936494261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2062397 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_328_1 : expNegUpper (267125164238130546479143 / 2879673071678489088000 : ℝ) ≤ (2589637525077202883 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2064123 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_328 : rowCell 4 328 ≤ (1995091142799129457 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28822948990936494261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2589637525077202883 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_328_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_328_1
  · norm_num [gridPoint]

theorem exp_4_329_0 : expNegUpper (346051738855324641833 / 3730520394096128000 : ℝ) ≤ (6474093316968986877 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2064123 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_329_1 : expNegUpper (173225867965422907141 / 1865260197048064000 : ℝ) ≤ (23263371106152279429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2065853 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_329 : rowCell 4 329 ≤ (7169545453423948699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6474093316968986877 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23263371106152279429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_329_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_329_1
  · norm_num [gridPoint]

theorem exp_4_330_0 : expNegUpper (134784190323883616086931 / 1451328188738132224000 : ℝ) ≤ (23263369338970671659 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2065853 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_330_1 : expNegUpper (269880056009993752858621 / 2902656377476264448000 : ℝ) ≤ (261185982207873441 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1033793 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_330 : rowCell 4 330 ≤ (6440118222862907111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23263369338970671659 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (261185982207873441 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_330_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_330_1
  · norm_num [gridPoint]

theorem exp_4_331_0 : expNegUpper (270951699899530251947189 / 2914182287833784832000 : ℝ) ≤ (41789754003823743231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1033793 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_331_1 : expNegUpper (13563252811061696678921 / 145709114391689241600 : ℝ) ≤ (37529344456552221963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (517331 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_331 : rowCell 4 331 ≤ (723002490372892297 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (41789754003823743231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37529344456552221963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_331_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_331_1
  · norm_num [gridPoint]

theorem exp_4_332_0 : expNegUpper (592043620348922398847 / 6360284861950131200 : ℝ) ≤ (37529341650503890681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (517331 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_332_1 : expNegUpper (11854569824889769345957 / 127205697239002624000 : ℝ) ≤ (8424544670700521967 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1035533 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_332 : rowCell 4 332 ≤ (5193974776179971411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (37529341650503890681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8424544670700521967 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_332_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_332_1
  · norm_num [gridPoint]

theorem exp_4_333_0 : expNegUpper (273733487023028033470219 / 2937302623466091008000 : ℝ) ≤ (33698176183040337071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1035533 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_333_1 : expNegUpper (137025107628012341861729 / 1468651311733045504000 : ℝ) ≤ (945423968122331529 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2072811 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_333 : rowCell 4 333 ≤ (466341856808692263 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33698176183040337071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (945423968122331529 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_333_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_333_1
  · norm_num [gridPoint]

theorem exp_4_334_0 : expNegUpper (5502639497588801773561 / 58977940974817536000 : ℝ) ≤ (30253564753307637929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2072811 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_334_1 : expNegUpper (11018015762570101864273 / 117955881949635072000 : ℝ) ≤ (13578501391201131863 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (6483 / 3125 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_334 : rowCell 4 334 ≤ (2093215082255368197 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30253564753307637929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13578501391201131863 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_334_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_334_1
  · norm_num [gridPoint]

theorem exp_4_335_0 : expNegUpper (276535538922079115822177 / 2960514312321417728000 : ℝ) ≤ (27157000799367430217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (6483 / 3125 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_335_1 : expNegUpper (17303478274342933146011 / 185032144520088608000 : ℝ) ≤ (24373761745505973173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1038157 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_335 : rowCell 4 335 ≤ (751533900388328497 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27157000799367430217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24373761745505973173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_335_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_335_1
  · norm_num [gridPoint]

theorem exp_4_336_0 : expNegUpper (17371511821455235101979 / 185759650887982112000 : ℝ) ≤ (24373759979633609221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1038157 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_336_1 : expNegUpper (11130640008962659265623 / 118886176568308551680 : ℝ) ≤ (5468133999362398131 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2078071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_336 : rowCell 4 336 ≤ (1686160726027724491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24373759979633609221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5468133999362398131 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_336_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_336_1
  · norm_num [gridPoint]

theorem exp_4_337_0 : expNegUpper (11174317421415706913423 / 119352694175990599680 : ℝ) ≤ (21872534425166233837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2078071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_337_1 : expNegUpper (139840723780164923624543 / 1491908677199882496000 : ℝ) ≤ (9812551574008700577 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (259979 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_337 : rowCell 4 337 ≤ (3026045014870307821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21872534425166233837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9812551574008700577 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_337_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_337_1
  · norm_num [gridPoint]

theorem exp_4_338_0 : expNegUpper (140388394045372248081487 / 1497751566448785664000 : ℝ) ≤ (19625101748284352499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (259979 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_338_1 : expNegUpper (281102004390615673890773 / 2995503132897571328000 : ℝ) ≤ (8803013407606662871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2081597 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_338 : rowCell 4 338 ≤ (542985468938463893 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19625101748284352499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8803013407606662871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_338_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_338_1
  · norm_num [gridPoint]

theorem exp_4_339_0 : expNegUpper (11288030272067115133717 / 120288469988045312000 : ℝ) ≤ (17606025569256901297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2081597 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_339_1 : expNegUpper (2825276807072626082947 / 30072117497011328000 : ℝ) ≤ (7896192863356500711 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (416673 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_339 : rowCell 4 339 ≤ (243544215808727403 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17606025569256901297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7896192863356500711 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_339_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_339_1
  · norm_num [gridPoint]

theorem exp_4_340_0 : expNegUpper (70907462915132866526123 / 754735801202612352000 : ℝ) ≤ (7896192308891576449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (416673 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_340_1 : expNegUpper (283958486502609297189931 / 3018943204810449408000 : ℝ) ≤ (442610272550206723 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1042569 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_340 : rowCell 4 340 ≤ (273051514278024093 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7896192308891576449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (442610272550206723 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_340_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_340_1
  · norm_num [gridPoint]

theorem exp_4_341_0 : expNegUpper (285064082659643906176739 / 3030697498225521152000 : ℝ) ≤ (14163527734760996967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1042569 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_341_1 : expNegUpper (28539443176899438730553 / 303069749822552115200 : ℝ) ≤ (6350426611400531073 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1043457 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_341 : rowCell 4 341 ≤ (1958974795392691911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14163527734760996967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6350426611400531073 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_341_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_341_1
  · norm_num [gridPoint]

theorem exp_4_342_0 : expNegUpper (28650345979135384528873 / 304247462994634803200 : ℝ) ≤ (12700852344711885601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1043457 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_342_1 : expNegUpper (286835526498756525370561 / 3042474629946348032000 : ℝ) ≤ (5693802486733762461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1044347 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_342 : rowCell 4 342 ≤ (878275974807507209 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12700852344711885601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5693802486733762461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_342_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_342_1
  · norm_num [gridPoint]

theorem exp_4_343_0 : expNegUpper (287947993047999930169529 / 3054274599972930048000 : ℝ) ≤ (11387604192248824989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1044347 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_343_1 : expNegUpper (36035222585529294764261 / 381784324996616256000 : ℝ) ≤ (10208697033977011357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2090479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_343 : rowCell 4 343 ≤ (393705422085817731 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11387604192248824989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10208697033977011357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_343_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_343_1
  · norm_num [gridPoint]

theorem exp_4_344_0 : expNegUpper (1446988462109604037741 / 15330487041526336000 : ℝ) ≤ (10208696339030194717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2090479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_344_1 : expNegUpper (11589328172710661290607 / 122643896332210688000 : ℝ) ≤ (9150546220595704953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1046133 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_344 : rowCell 4 344 ≤ (176461670064675971 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10208696339030194717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9150546220595704953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_344_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_344_1
  · norm_num [gridPoint]

theorem exp_4_345_0 : expNegUpper (290852567905455124153807 / 3077943054943359488000 : ℝ) ≤ (4575272801235733519 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1046133 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_345_1 : expNegUpper (145594903695845847276443 / 1538971527471679744000 : ℝ) ≤ (4100462667701481363 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1047029 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_345 : rowCell 4 345 ≤ (253056970000394833 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4575272801235733519 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4100462667701481363 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_345_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_345_1
  · norm_num [gridPoint]

theorem exp_4_346_0 : expNegUpper (146156314745470763357707 / 1544905769943603456000 : ℝ) ≤ (820092478567785927 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1047029 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_346_1 : expNegUpper (58530319979669698341257 / 617962307977441382400 : ℝ) ≤ (7348829689902590009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1047927 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_346 : rowCell 4 346 ≤ (141737758355232877 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (820092478567785927 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7348829689902590009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_346_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_346_1
  · norm_num [gridPoint]

theorem exp_4_347_0 : expNegUpper (58755577434143732392417 / 620340572627361894400 : ℝ) ≤ (918603650133590719 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1047927 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_347_1 : expNegUpper (73529647957518892613609 / 775425715784202368000 : ℝ) ≤ (3292178281977438947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2097653 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_347 : rowCell 4 347 ≤ (508010212041053471 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (918603650133590719 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3292178281977438947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_347_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_347_1
  · norm_num [gridPoint]

theorem exp_4_348_0 : expNegUpper (73812087734281294155721 / 778404256173041792000 : ℝ) ≤ (3292178064660667191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2097653 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_348_1 : expNegUpper (295590793179211577526403 / 3113617024692167168000 : ℝ) ≤ (1179719273636421149 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (32804 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_348 : rowCell 4 348 ≤ (91026811127058533 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3292178064660667191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1179719273636421149 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_348_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_348_1
  · norm_num [gridPoint]

theorem exp_4_349_0 : expNegUpper (474758449251999547883 / 5000886439285248000 : ℝ) ≤ (2949297990893436529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (32804 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_349_1 : expNegUpper (237654571150476127721 / 2500443219642624000 : ℝ) ≤ (528353439300930297 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2101263 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_349 : rowCell 4 349 ≤ (407705496687697881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2949297990893436529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (528353439300930297 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_349_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_349_1
  · norm_num [gridPoint]

theorem exp_4_350_0 : expNegUpper (149102468349590465551561 / 1568756931360073984000 : ℝ) ≤ (1320883512385152157 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2101263 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_350_1 : expNegUpper (298550864099064963558041 / 3137513862720147968000 : ℝ) ≤ (4731962132015236019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1051537 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_350 : rowCell 4 350 ≤ (730338979856402809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1320883512385152157 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4731962132015236019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_350_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_350_1
  · norm_num [gridPoint]

theorem exp_4_351_0 : expNegUpper (299691078679507464380689 / 3149496539192771072000 : ℝ) ≤ (946392365348255889 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1051537 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_351_1 : expNegUpper (1875242210340372724849 / 19684353369954819200 : ℝ) ≤ (847479452443709679 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (263111 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_351 : rowCell 4 351 ≤ (327026861587753567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (946392365348255889 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (847479452443709679 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_351_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_351_1
  · norm_num [gridPoint]

theorem sum_4_320_2 : blockSum (rowCell 4) 320 2 ≤ (8879930599810741281 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_320) (by simpa only [blockSum_one] using cell_4_321) (by norm_num)

theorem sum_4_322_2 : blockSum (rowCell 4) 322 2 ≤ (7183025234754575239 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_322) (by simpa only [blockSum_one] using cell_4_323) (by norm_num)

theorem sum_4_320_4 : blockSum (rowCell 4) 320 4 ≤ (401573895864132913 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_320_2 sum_4_322_2 (by norm_num)

theorem sum_4_324_2 : blockSum (rowCell 4) 324 2 ≤ (11613359486530833721 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_324) (by simpa only [blockSum_one] using cell_4_325) (by norm_num)

theorem sum_4_326_2 : blockSum (rowCell 4) 326 2 ≤ (1172774053802087211 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_326) (by simpa only [blockSum_one] using cell_4_327) (by norm_num)

theorem sum_4_324_4 : blockSum (rowCell 4) 324 4 ≤ (20995551916947531409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_324_2 sum_4_326_2 (by norm_num)

theorem sum_4_320_8 : blockSum (rowCell 4) 320 8 ≤ (53121463586078164449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_320_4 sum_4_324_4 (by norm_num)

theorem sum_4_328_2 : blockSum (rowCell 4) 328 2 ≤ (15149910024620466527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_328) (by simpa only [blockSum_one] using cell_4_329) (by norm_num)

theorem sum_4_330_2 : blockSum (rowCell 4) 330 2 ≤ (12224138145846045487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_330) (by simpa only [blockSum_one] using cell_4_331) (by norm_num)

theorem sum_4_328_4 : blockSum (rowCell 4) 328 4 ≤ (13687024085233256007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_328_2 sum_4_330_2 (by norm_num)

theorem sum_4_332_2 : blockSum (rowCell 4) 332 2 ≤ (9857393344266894041 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_332) (by simpa only [blockSum_one] using cell_4_333) (by norm_num)

theorem sum_4_334_2 : blockSum (rowCell 4) 334 2 ≤ (7944099666452378879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_334) (by simpa only [blockSum_one] using cell_4_335) (by norm_num)

theorem sum_4_332_4 : blockSum (rowCell 4) 332 4 ≤ (445037325267981823 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_332_2 sum_4_334_2 (by norm_num)

theorem sum_4_328_8 : blockSum (rowCell 4) 328 8 ≤ (22587770590592892467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_328_4 sum_4_332_4 (by norm_num)

theorem sum_4_320_16 : blockSum (rowCell 4) 320 16 ≤ (18927308544167764229 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_320_8 sum_4_328_8 (by norm_num)

theorem sum_4_336_2 : blockSum (rowCell 4) 336 2 ≤ (6398366466925756803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_336) (by simpa only [blockSum_one] using cell_4_337) (by norm_num)

theorem sum_4_338_2 : blockSum (rowCell 4) 338 2 ≤ (1030073900555918699 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_338) (by simpa only [blockSum_one] using cell_4_339) (by norm_num)

theorem sum_4_336_4 : blockSum (rowCell 4) 336 4 ≤ (5774367984852675149 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_336_2 sum_4_338_2 (by norm_num)

theorem sum_4_340_2 : blockSum (rowCell 4) 340 2 ≤ (828677381923376931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_340) (by simpa only [blockSum_one] using cell_4_341) (by norm_num)

theorem sum_4_342_2 : blockSum (rowCell 4) 342 2 ≤ (1665686818979142671 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_342) (by simpa only [blockSum_one] using cell_4_343) (by norm_num)

theorem sum_4_340_4 : blockSum (rowCell 4) 340 4 ≤ (7474760547575169997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_340_2 sum_4_342_2 (by norm_num)

theorem sum_4_336_8 : blockSum (rowCell 4) 336 8 ≤ (3804699303456104059 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_336_4 sum_4_340_4 (by norm_num)

theorem sum_4_344_2 : blockSum (rowCell 4) 344 2 ≤ (2676978210519381933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_344) (by simpa only [blockSum_one] using cell_4_345) (by norm_num)

theorem sum_4_346_2 : blockSum (rowCell 4) 346 2 ≤ (1074961245461984979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_346) (by simpa only [blockSum_one] using cell_4_347) (by norm_num)

theorem sum_4_344_4 : blockSum (rowCell 4) 344 4 ≤ (4826900701443351891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_344_2 sum_4_346_2 (by norm_num)

theorem sum_4_348_2 : blockSum (rowCell 4) 348 2 ≤ (431419776161495273 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_348) (by simpa only [blockSum_one] using cell_4_349) (by norm_num)

theorem sum_4_350_2 : blockSum (rowCell 4) 350 2 ≤ (1384392703031909943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_350) (by simpa only [blockSum_one] using cell_4_351) (by norm_num)

theorem sum_4_348_4 : blockSum (rowCell 4) 348 4 ≤ (622014361535578207 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_348_2 sum_4_350_2 (by norm_num)

theorem sum_4_344_8 : blockSum (rowCell 4) 344 8 ≤ (3968486254560621463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_344_4 sum_4_348_4 (by norm_num)

theorem sum_4_336_16 : blockSum (rowCell 4) 336 16 ≤ (26960469026401763221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_336_8 sum_4_344_8 (by norm_num)

theorem sum_4_320_32 : blockSum (rowCell 4) 320 32 ≤ (178378937379743877053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_320_16 sum_4_336_16 (by norm_num)

#print axioms sum_4_320_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
