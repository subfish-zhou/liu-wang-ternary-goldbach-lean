import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_320_0 : expNegUpper (3812555790115463441363 / 43572709073712392000 : ℝ) ≤ (5002621025605982478301 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (495241 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_320_1 : expNegUpper (244322891975453521500111 / 2788653380717593088000 : ℝ) ≤ (2230682101947276469607 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1982737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_320 : rowCell 0 320 ≤ (276048922293763468813 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5002621025605982478301 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2230682101947276469607 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_320_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_320_1
  · norm_num [gridPoint]

theorem exp_0_321_0 : expNegUpper (245312704857934172628039 / 2799950908017562112000 : ℝ) ≤ (4461363918830353852333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1982737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_321_1 : expNegUpper (24563367391767970573051 / 279995090801756211200 : ℝ) ≤ (7956330446089524262691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1984513 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_321 : rowCell 0 321 ≤ (1230836094829993721909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4461363918830353852333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7956330446089524262691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_321_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_321_1
  · norm_num [gridPoint]

theorem exp_0_322_0 : expNegUpper (2740297615936702771859 / 31236347484703180800 : ℝ) ≤ (7956329941800409824927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1984513 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_322_1 : expNegUpper (27438822830723333703229 / 312363474847031808000 : ℝ) ≤ (3546854540778630126229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1986293 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_322 : rowCell 0 322 ≤ (21949247342053526999 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7956329941800409824927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3546854540778630126229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_322_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_322_1
  · norm_num [gridPoint]

theorem exp_0_323_0 : expNegUpper (247945822288835537494109 / 2822614477534765568000 : ℝ) ≤ (7093708635552999711781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1986293 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_323_1 : expNegUpper (62067524161070765256207 / 705653619383691392000 : ℝ) ≤ (6323822738257460031683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1988077 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_323 : rowCell 0 323 ≤ (978418442591602382329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7093708635552999711781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6323822738257460031683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_323_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_323_1
  · norm_num [gridPoint]

theorem exp_0_324_0 : expNegUpper (797663441324382987 / 9068737663206400 : ℝ) ≤ (6323822343844464769687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1988077 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_324_1 : expNegUpper (3194825694890720327 / 36274950652825600 : ℝ) ≤ (281839646218687323259 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (248733 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_324 : rowCell 0 324 ≤ (436089405611876001523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6323822343844464769687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (281839646218687323259 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_324_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_324_1
  · norm_num [gridPoint]

theorem exp_0_325_0 : expNegUpper (27844311644638259336283 / 316152155586109952000 : ℝ) ≤ (5636792575621899060637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (248733 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_325_1 : expNegUpper (13940355432000669090237 / 158076077793054976000 : ℝ) ≤ (5023783047684052203471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (995827 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_325 : rowCell 0 325 ≤ (19434468807809538253 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5636792575621899060637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5023783047684052203471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_325_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_325_1
  · norm_num [gridPoint]

theorem exp_0_326_0 : expNegUpper (125966385222399067995157 / 1428390559551867136000 : ℝ) ≤ (5023782739340262260367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (995827 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_326_1 : expNegUpper (50452405544929052397213 / 571356223820746854400 : ℝ) ≤ (2238444853601712050791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1993449 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_326 : rowCell 0 326 ≤ (692797570562366801107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5023782739340262260367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2238444853601712050791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_326_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_326_1
  · norm_num [gridPoint]

theorem exp_0_327_0 : expNegUpper (50654346467073947211573 / 573643135247646822400 : ℝ) ≤ (1119222358653723628093 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1993449 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_327_1 : expNegUpper (31700332156446978420167 / 358526959529779264000 : ℝ) ≤ (797809038684589218243 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (997623 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_327 : rowCell 0 327 ≤ (617343559189661714561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1119222358653723628093 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (797809038684589218243 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_327_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_327_1
  · norm_num [gridPoint]

theorem exp_0_328_0 : expNegUpper (3536329173136080291087 / 39995459328867904000 : ℝ) ≤ (3989044952469068257117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (997623 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_328_1 : expNegUpper (28327588483238042942127 / 319963674630943232000 : ℝ) ≤ (3553930056477095847499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1997047 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_328 : rowCell 0 328 ≤ (275020257271981943289 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3989044952469068257117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3553930056477095847499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_328_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_328_1
  · norm_num [gridPoint]

theorem exp_0_329_0 : expNegUpper (330277012681833441833 / 3730520394096128000 : ℝ) ≤ (222120615219313231691 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1997047 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_329_1 : expNegUpper (165354164522376507141 / 1865260197048064000 : ℝ) ≤ (316589471597838951479 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (499713 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_329 : rowCell 0 329 ≤ (12250391105504974039 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (222120615219313231691 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (316589471597838951479 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_329_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_329_1
  · norm_num [gridPoint]

theorem exp_0_330_0 : expNegUpper (128659347707788896086931 / 1451328188738132224000 : ℝ) ≤ (316589452776536452809 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (499713 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_330_1 : expNegUpper (257654643225538072858621 / 2902656377476264448000 : ℝ) ≤ (2819889189375763134337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (100033 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_330 : rowCell 0 330 ≤ (436488726506489398127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (316589452776536452809 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2819889189375763134337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_330_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_330_1
  · norm_num [gridPoint]

theorem exp_0_331_0 : expNegUpper (28741971357734116883021 / 323798031981531648000 : ℝ) ≤ (88121531970550282529 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (100033 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_331_1 : expNegUpper (1438974283272469408769 / 16189901599076582400 : ℝ) ≤ (2511400108615263033503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (250309 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_331 : rowCell 0 331 ≤ (194381196655832534507 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (88121531970550282529 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2511400108615263033503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_331_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_331_1
  · norm_num [gridPoint]

theorem exp_0_332_0 : expNegUpper (13002091761642367173481 / 146286551824853017600 : ℝ) ≤ (1255699980830066752277 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (250309 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_332_1 : expNegUpper (260381148292541494957011 / 2925731036497060352000 : ℝ) ≤ (447278855719612589699 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2004287 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_332 : rowCell 0 332 ≤ (34621342159601541733 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1255699980830066752277 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (447278855719612589699 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_332_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_332_1
  · norm_num [gridPoint]

theorem exp_0_333_0 : expNegUpper (261410984447637313470219 / 2937302623466091008000 : ℝ) ≤ (1118197074382510155659 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2004287 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_333_1 : expNegUpper (130875992564183861861729 / 1468651311733045504000 : ℝ) ≤ (1991268106337292808733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1003053 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_333 : rowCell 0 333 ≤ (308284929932367991199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1118197074382510155659 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1991268106337292808733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_333_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_333_1
  · norm_num [gridPoint]

theorem exp_0_334_0 : expNegUpper (583967110791812463729 / 6553104552757504000 : ℝ) ≤ (1991267991643110837249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1003053 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_334_1 : expNegUpper (1169457295506052562697 / 13106209105515008000 : ℝ) ≤ (1772802297621987435879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (250991 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_334 : rowCell 0 334 ≤ (274479387275111477689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1991267991643110837249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1772802297621987435879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_334_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_334_1
  · norm_num [gridPoint]

theorem exp_0_335_0 : expNegUpper (264164491451220875822177 / 2960514312321417728000 : ℝ) ≤ (1772802196311714669491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (250991 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_335_1 : expNegUpper (16531804835397653146011 / 185032144520088608000 : ℝ) ≤ (1578121279136553781399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1004877 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_335 : rowCell 0 335 ≤ (244352350424997708493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1772802196311714669491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1578121279136553781399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_335_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_335_1
  · norm_num [gridPoint]

theorem exp_0_336_0 : expNegUpper (16596804326543235101979 / 185759650887982112000 : ℝ) ≤ (49316287176794211131 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1004877 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_336_1 : expNegUpper (10635798110128329665623 / 118886176568308551680 : ℝ) ≤ (1404656859020223731239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2011583 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_336 : rowCell 0 336 ≤ (5437671378730662683 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (49316287176794211131 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1404656859020223731239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_336_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_336_1
  · norm_num [gridPoint]

theorem exp_0_337_0 : expNegUpper (1186392636306964057047 / 13261410463998955520 : ℝ) ≤ (351164194999620648729 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2011583 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_337_1 : expNegUpper (14849229313429880402727 / 165767630799986944000 : ℝ) ≤ (625057844191042803991 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (402683 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_337 : rowCell 0 337 ≤ (193588393541450594023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (351164194999620648729 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (625057844191042803991 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_337_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_337_1
  · norm_num [gridPoint]

theorem exp_0_338_0 : expNegUpper (134166461638342488081487 / 1497751566448785664000 : ℝ) ≤ (1250115618602538479859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (402683 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_338_1 : expNegUpper (268682412024289913890773 / 2995503132897571328000 : ℝ) ≤ (27159427022824473 / 24414062500000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2015251 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_338 : rowCell 0 338 ≤ (34456083413620248621 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1250115618602538479859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27159427022824473 / 24414062500000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_338_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_338_1
  · norm_num [gridPoint]

theorem exp_0_339_0 : expNegUpper (10789304781595383933717 / 120288469988045312000 : ℝ) ≤ (278112517310672527937 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2015251 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_339_1 : expNegUpper (2700838158932030882947 / 30072117497011328000 : ℝ) ≤ (123729023420511590869 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2017091 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_339 : rowCell 0 339 ≤ (30660062184196304951 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (278112517310672527937 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (123729023420511590869 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_339_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_339_1
  · norm_num [gridPoint]

theorem exp_0_340_0 : expNegUpper (7531595609750122947347 / 83859533466956928000 : ℝ) ≤ (494916066484321309173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2017091 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_340_1 : expNegUpper (30165594360090668576659 / 335438133867827712000 : ℝ) ≤ (880630159349388686709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1009467 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_340 : rowCell 0 340 ≤ (68197895424648298623 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (494916066484321309173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (880630159349388686709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_340_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_340_1
  · norm_num [gridPoint]

theorem exp_0_341_0 : expNegUpper (272547400502383106176739 / 3030697498225521152000 : ℝ) ≤ (880630111330071891941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1009467 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_341_1 : expNegUpper (27290202205946734730553 / 303069749822552115200 : ℝ) ≤ (195846941525850390357 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (101039 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_341 : rowCell 0 341 ≤ (15167709829813830107 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (880630111330071891941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (195846941525850390357 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_341_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_341_1
  · norm_num [gridPoint]

theorem exp_0_342_0 : expNegUpper (27396250518635928528873 / 304247462994634803200 : ℝ) ≤ (1224043318307715509 / 1562500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (101039 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_342_1 : expNegUpper (274318844341495725370561 / 3042474629946348032000 : ℝ) ≤ (696805461046417870711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (202263 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_342 : rowCell 0 342 ≤ (107937016894008340507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1224043318307715509 / 1562500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (696805461046417870711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_342_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_342_1
  · norm_num [gridPoint]

theorem exp_0_343_0 : expNegUpper (30598085110585734463281 / 339363844441436672000 : ℝ) ≤ (696805423635664417377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (202263 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_343_1 : expNegUpper (3829733695544997196029 / 42420480555179584000 : ℝ) ≤ (619723717962392203147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2024483 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_343 : rowCell 0 343 ≤ (96002487824480943273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (696805423635664417377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (619723717962392203147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_343_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_343_1
  · norm_num [gridPoint]

theorem exp_0_344_0 : expNegUpper (1384040964607293637741 / 15330487041526336000 : ℝ) ≤ (61972368494642347249 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2024483 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_344_1 : expNegUpper (11086719090601528490607 / 122643896332210688000 : ℝ) ≤ (275554040886639644033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (101317 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_344 : rowCell 0 344 ≤ (85378104348366137533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (61972368494642347249 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (275554040886639644033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_344_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_344_1
  · norm_num [gridPoint]

theorem exp_0_345_0 : expNegUpper (278238795957259284153807 / 3077943054943359488000 : ℝ) ≤ (27555402631930118143 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (101317 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_345_1 : expNegUpper (139300153945614807276443 / 1538971527471679744000 : ℝ) ≤ (9800715991817569351 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (10141 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_345 : rowCell 0 345 ≤ (37960572553626739789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27555402631930118143 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9800715991817569351 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_345_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_345_1
  · norm_num [gridPoint]

theorem exp_0_346_0 : expNegUpper (15537476949722884817523 / 171656196660400384000 : ℝ) ≤ (490035773883653827503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (10141 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_346_1 : expNegUpper (6223062843336725593473 / 68662478664160153600 : ℝ) ≤ (435683866796598376671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (126879 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_346 : rowCell 0 346 ≤ (67504307899643664393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (490035773883653827503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (435683866796598376671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_346_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_346_1
  · norm_num [gridPoint]

theorem exp_0_347_0 : expNegUpper (56223114065411060392417 / 620340572627361894400 : ℝ) ≤ (43568384411575224441 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (126879 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_347_1 : expNegUpper (70370136858536492613609 / 775425715784202368000 : ℝ) ≤ (193659169987610302171 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2031931 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_347 : rowCell 0 347 ≤ (12002811735987701873 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43568384411575224441 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (193659169987610302171 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_347_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_347_1
  · norm_num [gridPoint]

theorem exp_0_348_0 : expNegUpper (70640440411432014155721 / 778404256173041792000 : ℝ) ≤ (77463663993269468449 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2031931 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_348_1 : expNegUpper (282928476335548217526403 / 3113617024692167168000 : ℝ) ≤ (172142391931507081413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1016901 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_348 : rowCell 0 348 ≤ (26674577815450318821 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (77463663993269468449 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (172142391931507081413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_348_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_348_1
  · norm_num [gridPoint]

theorem exp_0_349_0 : expNegUpper (50491230052154459987 / 555654048809472000 : ℝ) ≤ (344284766212978734567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1016901 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_349_1 : expNegUpper (25278366635262047969 / 277827024404736000 : ℝ) ≤ (305999733238429680177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (508919 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_349 : rowCell 0 349 ≤ (23709664969988338739 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (344284766212978734567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (305999733238429680177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_349_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_349_1
  · norm_num [gridPoint]

theorem exp_0_350_0 : expNegUpper (142734901256158145551561 / 1568756931360073984000 : ℝ) ≤ (305999717670590362553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (508919 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_350_1 : expNegUpper (285840002359934083558041 / 3137513862720147968000 : ℝ) ≤ (54388612608557367781 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2037553 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_350 : rowCell 0 350 ≤ (21072053407543256353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (305999717670590362553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (54388612608557367781 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_350_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_350_1
  · norm_num [gridPoint]

theorem exp_0_351_0 : expNegUpper (286931672044909064380689 / 3149496539192771072000 : ℝ) ≤ (135971524656383700467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2037553 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_351_1 : expNegUpper (1795647621672468724849 / 19684353369954819200 : ℝ) ≤ (3020639638886796701 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1019717 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_351 : rowCell 0 351 ≤ (936293799640110701 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (135971524656383700467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3020639638886796701 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_351_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_351_1
  · norm_num [gridPoint]

theorem sum_0_320_2 : blockSum (rowCell 0) 320 2 ≤ (1305540353149405532987 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_320) (by simpa only [blockSum_one] using cell_0_321) (by norm_num)

theorem sum_0_322_2 : blockSum (rowCell 0) 322 2 ≤ (2075880809694278732279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_322) (by simpa only [blockSum_one] using cell_0_323) (by norm_num)

theorem sum_0_320_4 : blockSum (rowCell 0) 320 4 ≤ (4686961515993089798253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_320_2 sum_0_322_2 (by norm_num)

theorem sum_0_324_2 : blockSum (rowCell 0) 324 2 ≤ (824778781768066766583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_324) (by simpa only [blockSum_one] using cell_0_325) (by norm_num)

theorem sum_0_326_2 : blockSum (rowCell 0) 326 2 ≤ (327535282438007128917 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_326) (by simpa only [blockSum_one] using cell_0_327) (by norm_num)

theorem sum_0_324_4 : blockSum (rowCell 0) 324 4 ≤ (1479849346644081024417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_324_2 sum_0_326_2 (by norm_num)

theorem sum_0_320_8 : blockSum (rowCell 0) 320 8 ≤ (7646660209281251847087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_320_4 sum_0_324_4 (by norm_num)

theorem sum_0_328_2 : blockSum (rowCell 0) 328 2 ≤ (520028079382081424069 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_328) (by simpa only [blockSum_one] using cell_0_329) (by norm_num)

theorem sum_0_330_2 : blockSum (rowCell 0) 330 2 ≤ (825251119818154467141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_330) (by simpa only [blockSum_one] using cell_0_331) (by norm_num)

theorem sum_0_328_4 : blockSum (rowCell 0) 328 4 ≤ (1865307278582317315279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_328_2 sum_0_330_2 (by norm_num)

theorem sum_0_332_2 : blockSum (rowCell 0) 332 2 ≤ (654498351528383408529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_332) (by simpa only [blockSum_one] using cell_0_333) (by norm_num)

theorem sum_0_334_2 : blockSum (rowCell 0) 334 2 ≤ (259415868850054593091 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_334) (by simpa only [blockSum_one] using cell_0_335) (by norm_num)

theorem sum_0_332_4 : blockSum (rowCell 0) 332 4 ≤ (1173330089228492594711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_332_2 sum_0_334_2 (by norm_num)

theorem sum_0_328_8 : blockSum (rowCell 0) 328 8 ≤ (303863736781080990999 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_328_4 sum_0_332_4 (by norm_num)

theorem sum_0_320_16 : blockSum (rowCell 0) 320 16 ≤ (10685297577092061757077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_320_8 sum_0_328_8 (by norm_num)

theorem sum_0_336_2 : blockSum (rowCell 0) 336 2 ≤ (411095248690677101343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_336) (by simpa only [blockSum_one] using cell_0_337) (by norm_num)

theorem sum_0_338_2 : blockSum (rowCell 0) 338 2 ≤ (16279036399454138393 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_338) (by simpa only [blockSum_one] using cell_0_339) (by norm_num)

theorem sum_0_336_4 : blockSum (rowCell 0) 336 4 ≤ (736675976679759869203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_336_2 sum_0_338_2 (by norm_num)

theorem sum_0_340_2 : blockSum (rowCell 0) 340 2 ≤ (128868734743903619051 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_340) (by simpa only [blockSum_one] using cell_0_341) (by norm_num)

theorem sum_0_342_2 : blockSum (rowCell 0) 342 2 ≤ (10196975235924464189 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_342) (by simpa only [blockSum_one] using cell_0_343) (by norm_num)

theorem sum_0_340_4 : blockSum (rowCell 0) 340 4 ≤ (230838487103148260941 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_340_2 sum_0_342_2 (by norm_num)

theorem sum_0_336_8 : blockSum (rowCell 0) 336 8 ≤ (239670590177211278217 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_336_4 sum_0_340_4 (by norm_num)

theorem sum_0_344_2 : blockSum (rowCell 0) 344 2 ≤ (161299249455619617111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_344) (by simpa only [blockSum_one] using cell_0_345) (by norm_num)

theorem sum_0_346_2 : blockSum (rowCell 0) 346 2 ≤ (63759183289791086879 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_346) (by simpa only [blockSum_one] using cell_0_347) (by norm_num)

theorem sum_0_344_4 : blockSum (rowCell 0) 344 4 ≤ (288817616035201790869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_344_2 sum_0_346_2 (by norm_num)

theorem sum_0_348_2 : blockSum (rowCell 0) 348 2 ≤ (1259606069635966439 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_348) (by simpa only [blockSum_one] using cell_0_349) (by norm_num)

theorem sum_0_350_2 : blockSum (rowCell 0) 350 2 ≤ (39797929400345470373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_350) (by simpa only [blockSum_one] using cell_0_351) (by norm_num)

theorem sum_0_348_4 : blockSum (rowCell 0) 348 4 ≤ (90182172185784127933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_348_2 sum_0_350_2 (by norm_num)

theorem sum_0_344_8 : blockSum (rowCell 0) 344 8 ≤ (93836392081354009347 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_344_4 sum_0_348_4 (by norm_num)

theorem sum_0_336_16 : blockSum (rowCell 0) 336 16 ≤ (83376745564641321891 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_336_8 sum_0_344_8 (by norm_num)

theorem sum_0_320_32 : blockSum (rowCell 0) 320 32 ≤ (12352832488384888194897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_320_16 sum_0_336_16 (by norm_num)

#print axioms sum_0_320_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
