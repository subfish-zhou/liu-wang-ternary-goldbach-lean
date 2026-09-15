import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_320_0 : expNegUpper (4018925428089479441363 / 43572709073712392000 : ℝ) ≤ (87763990310029972623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (513909 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_320_1 : expNegUpper (257503849113283409500111 / 2788653380717593088000 : ℝ) ≤ (19755342084266069663 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2057321 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_320 : rowCell 5 320 ≤ (6081069099383386151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (87763990310029972623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19755342084266069663 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_320_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_320_1
  · norm_num [gridPoint]

theorem exp_5_321_0 : expNegUpper (258547061380778332628039 / 2799950908017562112000 : ℝ) ≤ (79021361745099194039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2057321 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_321_1 : expNegUpper (25884133074801672973051 / 279995090801756211200 : ℝ) ≤ (35568947356210933283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2059011 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_321 : rowCell 5 321 ≤ (5474873944794704647 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (79021361745099194039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35568947356210933283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_321_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_321_1
  · norm_num [gridPoint]

theorem exp_5_322_0 : expNegUpper (25988784164965454546731 / 281127127362328627200 : ℝ) ≤ (71137888825840617103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2059011 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_322_1 : expNegUpper (260183761999354163329061 / 2811271273623286272000 : ℝ) ≤ (64030400503670530501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (412141 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_322 : rowCell 5 322 ≤ (4928296549083948683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (71137888825840617103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64030400503670530501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_322_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_322_1
  · norm_num [gridPoint]

theorem exp_5_323_0 : expNegUpper (261233578196693969494109 / 2822614477534765568000 : ℝ) ≤ (12806079049553836663 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (412141 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_323_1 : expNegUpper (65382788214908589256207 / 705653619383691392000 : ℝ) ≤ (57623628927127260631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2062403 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_323 : rowCell 5 323 ≤ (8871120741370793327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12806079049553836663 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (57623628927127260631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_323_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_323_1
  · norm_num [gridPoint]

theorem exp_5_324_0 : expNegUpper (4201348496227764023 / 45343688316032000 : ℝ) ≤ (28811812117512405677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2062403 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_324_1 : expNegUpper (16824544852556541283 / 181374753264128000 : ℝ) ≤ (25924751317371372319 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (412821 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_324 : rowCell 5 324 ≤ (99785984576323403 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28811812117512405677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25924751317371372319 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_324_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_324_1
  · norm_num [gridPoint]

theorem exp_5_325_0 : expNegUpper (263939960094617038026547 / 2845369400274989568000 : ℝ) ≤ (25924749223285975071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (412821 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_325_1 : expNegUpper (132120426688188805812133 / 1422684700137494784000 : ℝ) ≤ (23323225665909825139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2065811 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_325 : rowCell 5 325 ≤ (7182413150295194527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25924749223285975071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23323225665909825139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_325_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_325_1
  · norm_num [gridPoint]

theorem exp_5_326_0 : expNegUpper (132650312715088987995157 / 1428390559551867136000 : ℝ) ≤ (23323223797000213863 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2065811 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_326_1 : expNegUpper (53120636603503593197213 / 571356223820746854400 : ℝ) ≤ (5244850132611210723 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2067521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_326 : rowCell 5 326 ≤ (1292234867638535091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23323223797000213863 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5244850132611210723 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_326_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_326_1
  · norm_num [gridPoint]

theorem exp_5_327_0 : expNegUpper (53333257402651342411573 / 573643135247646822400 : ℝ) ≤ (20979398862738389649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2067521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_327_1 : expNegUpper (33371314029619458420167 / 358526959529779264000 : ℝ) ≤ (2358513726924855753 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (413847 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_327 : rowCell 5 327 ≤ (5811432266611690479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20979398862738389649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2358513726924855753 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_327_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_327_1
  · norm_num [gridPoint]

theorem exp_5_328_0 : expNegUpper (33504619354523986619783 / 359959133959811136000 : ℝ) ≤ (9434054163723782101 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (413847 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_328_1 : expNegUpper (268342851027029362479143 / 2879673071678489088000 : ℝ) ≤ (16966606575288214833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2070953 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_328 : rowCell 5 328 ≤ (1306549802979581717 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9434054163723782101 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16966606575288214833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_328_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_328_1
  · norm_num [gridPoint]

theorem exp_5_329_0 : expNegUpper (347629211472673761833 / 3730520394096128000 : ℝ) ≤ (33933210495812025011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2070953 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_329_1 : expNegUpper (174013038309727547141 / 1865260197048064000 : ℝ) ≤ (30508669067797514013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (82907 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_329 : rowCell 5 329 ≤ (4699159754779578017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33933210495812025011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (30508669067797514013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_329_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_329_1
  · norm_num [gridPoint]

theorem exp_5_330_0 : expNegUpper (135396674585493088086931 / 1451328188738132224000 : ℝ) ≤ (30508666699851362239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (82907 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_330_1 : expNegUpper (271102597288439320858621 / 2902656377476264448000 : ℝ) ≤ (548508830280296371 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2074401 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_330 : rowCell 5 330 ≤ (4224607221130470299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30508666699851362239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (548508830280296371 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_330_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_330_1
  · norm_num [gridPoint]

theorem exp_5_331_0 : expNegUpper (272179095667522571947189 / 2914182287833784832000 : ℝ) ≤ (5485087880439259091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2074401 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_331_1 : expNegUpper (13624501237222643878921 / 145709114391689241600 : ℝ) ≤ (2464997512868991379 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2076131 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_331 : rowCell 5 331 ≤ (949346503524366243 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5485087880439259091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2464997512868991379 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_331_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_331_1
  · norm_num [gridPoint]

theorem exp_5_332_0 : expNegUpper (13678494418663499973481 / 146286551824853017600 : ℝ) ≤ (24649973245558275761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2076131 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_332_1 : expNegUpper (273882501740457014957011 / 2925731036497060352000 : ℝ) ≤ (22151963870386333689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (415573 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_332 : rowCell 5 332 ≤ (106651228222189329 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24649973245558275761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22151963870386333689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_332_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_332_1
  · norm_num [gridPoint]

theorem exp_5_333_0 : expNegUpper (274965737280567105470219 / 2937302623466091008000 : ℝ) ≤ (2768995273926310117 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (415573 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_333_1 : expNegUpper (137640019134395189861729 / 1468651311733045504000 : ℝ) ≤ (1990404163260712297 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1039801 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_333 : rowCell 5 333 ≤ (1533380791769149659 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2768995273926310117 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1990404163260712297 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_333_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_333_1
  · norm_num [gridPoint]

theorem exp_5_334_0 : expNegUpper (5527333047635050733561 / 58977940974817536000 : ℝ) ≤ (19904040135860540501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1039801 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_334_1 : expNegUpper (11067305772871664744273 / 117955881949635072000 : ℝ) ≤ (8940750881897524949 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (32521 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_334 : rowCell 5 334 ≤ (688838915817671531 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19904040135860540501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8940750881897524949 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_334_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_334_1
  · norm_num [gridPoint]

theorem exp_5_335_0 : expNegUpper (277772643669164939822177 / 2960514312321417728000 : ℝ) ≤ (894075021484116949 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (32521 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_335_1 : expNegUpper (17380645618237461146011 / 185032144520088608000 : ℝ) ≤ (16062042848898776339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (208309 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_335 : rowCell 5 335 ≤ (30939920900328741 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (894075021484116949 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16062042848898776339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_335_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_335_1
  · norm_num [gridPoint]

theorem exp_5_336_0 : expNegUpper (17448982570946435101979 / 185759650887982112000 : ℝ) ≤ (8031020829955274717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (208309 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_336_1 : expNegUpper (11180124198846092225623 / 118886176568308551680 : ℝ) ≤ (14425538345541294483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2084839 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_336 : rowCell 5 336 ≤ (2223181725182709607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8031020829955274717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14425538345541294483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_336_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_336_1
  · norm_num [gridPoint]

theorem exp_5_337_0 : expNegUpper (11223995790881009953423 / 119352694175990599680 : ℝ) ≤ (1442553728603453133 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2084839 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_337_1 : expNegUpper (140460489776094523624543 / 1491908677199882496000 : ℝ) ≤ (12953827883060280303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2086593 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_337 : rowCell 5 337 ≤ (1996527906778787773 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1442553728603453133 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12953827883060280303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_337_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_337_1
  · norm_num [gridPoint]

theorem exp_5_338_0 : expNegUpper (3000225261405855831521 / 31867054605293312000 : ℝ) ≤ (1295382693906153537 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2086593 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_338_1 : expNegUpper (6007318375047835104059 / 63734109210586624000 : ℝ) ≤ (11630528229227772667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (41767 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_338 : rowCell 5 338 ≤ (448178316594563213 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1295382693906153537 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11630528229227772667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_338_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_338_1
  · norm_num [gridPoint]

theorem exp_5_339_0 : expNegUpper (11337902821114288253717 / 120288469988045312000 : ℝ) ≤ (2907631847064221941 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (41767 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_339_1 : expNegUpper (2837720671886685602947 / 30072117497011328000 : ℝ) ≤ (10440862108866743671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2090111 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_339 : rowCell 5 339 ≤ (1609465551894256527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2907631847064221941 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10440862108866743671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_339_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_339_1
  · norm_num [gridPoint]

theorem exp_5_340_0 : expNegUpper (71219773157871042526123 / 754735801202612352000 : ℝ) ≤ (2088172271955791377 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2090111 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_340_1 : expNegUpper (285205300228788625189931 / 3018943204810449408000 : ℝ) ≤ (937150322230679259 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (522969 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_340 : rowCell 5 340 ≤ (144473542549699707 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2088172271955791377 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (937150322230679259 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_340_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_340_1
  · norm_num [gridPoint]

theorem exp_5_341_0 : expNegUpper (286315750875369986176739 / 3030697498225521152000 : ℝ) ≤ (9371502555151348503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (522969 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_341_1 : expNegUpper (28664367273994709130553 / 303069749822552115200 : ℝ) ≤ (4205217980493078833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (418729 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_341 : rowCell 5 341 ≤ (1296674932557132543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9371502555151348503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4205217980493078833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_341_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_341_1
  · norm_num [gridPoint]

theorem exp_5_342_0 : expNegUpper (28775755525185330128873 / 304247462994634803200 : ℝ) ≤ (4205217683439858097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (418729 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_342_1 : expNegUpper (288087194714482605370561 / 3042474629946348032000 : ℝ) ≤ (7546828453730825891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1047709 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_342 : rowCell 5 342 ≤ (1163618014403134559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4205217683439858097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7546828453730825891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_342_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_342_1
  · norm_num [gridPoint]

theorem exp_5_343_0 : expNegUpper (289204515753272762169529 / 3054274599972930048000 : ℝ) ≤ (7546827924744140347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1047709 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_343_1 : expNegUpper (36191984518091726764261 / 381784324996616256000 : ℝ) ≤ (846364712680356543 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (419439 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_343 : rowCell 5 343 ≤ (208812574932228307 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7546827924744140347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (846364712680356543 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_343_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_343_1
  · norm_num [gridPoint]

theorem exp_5_344_0 : expNegUpper (1453283211859835077741 / 15330487041526336000 : ℝ) ≤ (3385458615249671581 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (419439 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_344_1 : expNegUpper (11639589080921574570607 / 122643896332210688000 : ℝ) ≤ (6073905671136650807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (65593 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_344 : rowCell 5 344 ≤ (936656026257872369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3385458615249671581 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6073905671136650807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_344_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_344_1
  · norm_num [gridPoint]

theorem exp_5_345_0 : expNegUpper (292113945100274708153807 / 3077943054943359488000 : ℝ) ≤ (6073905251921641597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (65593 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_345_1 : expNegUpper (146224378670868951276443 / 1538971527471679744000 : ℝ) ≤ (5447865323417122683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (52519 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_345 : rowCell 5 345 ≤ (840177861944453973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6073905251921641597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5447865323417122683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_345_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_345_1
  · norm_num [gridPoint]

theorem exp_5_346_0 : expNegUpper (146788216965267243357707 / 1544905769943603456000 : ℝ) ≤ (2723932475148315709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (52519 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_346_1 : expNegUpper (58782595418633615141257 / 617962307977441382400 : ℝ) ≤ (2442827820731173797 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2102549 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_346 : rowCell 5 346 ≤ (753529605573471409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2723932475148315709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2442827820731173797 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_346_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_346_1
  · norm_num [gridPoint]

theorem exp_5_347_0 : expNegUpper (59008823771016999592417 / 620340572627361894400 : ℝ) ≤ (4885655309410439161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2102549 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_347_1 : expNegUpper (73845599067417132613609 / 775425715784202368000 : ℝ) ≤ (136901400473429287 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2104341 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_347 : rowCell 5 347 ≤ (675721514454133719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4885655309410439161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (136901400473429287 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_347_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_347_1
  · norm_num [gridPoint]

theorem exp_5_348_0 : expNegUpper (74129252466566222155721 / 778404256173041792000 : ℝ) ≤ (4380844519683545497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2104341 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_348_1 : expNegUpper (296857024863577913526403 / 3113617024692167168000 : ℝ) ≤ (1963820405937782633 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2106137 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_348 : rowCell 5 348 ≤ (60586221503208043 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4380844519683545497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1963820405937782633 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_348_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_348_1
  · norm_num [gridPoint]

theorem exp_5_349_0 : expNegUpper (476792187130260488683 / 5000886439285248000 : ℝ) ≤ (785528109799436967 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2106137 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_349_1 : expNegUpper (238669498293787897321 / 2500443219642624000 : ℝ) ≤ (3520828636530331841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2107937 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_349 : rowCell 5 349 ≤ (543149064992700389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (785528109799436967 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3520828636530331841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_349_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_349_1
  · norm_num [gridPoint]

theorem exp_5_350_0 : expNegUpper (149739225058933697551561 / 1568756931360073984000 : ℝ) ≤ (3520828402674861047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2107937 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_350_1 : expNegUpper (299821950272978051558041 / 3137513862720147968000 : ℝ) ≤ (3155713647617237587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2109741 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_350 : rowCell 5 350 ≤ (243429722381524071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3520828402674861047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3155713647617237587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_350_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_350_1
  · norm_num [gridPoint]

theorem exp_5_351_0 : expNegUpper (300967019342967304380689 / 3149496539192771072000 : ℝ) ≤ (1577856719803164977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2109741 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_351_1 : expNegUpper (1883201669207163124849 / 19684353369954819200 : ℝ) ≤ (1414035177598707353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (527887 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_351 : rowCell 5 351 ≤ (87268578074568441 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1577856719803164977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1414035177598707353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_351_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_351_1
  · norm_num [gridPoint]

theorem sum_5_320_2 : blockSum (rowCell 5) 320 2 ≤ (5777971522089045399 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_320) (by simpa only [blockSum_one] using cell_5_321) (by norm_num)

theorem sum_5_322_2 : blockSum (rowCell 5) 322 2 ≤ (18727713839538690693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_322) (by simpa only [blockSum_one] using cell_5_323) (by norm_num)

theorem sum_5_320_4 : blockSum (rowCell 5) 320 4 ≤ (41839599927894872289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_320_2 sum_5_322_2 (by norm_num)

theorem sum_5_324_2 : blockSum (rowCell 5) 324 2 ≤ (15165291916401066767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_324) (by simpa only [blockSum_one] using cell_5_325) (by norm_num)

theorem sum_5_326_2 : blockSum (rowCell 5) 326 2 ≤ (6136303302402182967 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_326) (by simpa only [blockSum_one] using cell_5_327) (by norm_num)

theorem sum_5_324_4 : blockSum (rowCell 5) 324 4 ≤ (27437898521205432701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_324_2 sum_5_326_2 (by norm_num)

theorem sum_5_320_8 : blockSum (rowCell 5) 320 8 ≤ (6927749844910030499 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_320_4 sum_5_324_4 (by norm_num)

theorem sum_5_328_2 : blockSum (rowCell 5) 328 2 ≤ (1985071793339580977 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_328) (by simpa only [blockSum_one] using cell_5_329) (by norm_num)

theorem sum_5_330_2 : blockSum (rowCell 5) 330 2 ≤ (8021993235227935271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_330) (by simpa only [blockSum_one] using cell_5_331) (by norm_num)

theorem sum_5_328_4 : blockSum (rowCell 5) 328 4 ≤ (4486838050481460039 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_328_2 sum_5_330_2 (by norm_num)

theorem sum_5_332_2 : blockSum (rowCell 5) 332 2 ≤ (3239800443324178923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_332) (by simpa only [blockSum_one] using cell_5_333) (by norm_num)

theorem sum_5_334_2 : blockSum (rowCell 5) 334 2 ≤ (1307637333824246351 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_334) (by simpa only [blockSum_one] using cell_5_335) (by norm_num)

theorem sum_5_332_4 : blockSum (rowCell 5) 332 4 ≤ (46840600887781373 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_332_2 sum_5_334_2 (by norm_num)

theorem sum_5_328_8 : blockSum (rowCell 5) 328 8 ≤ (14828751211935591703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_328_4 sum_5_332_4 (by norm_num)

theorem sum_5_320_16 : blockSum (rowCell 5) 320 16 ≤ (24733750218242872099 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_320_8 sum_5_328_8 (by norm_num)

theorem sum_5_336_2 : blockSum (rowCell 5) 336 2 ≤ (210985481598074869 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_336) (by simpa only [blockSum_one] using cell_5_337) (by norm_num)

theorem sum_5_338_2 : blockSum (rowCell 5) 338 2 ≤ (3402178818272509379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_338) (by simpa only [blockSum_one] using cell_5_339) (by norm_num)

theorem sum_5_336_4 : blockSum (rowCell 5) 336 4 ≤ (7621888450234006759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_336_2 sum_5_338_2 (by norm_num)

theorem sum_5_340_2 : blockSum (rowCell 5) 340 2 ≤ (2741410358054129613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_340) (by simpa only [blockSum_one] using cell_5_341) (by norm_num)

theorem sum_5_342_2 : blockSum (rowCell 5) 342 2 ≤ (1103840444532138047 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_342) (by simpa only [blockSum_one] using cell_5_343) (by norm_num)

theorem sum_5_340_4 : blockSum (rowCell 5) 340 4 ≤ (4949091247118405707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_340_2 sum_5_342_2 (by norm_num)

theorem sum_5_336_8 : blockSum (rowCell 5) 336 8 ≤ (6285489848676206233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_336_4 sum_5_340_4 (by norm_num)

theorem sum_5_344_2 : blockSum (rowCell 5) 344 2 ≤ (888416944101163171 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_344) (by simpa only [blockSum_one] using cell_5_345) (by norm_num)

theorem sum_5_346_2 : blockSum (rowCell 5) 346 2 ≤ (178656390003450641 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_346) (by simpa only [blockSum_one] using cell_5_347) (by norm_num)

theorem sum_5_344_4 : blockSum (rowCell 5) 344 4 ≤ (320608500822993147 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_344_2 sum_5_346_2 (by norm_num)

theorem sum_5_348_2 : blockSum (rowCell 5) 348 2 ≤ (1149011280024780819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_348) (by simpa only [blockSum_one] using cell_5_349) (by norm_num)

theorem sum_5_350_2 : blockSum (rowCell 5) 350 2 ≤ (923202335135890347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_350) (by simpa only [blockSum_one] using cell_5_351) (by norm_num)

theorem sum_5_348_4 : blockSum (rowCell 5) 348 4 ≤ (1036106807580335583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_348_2 sum_5_350_2 (by norm_num)

theorem sum_5_344_8 : blockSum (rowCell 5) 344 8 ≤ (1319574655847650659 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_344_4 sum_5_348_4 (by norm_num)

theorem sum_5_336_16 : blockSum (rowCell 5) 336 16 ≤ (8924639160371507551 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_336_8 sum_5_344_8 (by norm_num)

theorem sum_5_320_32 : blockSum (rowCell 5) 320 32 ≤ (58392139596857251749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_320_16 sum_5_336_16 (by norm_num)

#print axioms sum_5_320_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
