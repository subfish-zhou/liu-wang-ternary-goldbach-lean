import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_96_0 : expNegUpper (140397635375576118129 / 2003684063831632000 : ℝ) ≤ (46391629763640607341715051069 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (864393 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_96_1 : expNegUpper (898958733198791203439 / 12823578008522444800 : ℝ) ≤ (359346354008404990799807807491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (864611 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_96 : rowCell 1 96 ≤ (26633606781644566110604533897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (46391629763640607341715051069 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (359346354008404990799807807491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_96_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_96_1
  · norm_num [gridPoint]

theorem exp_1_97_0 : expNegUpper (3924378083353295949289 / 55980954490985164800 : ℝ) ≤ (359346076522443985486033848101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (864611 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_97_1 : expNegUpper (9815579024840653066781 / 139952386227462912000 : ℝ) ≤ (347642959959207260326520220313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (172967 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_97 : rowCell 1 97 ≤ (25777137862852236414096301193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (359346076522443985486033848101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (347642959959207260326520220313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_97_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_97_1
  · norm_num [gridPoint]

theorem exp_1_98_0 : expNegUpper (29664317093163455242567 / 422959451240675584000 : ℝ) ≤ (43455336930163932615944865813 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (172967 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_98_1 : expNegUpper (59357341972913654635653 / 845918902481351168000 : ℝ) ≤ (336042758065923495344710445247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108133 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_98 : rowCell 1 98 ≤ (6231869689799651052222488557 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43455336930163932615944865813 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (336042758065923495344710445247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_98_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_98_1
  · norm_num [gridPoint]

theorem exp_1_99_0 : expNegUpper (95670904186657160973 / 1363434121445888000 : ℝ) ≤ (84010626526198656480331450617 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108133 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_99_1 : expNegUpper (23929572448747713463 / 340858530361472000 : ℝ) ≤ (324564102051868744778709335047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (865299 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_99 : rowCell 1 99 ≤ (48172027380533408743693675541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (84010626526198656480331450617 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (324564102051868744778709335047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_99_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_99_1
  · norm_num [gridPoint]

theorem exp_1_100_0 : expNegUpper (5021893669469960944781 / 71533048969313664000 : ℝ) ≤ (324563862234718455394791887427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (865299 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_100_1 : expNegUpper (20097750529416484065097 / 286132195877254656000 : ℝ) ≤ (62644816725450143132126922713 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1731079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_100 : rowCell 1 100 ≤ (46508070024862402316288820563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (324563862234718455394791887427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (62644816725450143132126922713 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_100_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_100_1
  · norm_num [gridPoint]

theorem exp_1_101_0 : expNegUpper (60733870929601974401939 / 864669687665603072000 : ℝ) ≤ (156611927770568487897803489853 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1731079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_101_1 : expNegUpper (6076531336439280697809 / 86466968766560307200 : ℝ) ≤ (302038534470169849602402842971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1731571 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_101 : rowCell 1 101 ≤ (8973097250885603898299763959 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (156611927770568487897803489853 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (302038534470169849602402842971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_101_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_101_1
  · norm_num [gridPoint]

theorem exp_1_102_0 : expNegUpper (6120776579688670153089 / 87096562600519731200 : ℝ) ≤ (302038317703242243874977879669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1731571 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_102_1 : expNegUpper (61240126442637994734961 / 870965626005197312000 : ℝ) ≤ (29102203425141063807368609743 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (866037 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_102 : rowCell 1 102 ≤ (43246493692193247410145202963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (302038317703242243874977879669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29102203425141063807368609743 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_102_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_102_1
  · norm_num [gridPoint]

theorem exp_1_103_0 : expNegUpper (20561472875944119817763 / 292428134216848896000 : ℝ) ≤ (72755457098516271927137302289 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (866037 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_103_1 : expNegUpper (2571570867305152591457 / 36553516777106112000 : ℝ) ≤ (70046981065065746047136481777 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1732587 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_103 : rowCell 1 103 ≤ (41653128359815753375613272383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (72755457098516271927137302289 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (70046981065065746047136481777 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_103_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_103_1
  · norm_num [gridPoint]

theorem exp_1_104_0 : expNegUpper (310819197073887974491 / 4418130088008256000 : ℝ) ≤ (56037545781241383505097557211 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1732587 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_104_1 : expNegUpper (2487921858991538243487 / 35345040704066048000 : ℝ) ≤ (134774163090898589824131492751 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1733111 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_104 : rowCell 1 104 ≤ (10021811760126062973647740201 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (56037545781241383505097557211 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (134774163090898589824131492751 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_104_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_104_1
  · norm_num [gridPoint]

theorem exp_1_105_0 : expNegUpper (62646038150061054594687 / 889990470858510848000 : ℝ) ≤ (269548140929026625459952531249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1733111 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_105_1 : expNegUpper (31340586706685511570323 / 444995235429255424000 : ℝ) ≤ (16194635348325797998264961911 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (866823 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_105 : rowCell 1 105 ≤ (1542021214407371786991218867 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (269548140929026625459952531249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16194635348325797998264961911 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_105_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_105_1
  · norm_num [gridPoint]

theorem exp_1_106_0 : expNegUpper (10521837471003564211969 / 149396293736854272000 : ℝ) ≤ (259113990024903247285059735753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (866823 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_106_1 : expNegUpper (4211139441560667338963 / 59758517494741708800 : ℝ) ≤ (31111899948473535632981320119 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1734191 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_106 : rowCell 1 106 ≤ (926112163026593979785778339 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (259113990024903247285059735753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31111899948473535632981320119 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_106_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_106_1
  · norm_num [gridPoint]

theorem exp_1_107_0 : expNegUpper (12723761886999446731729 / 180557578457899110400 : ℝ) ≤ (62223758338275432944814660299 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1734191 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_107_1 : expNegUpper (15913952774311015911909 / 225696973072373888000 : ℝ) ≤ (9556001939970557741738448001 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (867373 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_107 : rowCell 1 107 ≤ (17785227811034178389659576789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (62223758338275432944814660299 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9556001939970557741738448001 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_107_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_107_1
  · norm_num [gridPoint]

theorem exp_1_108_0 : expNegUpper (16027350492331811621061 / 227305215115905152000 : ℝ) ≤ (119449945597037096475855010271 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (867373 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_108_1 : expNegUpper (64147341827211830559283 / 909220860463620608000 : ℝ) ≤ (45827246117375111772431041683 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108457 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_108 : rowCell 1 108 ≤ (17064807250735009237154848883 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (119449945597037096475855010271 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45827246117375111772431041683 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_108_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_108_1
  · norm_num [gridPoint]

theorem exp_1_109_0 : expNegUpper (66259294791128277413 / 939155555839488000 : ℝ) ≤ (229136081834415207900357655771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108457 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_109_1 : expNegUpper (33149586567001003871 / 469577777919744000 : ℝ) ≤ (27451274993925815513398621383 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108493 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_109 : rowCell 1 109 ≤ (32722982038309662647202650559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (229136081834415207900357655771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27451274993925815513398621383 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_109_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_109_1
  · norm_num [gridPoint]

theorem exp_1_110_0 : expNegUpper (32549525391702176184001 / 461077655864568064000 : ℝ) ≤ (109805029691419094964262178223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108493 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_110_1 : expNegUpper (65138877024903091344201 / 922155311729136128000 : ℝ) ≤ (52581846711304592446838696163 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1736473 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_110 : rowCell 1 110 ≤ (6270284970174845970809455341 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (109805029691419094964262178223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (52581846711304592446838696163 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_110_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_110_1
  · norm_num [gridPoint]

theorem exp_1_111_0 : expNegUpper (65598127047828738884289 / 928656794820526592000 : ℝ) ≤ (52581813525033389010014087213 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1736473 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_111_1 : expNegUpper (164097253693259696689 / 2321641987051316480 : ℝ) ≤ (3145191251780426539109340891 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1737069 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_111 : rowCell 1 111 ≤ (30015663332480108876547263301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (52581813525033389010014087213 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3145191251780426539109340891 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_111_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_111_1
  · norm_num [gridPoint]

theorem exp_1_112_0 : expNegUpper (1776883096961340773 / 25139277317679360 : ℝ) ≤ (1610336918726369791710405971 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1737069 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_112_1 : expNegUpper (711201904894548024427 / 10055710927071744000 : ℝ) ≤ (38501654272821940127523506151 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (69507 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_112 : rowCell 1 112 ≤ (3589534745887027624012756857 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1610336918726369791710405971 / 8000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38501654272821940127523506151 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_112_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_112_1
  · norm_num [gridPoint]

theorem exp_1_113_0 : expNegUpper (66604833253142412710999 / 941728275920572928000 : ℝ) ≤ (192508153220565554900776496851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (69507 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_113_1 : expNegUpper (33323757025454500430799 / 470864137960286464000 : ℝ) ≤ (36795620097789964418747008897 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (173829 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_113 : rowCell 1 113 ≤ (27453715869866428433161300101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (192508153220565554900776496851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36795620097789964418747008897 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_113_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_113_1
  · norm_num [gridPoint]

theorem exp_1_114_0 : expNegUpper (1342249663574179869591 / 18965965478584576000 : ℝ) ≤ (183977989142210990345660628593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (173829 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_114_1 : expNegUpper (2686244886271625166973 / 37931930957169152000 : ℝ) ≤ (35140700440841092468001468361 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (347783 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_114 : rowCell 1 114 ≤ (13114148750160284637935309091 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (183977989142210990345660628593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35140700440841092468001468361 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_114_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_114_1
  · norm_num [gridPoint]

theorem exp_1_115_0 : expNegUpper (22541003658666755263439 / 318297036747879936000 : ℝ) ≤ (43925849332809827087224632977 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (347783 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_115_1 : expNegUpper (5638967622098041494913 / 79574259186969984000 : ℝ) ≤ (167685453265794750684619602507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (34791 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_115 : rowCell 1 115 ≤ (3130027937369522732188944411 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43925849332809827087224632977 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (167685453265794750684619602507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_115_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_115_1
  · norm_num [gridPoint]

theorem exp_1_116_0 : expNegUpper (17034106659338719093091 / 240376696215951488000 : ℝ) ≤ (167685354553526566510522018413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (34791 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_116_1 : expNegUpper (13636398393681050776911 / 192301356972761190400 : ℝ) ≤ (79962090031242959677590991229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (870097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_116 : rowCell 1 116 ≤ (1493098850055680440190306607 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (167685354553526566510522018413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (79962090031242959677590991229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_116_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_116_1
  · norm_num [gridPoint]

theorem exp_1_117_0 : expNegUpper (13730548031022294390951 / 193629059557945446400 : ℝ) ≤ (39981021801984161107264408859 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (870097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_117_1 : expNegUpper (34349636829407771870093 / 484072648894863616000 : ℝ) ≤ (76209603149083102054463977883 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108803 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_117 : rowCell 1 117 ≤ (22776353583392779104667892657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (39981021801984161107264408859 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (76209603149083102054463977883 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_117_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_117_1
  · norm_num [gridPoint]

theorem exp_1_118_0 : expNegUpper (11528660253601449877759 / 162467774836900608000 : ℝ) ≤ (19052389876067810961551081693 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108803 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_118_1 : expNegUpper (23073155509582004744971 / 324935549673801216000 : ℝ) ≤ (36292350125039098231294359463 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1741511 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_118 : rowCell 1 118 ≤ (2712552775907477308910616581 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19052389876067810961551081693 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36292350125039098231294359463 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_118_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_118_1
  · norm_num [gridPoint]

theorem exp_1_119_0 : expNegUpper (2787764029167408201473 / 39259633542353408000 : ℝ) ≤ (145169318492896524942115191327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1741511 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_119_1 : expNegUpper (348712902852676560489 / 4907454192794176000 : ℝ) ≤ (138173023111922668438408821421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1742183 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_119 : rowCell 1 119 ≤ (826463124608338046442074553 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (145169318492896524942115191327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (138173023111922668438408821421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_119_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_119_1
  · norm_num [gridPoint]

theorem exp_1_120_0 : expNegUpper (8777395971272454499329 / 123524733300252736000 : ℝ) ≤ (34543236528675459147237319721 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1742183 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_120_1 : expNegUpper (70268625776522084057911 / 988197866402021888000 : ℝ) ≤ (65713886475166904371869704939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108929 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_120 : rowCell 1 120 ≤ (19659526653618434250622262773 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34543236528675459147237319721 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (65713886475166904371869704939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_120_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_120_1
  · norm_num [gridPoint]

theorem exp_1_121_0 : expNegUpper (23582390878976879623013 / 331642577516987904000 : ℝ) ≤ (65713850350516028454474975317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108929 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_121_1 : expNegUpper (2359920404634832561477 / 33164257751698790400 : ℝ) ≤ (124930832829134140087803135001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (348711 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_121 : rowCell 1 121 ≤ (747755783485587503747833971 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (65713850350516028454474975317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (124930832829134140087803135001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_121_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_121_1
  · norm_num [gridPoint]

theorem exp_1_122_0 : expNegUpper (548293271705975849147 / 7705234130812774400 : ℝ) ≤ (124930765075770306447807450327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (348711 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_122_1 : expNegUpper (5486888434649433629697 / 77052341308127744000 : ℝ) ≤ (11867891417140340370366185051 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (872127 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_122 : rowCell 1 122 ≤ (4441059169693776394218838907 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (124930765075770306447807450327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11867891417140340370366185051 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_122_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_122_1
  · norm_num [gridPoint]

theorem exp_1_123_0 : expNegUpper (71812035817056947283909 / 1008455979766112768000 : ℝ) ≤ (23735770134407641751603240801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (872127 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_123_1 : expNegUpper (17966112075763427953057 / 252113994941528192000 : ℝ) ≤ (112668300454324031093117505589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (872481 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_123 : rowCell 1 123 ≤ (16870042111090424621019536357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23735770134407641751603240801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (112668300454324031093117505589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_123_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_123_1
  · norm_num [gridPoint]

theorem exp_1_124_0 : expNegUpper (9646521882014606171 / 135367248110976000 : ℝ) ≤ (112668240976935367808385735471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (872481 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_124_1 : expNegUpper (38614569647582318641 / 541468992443904000 : ℝ) ≤ (106894889349461459694064190283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (21821 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_124 : rowCell 1 124 ≤ (16010740727150759283628357819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (112668240976935367808385735471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (106894889349461459694064190283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_124_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_124_1
  · norm_num [gridPoint]

theorem exp_1_125_0 : expNegUpper (72888770208273304113947 / 1022075580204282368000 : ℝ) ≤ (53447416835897406055509915147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (21821 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_125_1 : expNegUpper (36471584500635345417033 / 511037790102141184000 : ℝ) ≤ (25338558360221954630358699289 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (873203 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_125 : rowCell 1 125 ≤ (379642726815701286912988757 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (53447416835897406055509915147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25338558360221954630358699289 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_125_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_125_1
  · norm_num [gridPoint]

theorem exp_1_126_0 : expNegUpper (36715807044443433753657 / 514459818940999936000 : ℝ) ≤ (10135418135028460301173711067 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (873203 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_126_1 : expNegUpper (14697402206310777737573 / 205783927576399974400 : ℝ) ≤ (96041579421763120020543457601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (87357 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_126 : rowCell 1 126 ≤ (14394276223251538600140060853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10135418135028460301173711067 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (96041579421763120020543457601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_126_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_126_1
  · norm_num [gridPoint]

theorem exp_1_127_0 : expNegUpper (4931830383285925546111 / 69052435591031500800 : ℝ) ≤ (96041530714969606544910551381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (87357 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_127_1 : expNegUpper (192796495240638249329 / 2697360765274668000 : ℝ) ≤ (45475952843682772659574004331 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (436971 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_127 : rowCell 1 127 ≤ (1704466173046724624614394133 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (96041530714969606544910551381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45475952843682772659574004331 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_127_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_127_1
  · norm_num [gridPoint]

theorem sum_1_96_2 : blockSum (rowCell 1) 96 2 ≤ (5241074464449680252470083509 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_96) (by simpa only [blockSum_one] using cell_1_97) (by norm_num)

theorem sum_1_98_2 : blockSum (rowCell 1) 98 2 ≤ (98026984898930617161473583997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_98) (by simpa only [blockSum_one] using cell_1_99) (by norm_num)

theorem sum_1_96_4 : blockSum (rowCell 1) 96 4 ≤ (202848474187924222210875254177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_96_2 sum_1_98_2 (by norm_num)

theorem sum_1_100_2 : blockSum (rowCell 1) 100 2 ≤ (45686778139645210903893820179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_100) (by simpa only [blockSum_one] using cell_1_101) (by norm_num)

theorem sum_1_102_2 : blockSum (rowCell 1) 102 2 ≤ (42449811026004500392879237673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_102) (by simpa only [blockSum_one] using cell_1_103) (by norm_num)

theorem sum_1_100_4 : blockSum (rowCell 1) 100 4 ≤ (22034147291412427824193264463 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_100_2 sum_1_102_2 (by norm_num)

theorem sum_1_96_8 : blockSum (rowCell 1) 96 8 ≤ (379121652519223644804421369881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_96_4 sum_1_100_4 (by norm_num)

theorem sum_1_104_2 : blockSum (rowCell 1) 104 2 ≤ (78637777400688546569371432479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_104) (by simpa only [blockSum_one] using cell_1_105) (by norm_num)

theorem sum_1_106_2 : blockSum (rowCell 1) 106 2 ≤ (36307471071566057985375143569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_106) (by simpa only [blockSum_one] using cell_1_107) (by norm_num)

theorem sum_1_104_4 : blockSum (rowCell 1) 104 4 ≤ (151252719543820662540121719617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_104_2 sum_1_106_2 (by norm_num)

theorem sum_1_108_2 : blockSum (rowCell 1) 108 2 ≤ (2674103861591187244860493933 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_108) (by simpa only [blockSum_one] using cell_1_109) (by norm_num)

theorem sum_1_110_2 : blockSum (rowCell 1) 110 2 ≤ (30683544091677169365297270003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_110) (by simpa only [blockSum_one] using cell_1_111) (by norm_num)

theorem sum_1_108_4 : blockSum (rowCell 1) 108 4 ≤ (128219684723134019852106888331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_108_2 sum_1_110_2 (by norm_num)

theorem sum_1_104_8 : blockSum (rowCell 1) 104 8 ≤ (69868101066738670598057151987 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_104_4 sum_1_108_4 (by norm_num)

theorem sum_1_96_16 : blockSum (rowCell 1) 96 16 ≤ (658594056786178327196649977829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_96_8 sum_1_104_8 (by norm_num)

theorem sum_1_112_2 : blockSum (rowCell 1) 112 2 ≤ (56169993836962649425263354957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_112) (by simpa only [blockSum_one] using cell_1_113) (by norm_num)

theorem sum_1_114_2 : blockSum (rowCell 1) 114 2 ≤ (5126852099927675113338217347 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_114) (by simpa only [blockSum_one] using cell_1_115) (by norm_num)

theorem sum_1_112_4 : blockSum (rowCell 1) 112 4 ≤ (107438514836239400558645528427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_112_2 sum_1_114_2 (by norm_num)

theorem sum_1_116_2 : blockSum (rowCell 1) 116 2 ≤ (46665935184283666147712798369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_116) (by simpa only [blockSum_one] using cell_1_117) (by norm_num)

theorem sum_1_118_2 : blockSum (rowCell 1) 118 2 ≤ (42362000322468269632336796473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_118) (by simpa only [blockSum_one] using cell_1_119) (by norm_num)

theorem sum_1_116_4 : blockSum (rowCell 1) 116 4 ≤ (44513967753375967890024797421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_116_2 sum_1_118_2 (by norm_num)

theorem sum_1_112_8 : blockSum (rowCell 1) 112 8 ≤ (196466450342991336338695123269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_112_4 sum_1_116_4 (by norm_num)

theorem sum_1_120_2 : blockSum (rowCell 1) 120 2 ≤ (2397088827547382615269882003 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_120) (by simpa only [blockSum_one] using cell_1_121) (by norm_num)

theorem sum_1_122_2 : blockSum (rowCell 1) 122 2 ≤ (6926855757973106039578978397 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_122) (by simpa only [blockSum_one] using cell_1_123) (by norm_num)

theorem sum_1_120_4 : blockSum (rowCell 1) 120 4 ≤ (72987700030623652042213004033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_120_2 sum_1_122_2 (by norm_num)

theorem sum_1_124_2 : blockSum (rowCell 1) 124 2 ≤ (31196449799778810760147908099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_124) (by simpa only [blockSum_one] using cell_1_125) (by norm_num)

theorem sum_1_126_2 : blockSum (rowCell 1) 126 2 ≤ (28030005607625335597055213917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_126) (by simpa only [blockSum_one] using cell_1_127) (by norm_num)

theorem sum_1_124_4 : blockSum (rowCell 1) 124 4 ≤ (1850826731481379573662597563 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_124_2 sum_1_126_2 (by norm_num)

theorem sum_1_120_8 : blockSum (rowCell 1) 120 8 ≤ (132214155438027798399416126049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_120_4 sum_1_124_4 (by norm_num)

theorem sum_1_112_16 : blockSum (rowCell 1) 112 16 ≤ (164340302890509567369055624659 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_112_8 sum_1_120_8 (by norm_num)

theorem sum_1_96_32 : blockSum (rowCell 1) 96 32 ≤ (987274662567197461934761227147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_96_16 sum_1_112_16 (by norm_num)

#print axioms sum_1_96_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
