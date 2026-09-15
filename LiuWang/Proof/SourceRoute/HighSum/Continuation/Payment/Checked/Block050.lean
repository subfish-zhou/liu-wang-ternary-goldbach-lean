import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_64_0 : expNegUpper (3369667902209342327 / 44984395697672000 : ℝ) ≤ (29412172952292592941930949 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112211 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_64_1 : expNegUpper (215593175513115317167 / 2879001324651008000 : ℝ) ≤ (3008973165886343178935698517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1795057 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_64 : rowCell 3 64 ≤ (54236654287349017611206071 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29412172952292592941930949 / 10000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3008973165886343178935698517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_64_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_64_1
  · norm_num [gridPoint]

theorem exp_3_65_0 : expNegUpper (48916656086353723812167 / 653226219073131008000 : ℝ) ≤ (3008968731229864495955081343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1795057 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_65_1 : expNegUpper (24451348878553645817703 / 326613109536565504000 : ℝ) ≤ (614791425894486446835821011 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1794757 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_65 : rowCell 3 65 ≤ (443572418891114452281103353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3008968731229864495955081343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (614791425894486446835821011 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_65_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_65_1
  · norm_num [gridPoint]

theorem exp_3_66_0 : expNegUpper (24656241314011959966807 / 329349989202770176000 : ℝ) ≤ (768488168545001961726735239 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1794757 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_66_1 : expNegUpper (9859864520334837527201 / 131739995681108070400 : ℝ) ≤ (783996028003400523681976761 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1794477 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_66 : rowCell 3 66 ≤ (226417084844659691382722527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (768488168545001961726735239 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (783996028003400523681976761 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_66_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_66_1
  · norm_num [gridPoint]

theorem exp_3_67_0 : expNegUpper (1104682386870305880049 / 14759923912082329600 : ℝ) ≤ (3135979641892978387155086573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1794477 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_67_1 : expNegUpper (1380509694902507808151 / 18449904890102912000 : ℝ) ≤ (3194875562357907756632822397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224277 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_67 : rowCell 3 67 ≤ (115412912342924296690133533 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3135979641892978387155086573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3194875562357907756632822397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_67_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_67_1
  · norm_num [gridPoint]

theorem exp_3_68_0 : expNegUpper (12527835105527976136751 / 167429002996906112000 : ℝ) ≤ (1597435541600336493605287303 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224277 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_68_1 : expNegUpper (50099786993894218736763 / 669716011987624448000 : ℝ) ≤ (812616176301659506301855849 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896987 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_68 : rowCell 3 68 ≤ (234999838211016758109504067 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1597435541600336493605287303 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (812616176301659506301855849 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_68_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_68_1
  · norm_num [gridPoint]

theorem exp_3_69_0 : expNegUpper (2020575666368279459883 / 27010331449491968000 : ℝ) ≤ (3250460222766168256219255437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896987 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_69_1 : expNegUpper (1010072930524492945901 / 13505165724745984000 : ℝ) ≤ (3302597301435394190907783351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793751 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_69 : rowCell 3 69 ≤ (11946371054434933337144119 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3250460222766168256219255437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3302597301435394190907783351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_69_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_69_1
  · norm_num [gridPoint]

theorem exp_3_70_0 : expNegUpper (2828881728488203176749 / 37823522155151616000 : ℝ) ≤ (3302592821405504195493475229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793751 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_70_1 : expNegUpper (5656659733980023721929 / 75647044310303232000 : ℝ) ≤ (41889153997531004034182671 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793547 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_70 : rowCell 3 70 ≤ (485195615253067785117782839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3302592821405504195493475229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41889153997531004034182671 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_70_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_70_1
  · norm_num [gridPoint]

theorem exp_3_71_0 : expNegUpper (51327788775192563329289 / 686411349653914112000 : ℝ) ≤ (1675563923898447352992442181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793547 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_71_1 : expNegUpper (1282966755625489101819 / 17160283741347852800 : ℝ) ≤ (679188503361170780017633271 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_71 : rowCell 3 71 ≤ (123000608201965781534199407 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1675563923898447352992442181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (679188503361170780017633271 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_71_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_71_1
  · norm_num [gridPoint]

theorem exp_3_72_0 : expNegUpper (1293453865969008791739 / 17300553470521356800 : ℝ) ≤ (424492257292325399355234581 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_72_1 : expNegUpper (51729854376161345750311 / 692022138820854272000 : ℝ) ≤ (3436914922336563264140564897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793193 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_72 : rowCell 3 72 ≤ (49825777824218296353386513 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (424492257292325399355234581 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3436914922336563264140564897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_72_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_72_1
  · norm_num [gridPoint]

theorem exp_3_73_0 : expNegUpper (5794553188425518770151 / 77517307365949952000 : ℝ) ≤ (1718455241401699403906013881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793193 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_73_1 : expNegUpper (2896861113976900292171 / 38758653682974976000 : ℝ) ≤ (1736975614828427304739038791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793043 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_73 : rowCell 3 73 ≤ (503946245049921467697724079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1718455241401699403906013881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1736975614828427304739038791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_73_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_73_1
  · norm_num [gridPoint]

theorem exp_3_74_0 : expNegUpper (1682120670039653179 / 22505991426304000 : ℝ) ≤ (694789362863552942026262729 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793043 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_74_1 : expNegUpper (3363815503592114517 / 45011982852608000 : ℝ) ≤ (1753484044547715216112556419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (179291 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_74 : rowCell 3 74 ≤ (50905458667262372507314133 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (694789362863552942026262729 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1753484044547715216112556419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_74_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_74_1
  · norm_num [gridPoint]

theorem exp_3_75_0 : expNegUpper (52984041359827477135797 / 708991536156205568000 : ℝ) ≤ (3506963703058328821236493197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (179291 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_75_1 : expNegUpper (13244553986156936171629 / 177247884039051392000 : ℝ) ≤ (3535897305691789601981562507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (358559 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_75 : rowCell 3 75 ≤ (256785876164248092177790741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3506963703058328821236493197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3535897305691789601981562507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_75_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_75_1
  · norm_num [gridPoint]

theorem exp_3_76_0 : expNegUpper (1483452776428701709349 / 19852602181837952000 : ℝ) ≤ (141435718155897422917810491 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (358559 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_76_1 : expNegUpper (1186651247709460401407 / 15882081745470361600 : ℝ) ≤ (356068594182801041578995569 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792697 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_76 : rowCell 3 76 ≤ (517488908908901149828952599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (141435718155897422917810491 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (356068594182801041578995569 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_76_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_76_1
  · norm_num [gridPoint]

theorem exp_3_77_0 : expNegUpper (10765411341179032355023 / 144083731848376422400 : ℝ) ≤ (3560681629036208484435145901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792697 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_77_1 : expNegUpper (26911448921429678093793 / 360209329620941056000 : ℝ) ≤ (3581296326652384120103000561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224077 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_77 : rowCell 3 77 ≤ (26039972457481586834641989 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3560681629036208484435145901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3581296326652384120103000561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_77_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_77_1
  · norm_num [gridPoint]

theorem exp_3_78_0 : expNegUpper (27126160807775912290257 / 363083239121676544000 : ℝ) ≤ (111915376794671863128255991 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224077 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_78_1 : expNegUpper (54249001024767305788393 / 726166478243353088000 : ℝ) ≤ (1798852987409225991756806479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224069 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_78 : rowCell 3 78 ≤ (65437373299070653588103649 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (111915376794671863128255991 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1798852987409225991756806479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_78_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_78_1
  · norm_num [gridPoint]

theorem exp_3_79_0 : expNegUpper (243022687434408429697 / 3253053935780352000 : ℝ) ≤ (112428179797695870064567717 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224069 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_79_1 : expNegUpper (15188229356941170443 / 203315870986272000 : ℝ) ≤ (721981483545923970662228467 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (358501 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_79 : rowCell 3 79 ≤ (525585336354344130958514709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (112428179797695870064567717 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (721981483545923970662228467 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_79_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_79_1
  · norm_num [gridPoint]

theorem exp_3_80_0 : expNegUpper (3444400991862751550507 / 46108164447722528000 : ℝ) ≤ (1804951624257774481526865253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (358501 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_80_1 : expNegUpper (55108781815860726335871 / 737730631163560448000 : ℝ) ≤ (3617907951088910735319983413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_80 : rowCell 3 80 ≤ (527058486411781845837171477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1804951624257774481526865253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3617907951088910735319983413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_80_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_80_1
  · norm_num [gridPoint]

theorem exp_3_81_0 : expNegUpper (1791718232228285667369 / 23985385970396672000 : ℝ) ≤ (1808951918938783970433806903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_81_1 : expNegUpper (179169288418462873357 / 2398538597039667200 : ℝ) ≤ (724345860620356482156937187 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792459 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_81 : rowCell 3 81 ≤ (26396027649905716313878363 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1808951918938783970433806903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (724345860620356482156937187 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_81_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_81_1
  · norm_num [gridPoint]

theorem exp_3_82_0 : expNegUpper (621985140587767067243 / 8326512636742092800 : ℝ) ≤ (3621725249587910234073801331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792459 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_82_1 : expNegUpper (6219858717657239282029 / 83265126367420928000 : ℝ) ≤ (3621407228164416353962688287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (89623 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_82 : rowCell 3 82 ≤ (264087863889767567702769881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3621725249587910234073801331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3621407228164416353962688287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_82_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_82_1
  · norm_num [gridPoint]

theorem exp_3_83_0 : expNegUpper (56416618223609212627469 / 755248147837035008000 : ℝ) ≤ (3621403237807149257898214669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (89623 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_83_1 : expNegUpper (14104384738943590364427 / 188812036959258752000 : ℝ) ≤ (1808495515644255228768542169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792477 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_83 : rowCell 3 83 ≤ (52783021334730664708131759 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3621403237807149257898214669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1808495515644255228768542169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_83_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_83_1
  · norm_num [gridPoint]

theorem exp_3_84_0 : expNegUpper (568571419035460321443 / 7611329966730368000 : ℝ) ≤ (3616987107306953746905382067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792477 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_84_1 : expNegUpper (2274356835705590449123 / 30445319866921472000 : ℝ) ≤ (3608543028865287843576579219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (179251 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_84 : rowCell 3 84 ≤ (263446074608455787013124283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3616987107306953746905382067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3608543028865287843576579219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_84_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_84_1
  · norm_num [gridPoint]

theorem exp_3_85_0 : expNegUpper (6366693742783126814603 / 85226742646088192000 : ℝ) ≤ (144341566969415170819748299 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (179251 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_85_1 : expNegUpper (3183493570102777754357 / 42613371323044096000 : ℝ) ≤ (3596137951655906943600145647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896279 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_85 : rowCell 3 85 ≤ (105074305794419576736836349 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (144341566969415170819748299 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3596137951655906943600145647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_85_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_85_1
  · norm_num [gridPoint]

theorem exp_3_86_0 : expNegUpper (28872966780227093458957 / 386485604631152896000 : ℝ) ≤ (1798067084554260878277419587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896279 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_86_1 : expNegUpper (2309977562229748929513 / 30918848370492231680 : ℝ) ≤ (1789931148056624299366016583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896311 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_86 : rowCell 3 86 ≤ (52328010942829571699182231 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1798067084554260878277419587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1789931148056624299366016583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_86_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_86_1
  · norm_num [gridPoint]

theorem exp_3_87_0 : expNegUpper (2327768860884112625313 / 31156982920622919680 : ℝ) ≤ (894964647033375543632206651 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896311 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_87_1 : expNegUpper (7274824408332447366917 / 97365571626946624000 : ℝ) ≤ (71196272605848358108767133 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_87 : rowCell 3 87 ≤ (520631312716876834268778849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (894964647033375543632206651 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (71196272605848358108767133 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_87_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_87_1
  · norm_num [gridPoint]

theorem exp_3_88_0 : expNegUpper (814515521699064919517 / 10901399653813824000 : ℝ) ≤ (3559809999120114247749327117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_88_1 : expNegUpper (6516706987437357044447 / 87211197230510592000 : ℝ) ≤ (3536099860696153020976030651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896397 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_88 : rowCell 3 88 ≤ (258720061104658443956538667 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3559809999120114247749327117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3536099860696153020976030651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_88_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_88_1
  · norm_num [gridPoint]

theorem exp_3_89_0 : expNegUpper (2363945266939296374567 / 31635992617574912000 : ℝ) ≤ (1768048154163661152348573629 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896397 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_89_1 : expNegUpper (1182095038178245467219 / 15817996308787456000 : ℝ) ≤ (3508838466429201971243163859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792903 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_89 : rowCell 3 89 ≤ (128430743302208111379086663 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1768048154163661152348573629 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3508838466429201971243163859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_89_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_89_1
  · norm_num [gridPoint]

theorem exp_3_90_0 : expNegUpper (29777386923945333919371 / 398460847054952704000 : ℝ) ≤ (3508834994618665957146234071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792903 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_90_1 : expNegUpper (59561772324926405547181 / 796921694109905408000 : ℝ) ≤ (3478155707005664127186813169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896513 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_90 : rowCell 3 90 ≤ (127374409834226160089656487 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3508834994618665957146234071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3478155707005664127186813169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_90_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_90_1
  · norm_num [gridPoint]

theorem exp_3_91_0 : expNegUpper (6668172675321788484221 / 89218490120688128000 : ℝ) ≤ (3478152317270564657605940631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896513 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_91_1 : expNegUpper (333452411818429203821 / 4460924506034406400 : ℝ) ≤ (688837162013761253375506183 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793163 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_91 : rowCell 3 91 ≤ (504783115533748209279399711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3478152317270564657605940631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (688837162013761253375506183 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_91_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_91_1
  · norm_num [gridPoint]

theorem exp_3_92_0 : expNegUpper (3023749117791867082549 / 40451698318411801600 : ℝ) ≤ (3444182503693029164609036681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793163 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_92_1 : expNegUpper (60483747308423473511811 / 809033966368236032000 : ℝ) ≤ (681414029029570005759966411 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (358663 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_92 : rowCell 3 92 ≤ (499599498575778603760775037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3444182503693029164609036681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (681414029029570005759966411 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_92_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_92_1
  · norm_num [gridPoint]

theorem exp_3_93_0 : expNegUpper (60939068674053050446779 / 815124359956034048000 : ℝ) ≤ (53235420674801164625975077 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (358663 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_93_1 : expNegUpper (30474360930291851374169 / 407562179978017024000 : ℝ) ≤ (3366956389394896254909688559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793481 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_93 : rowCell 3 93 ≤ (7718247906094715501902423 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (53235420674801164625975077 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3366956389394896254909688559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_93_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_93_1
  · norm_num [gridPoint]

theorem exp_3_94_0 : expNegUpper (136457384499737487721 / 1824972426332416000 : ℝ) ≤ (3366953252683398639661162383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793481 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_94_1 : expNegUpper (272961634560607071673 / 3649944852664832000 : ℝ) ≤ (1661998845510975367561828373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793661 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_94 : rowCell 3 94 ≤ (1524719231925726755262931 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3366953252683398639661162383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1661998845510975367561828373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_94_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_94_1
  · norm_num [gridPoint]

theorem exp_3_95_0 : expNegUpper (61875255400662445463057 / 827373662048895488000 : ℝ) ≤ (10387483250556530706451171 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793661 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_95_1 : expNegUpper (1933959220231899542973 / 25855426939027984000 : ℝ) ≤ (3278351835897564392226447043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896927 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_95 : rowCell 3 95 ≤ (481449036831098804818353469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10387483250556530706451171 / 3125000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3278351835897564392226447043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_95_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_95_1
  · norm_num [gridPoint]

theorem sum_3_64_2 : blockSum (rowCell 3) 64 2 ≤ (877465653189906593170751921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_64) (by simpa only [blockSum_one] using cell_3_65) (by norm_num)

theorem sum_3_66_2 : blockSum (rowCell 3) 66 2 ≤ (457242909530508284762989593 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_66) (by simpa only [blockSum_one] using cell_3_67) (by norm_num)

theorem sum_3_64_4 : blockSum (rowCell 3) 64 4 ≤ (1791951472250923162696731107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_64_2 sum_3_66_2 (by norm_num)

theorem sum_3_68_2 : blockSum (rowCell 3) 68 2 ≤ (473927259299715424852386447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_68) (by simpa only [blockSum_one] using cell_3_69) (by norm_num)

theorem sum_3_70_2 : blockSum (rowCell 3) 70 2 ≤ (977198048060930911254580467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_70) (by simpa only [blockSum_one] using cell_3_71) (by norm_num)

theorem sum_3_68_4 : blockSum (rowCell 3) 68 4 ≤ (1925052566660361760959353361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_68_2 sum_3_70_2 (by norm_num)

theorem sum_3_64_8 : blockSum (rowCell 3) 64 8 ≤ (929251009727821230914021117 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_64_4 sum_3_68_4 (by norm_num)

theorem sum_3_72_2 : blockSum (rowCell 3) 72 2 ≤ (1002204023292104431231589209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_72) (by simpa only [blockSum_one] using cell_3_73) (by norm_num)

theorem sum_3_74_2 : blockSum (rowCell 3) 74 2 ≤ (255656584750279977357180703 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_74) (by simpa only [blockSum_one] using cell_3_75) (by norm_num)

theorem sum_3_72_4 : blockSum (rowCell 3) 72 4 ≤ (2024830362293224340660312021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_72_2 sum_3_74_2 (by norm_num)

theorem sum_3_76_2 : blockSum (rowCell 3) 76 2 ≤ (1038288358058532886521792379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_76) (by simpa only [blockSum_one] using cell_3_77) (by norm_num)

theorem sum_3_78_2 : blockSum (rowCell 3) 78 2 ≤ (1049084322746909359663343901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_78) (by simpa only [blockSum_one] using cell_3_79) (by norm_num)

theorem sum_3_76_4 : blockSum (rowCell 3) 76 4 ≤ (52184317020136056154628407 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_76_2 sum_3_78_2 (by norm_num)

theorem sum_3_72_8 : blockSum (rowCell 3) 72 8 ≤ (4112203043098666586845448301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_72_4 sum_3_76_4 (by norm_num)

theorem sum_3_64_16 : blockSum (rowCell 3) 64 16 ≤ (7829207082009951510501532769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_64_8 sum_3_72_8 (by norm_num)

theorem sum_3_80_2 : blockSum (rowCell 3) 80 2 ≤ (1054979039409896172114738737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_80) (by simpa only [blockSum_one] using cell_3_81) (by norm_num)

theorem sum_3_82_2 : blockSum (rowCell 3) 82 2 ≤ (132000742640855222810857169 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_82) (by simpa only [blockSum_one] using cell_3_83) (by norm_num)

theorem sum_3_80_4 : blockSum (rowCell 3) 80 4 ≤ (2110984980536737954601596089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_80_2 sum_3_82_2 (by norm_num)

theorem sum_3_84_2 : blockSum (rowCell 3) 84 2 ≤ (1052263678189009457710430311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_84) (by simpa only [blockSum_one] using cell_3_85) (by norm_num)

theorem sum_3_86_2 : blockSum (rowCell 3) 86 2 ≤ (1043911422145172551260601159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_86) (by simpa only [blockSum_one] using cell_3_87) (by norm_num)

theorem sum_3_84_4 : blockSum (rowCell 3) 84 4 ≤ (209617510033418200897103147 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_84_2 sum_3_86_2 (by norm_num)

theorem sum_3_80_8 : blockSum (rowCell 3) 80 8 ≤ (4207160080870919963572627559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_80_4 sum_3_84_4 (by norm_num)

theorem sum_3_88_2 : blockSum (rowCell 3) 88 2 ≤ (515581547709074666714711993 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_88) (by simpa only [blockSum_one] using cell_3_89) (by norm_num)

theorem sum_3_90_2 : blockSum (rowCell 3) 90 2 ≤ (1014280754870652849638025659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_90) (by simpa only [blockSum_one] using cell_3_91) (by norm_num)

theorem sum_3_88_4 : blockSum (rowCell 3) 88 4 ≤ (409088770057760436613489929 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_88_2 sum_3_90_2 (by norm_num)

theorem sum_3_92_2 : blockSum (rowCell 3) 92 2 ≤ (993567364565840395882530109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_92) (by simpa only [blockSum_one] using cell_3_93) (by norm_num)

theorem sum_3_94_2 : blockSum (rowCell 3) 94 2 ≤ (969359191047331366502491389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_94) (by simpa only [blockSum_one] using cell_3_95) (by norm_num)

theorem sum_3_92_4 : blockSum (rowCell 3) 92 4 ≤ (981463277806585881192510749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_92_2 sum_3_94_2 (by norm_num)

theorem sum_3_88_8 : blockSum (rowCell 3) 88 8 ≤ (4008370405901973945452471143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_88_4 sum_3_92_4 (by norm_num)

theorem sum_3_80_16 : blockSum (rowCell 3) 80 16 ≤ (4107765243386446954512549351 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_80_8 sum_3_88_8 (by norm_num)

theorem sum_3_64_32 : blockSum (rowCell 3) 64 32 ≤ (16044737568782845419526631471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_64_16 sum_3_80_16 (by norm_num)

#print axioms sum_3_64_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
