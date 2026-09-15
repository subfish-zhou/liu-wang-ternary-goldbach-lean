import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_96_0 : expNegUpper (1948355493554169535677 / 26047892829811216000 : ℝ) ≤ (3278348871331876545213889479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896927 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_96_1 : expNegUpper (12471942733354986444707 / 166706514110791782400 : ℝ) ≤ (3230180422469622145201209639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897031 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_96 : rowCell 3 96 ≤ (237303901805396342144524349 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3278348871331876545213889479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3230180422469622145201209639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_96_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_96_1
  · norm_num [gridPoint]

theorem exp_3_97_0 : expNegUpper (1396048759920743449763 / 18660318163661721600 : ℝ) ≤ (3230177544392453453023735943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897031 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_97_1 : expNegUpper (3490857423696537688927 / 46650795409154304000 : ℝ) ≤ (1589824024930036311024784931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1794283 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_97 : rowCell 3 97 ≤ (467410241160576537648241033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3230177544392453453023735943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1589824024930036311024784931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_97_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_97_1
  · norm_num [gridPoint]

theorem exp_3_98_0 : expNegUpper (31649860300550591242567 / 422959451240675584000 : ℝ) ≤ (3179645258289877014410676823 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1794283 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_98_1 : expNegUpper (63313864919047670635653 / 845918902481351168000 : ℝ) ≤ (1563460761816815856088912001 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1794517 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_98 : rowCell 3 98 ≤ (18395220631758215629808201 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3179645258289877014410676823 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1563460761816815856088912001 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_98_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_98_1
  · norm_num [gridPoint]

theorem exp_3_99_0 : expNegUpper (102047944000120405773 / 1363434121445888000 : ℝ) ≤ (312691881840566490922960969 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1794517 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_99_1 : expNegUpper (25518007014657422263 / 340858530361472000 : ℝ) ≤ (3072169083380390795063763623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (358953 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_99 : rowCell 3 99 ≤ (452043059291275942866494609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (312691881840566490922960969 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3072169083380390795063763623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_99_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_99_1
  · norm_num [gridPoint]

theorem exp_3_100_0 : expNegUpper (1785081594047064314927 / 23844349656437888000 : ℝ) ≤ (30721664641557318304870377 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (358953 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_100_1 : expNegUpper (7142100163518220021699 / 95377398625751552000 : ℝ) ≤ (753889913969092116097511971 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897513 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_100 : rowCell 3 100 ≤ (2774515363213604499015911 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30721664641557318304870377 / 10000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (753889913969092116097511971 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_100_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_100_1
  · norm_num [gridPoint]

theorem exp_3_101_0 : expNegUpper (64748647750297014401939 / 864669687665603072000 : ℝ) ≤ (3015557122151202636714759843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897513 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_101_1 : expNegUpper (6476552671644759097809 / 86466968766560307200 : ℝ) ≤ (369657767150093883405830443 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (17953 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_101 : rowCell 3 101 ≤ (217771673298373894056885719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3015557122151202636714759843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (369657767150093883405830443 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_101_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_101_1
  · norm_num [gridPoint]

theorem exp_3_102_0 : expNegUpper (6523710608622199753089 / 87096562600519731200 : ℝ) ≤ (46207182629935166633361613 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (17953 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_102_1 : expNegUpper (65254903263333034734961 / 870965626005197312000 : ℝ) ≤ (1448722353399028921795285733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897793 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_102 : rowCell 3 102 ≤ (85386060915537238712940477 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (46207182629935166633361613 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1448722353399028921795285733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_102_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_102_1
  · norm_num [gridPoint]

theorem exp_3_103_0 : expNegUpper (7303146931756434605921 / 97476044738949632000 : ℝ) ≤ (579488468389679954159317893 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897793 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_103_1 : expNegUpper (913153348675818863819 / 12184505592368704000 : ℝ) ≤ (354534272010211341063588387 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897943 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_103 : rowCell 3 103 ≤ (83621551976137673373755039 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (579488468389679954159317893 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (354534272010211341063588387 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_103_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_103_1
  · norm_num [gridPoint]

theorem exp_3_104_0 : expNegUpper (331111533206967014491 / 4418130088008256000 : ℝ) ≤ (709067973581538300898978527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897943 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_104_1 : expNegUpper (2649678009310560323487 / 35345040704066048000 : ℝ) ≤ (2773915373785974065467503833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (898099 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_104 : rowCell 3 104 ≤ (51137486999170001868680967 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (709067973581538300898978527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2773915373785974065467503833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_104_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_104_1
  · norm_num [gridPoint]

theorem exp_3_105_0 : expNegUpper (66719068845317118594687 / 889990470858510848000 : ℝ) ≤ (1386956587028528897869547193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (898099 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_105_1 : expNegUpper (33369820319993415570323 / 444995235429255424000 : ℝ) ≤ (2710530569890258181561831827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (898261 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_105 : rowCell 3 105 ≤ (49991320654820560466435237 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1386956587028528897869547193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2710530569890258181561831827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_105_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_105_1
  · norm_num [gridPoint]

theorem exp_3_106_0 : expNegUpper (3734367721662094737323 / 49798764578951424000 : ℝ) ≤ (1355264225501890421593257359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (898261 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_106_1 : expNegUpper (1494224940414801646321 / 19919505831580569600 : ℝ) ≤ (2646278939564054618757265781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1796859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_106 : rowCell 3 106 ≤ (78124641535369305034922663 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1355264225501890421593257359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2646278939564054618757265781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_106_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_106_1
  · norm_num [gridPoint]

theorem exp_3_107_0 : expNegUpper (13544193413506761931729 / 180557578457899110400 : ℝ) ≤ (264627690022877099960779881 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1796859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_107_1 : expNegUpper (16935851315285095911909 / 225696973072373888000 : ℝ) ≤ (1290658034109639471984690067 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224651 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_107 : rowCell 3 107 ≤ (11912524247649668497828721 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (264627690022877099960779881 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1290658034109639471984690067 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_107_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_107_1
  · norm_num [gridPoint]

theorem exp_3_108_0 : expNegUpper (17056530767626019621061 / 227305215115905152000 : ℝ) ≤ (2581314107046382734166719003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224651 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_108_1 : expNegUpper (68249499459748406559283 / 909220860463620608000 : ℝ) ≤ (2515793498406969377566968473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1797569 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_108 : rowCell 3 108 ≤ (371685666022272710483658377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2581314107046382734166719003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2515793498406969377566968473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_108_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_108_1
  · norm_num [gridPoint]

theorem exp_3_109_0 : expNegUpper (305484875516298482123 / 4069674075304448000 : ℝ) ≤ (2515791613919436267425249863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1797569 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_109_1 : expNegUpper (152796477570730643441 / 2034837037652224000 : ℝ) ≤ (1224929159481737139096892909 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (898971 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_109 : rowCell 3 109 ≤ (90524913607983352869120853 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2515791613919436267425249863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1224929159481737139096892909 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_109_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_109_1
  · norm_num [gridPoint]

theorem exp_3_110_0 : expNegUpper (34622449410930848184001 / 461077655864568064000 : ℝ) ≤ (1224928254802604857981416293 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (898971 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_110_1 : expNegUpper (69270161594720179344201 / 922155311729136128000 : ℝ) ≤ (476730559299377433782427071 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1798327 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_110 : rowCell 3 110 ≤ (88115960301745526486938167 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1224928254802604857981416293 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (476730559299377433782427071 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_110_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_110_1
  · norm_num [gridPoint]

theorem exp_3_111_0 : expNegUpper (69758538554926338884289 / 928656794820526592000 : ℝ) ≤ (148978191290102863112903133 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1798327 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_111_1 : expNegUpper (174461873789403056689 / 2321641987051316480 : ℝ) ≤ (2317314049009968276134187817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1798723 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_111 : rowCell 3 111 ≤ (342798599319136401768821657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (148978191290102863112903133 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2317314049009968276134187817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_111_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_111_1
  · norm_num [gridPoint]

theorem exp_3_112_0 : expNegUpper (629704535687273591 / 8379759105893120 : ℝ) ≤ (2317312384970015791311356701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1798723 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_112_1 : expNegUpper (251979170832582674809 / 3351903642357248000 : ℝ) ≤ (2250973761182134315681739369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1799131 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_112 : rowCell 3 112 ≤ (166561765048499609687149159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2317312384970015791311356701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2250973761182134315681739369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_112_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_112_1
  · norm_num [gridPoint]

theorem exp_3_113_0 : expNegUpper (70794371697520524710999 / 941728275920572928000 : ℝ) ≤ (2250972167216625799523619369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1799131 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_113_1 : expNegUpper (35411244513323428430799 / 470864137960286464000 : ℝ) ≤ (546189485145309219298576523 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1799551 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_113 : rowCell 3 113 ≤ (323457424686888871028519739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2250972167216625799523619369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (546189485145309219298576523 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_113_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_113_1
  · norm_num [gridPoint]

theorem exp_3_114_0 : expNegUpper (1426331701834547229591 / 18965965478584576000 : ℝ) ≤ (1092378207452144785320199469 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1799551 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_114_1 : expNegUpper (2853826424046749646973 / 37931930957169152000 : ℝ) ≤ (2118786713846417107930449653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (899991 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_114 : rowCell 3 114 ≤ (19613639463314454247776113 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1092378207452144785320199469 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2118786713846417107930449653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_114_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_114_1
  · norm_num [gridPoint]

theorem exp_3_115_0 : expNegUpper (7982408484184321087813 / 106099012249293312000 : ℝ) ≤ (2118785254634858524637108651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (899991 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_115_1 : expNegUpper (1996436482727635164971 / 26524753062323328000 : ℝ) ≤ (513293540419172222063629761 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72017 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_115 : rowCell 3 115 ≤ (152111514441113064876968131 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2118785254634858524637108651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (513293540419172222063629761 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_115_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_115_1
  · norm_num [gridPoint]

theorem exp_3_116_0 : expNegUpper (18092413871913439093091 / 240376696215951488000 : ℝ) ≤ (2053172767077464671613887489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72017 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_116_1 : expNegUpper (14480131470012775576911 / 192301356972761190400 : ℝ) ≤ (1988028191276185967929135657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (900439 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_116 : rowCell 3 116 ≤ (294688004649634225493473713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2053172767077464671613887489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1988028191276185967929135657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_116_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_116_1
  · norm_num [gridPoint]

theorem exp_3_117_0 : expNegUpper (14580106494810121590951 / 193629059557945446400 : ℝ) ≤ (124251678713338431606134783 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (900439 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_117_1 : expNegUpper (36466251254557211870093 / 484072648894863616000 : ℝ) ≤ (1923450444746104483945403189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1801343 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_117 : rowCell 3 117 ≤ (35653554904650326213876251 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (124251678713338431606134783 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1923450444746104483945403189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_117_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_117_1
  · norm_num [gridPoint]

theorem exp_3_118_0 : expNegUpper (4079684294954893959253 / 54155924945633536000 : ℝ) ≤ (480862293431942762786648841 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1801343 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_118_1 : expNegUpper (8163028760853905581657 / 108311849891267072000 : ℝ) ≤ (1859536241774966997694650057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1801819 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_118 : rowCell 3 118 ≤ (68964673818604724815679843 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (480862293431942762786648841 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1859536241774966997694650057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_118_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_118_1
  · norm_num [gridPoint]

theorem exp_3_119_0 : expNegUpper (2958840799416194121473 / 39259633542353408000 : ℝ) ≤ (74381401187969783108087163 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1801819 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_119_1 : expNegUpper (370024681790573520489 / 4907454192794176000 : ℝ) ≤ (898187277431213266575568429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (360461 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_119 : rowCell 3 119 ≤ (33324026439063054628726557 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (74381401187969783108087163 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (898187277431213266575568429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_119_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_119_1
  · norm_num [gridPoint]

theorem exp_3_120_0 : expNegUpper (9313831311879942499329 / 123524733300252736000 : ℝ) ≤ (898186699911813536946975211 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (360461 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_120_1 : expNegUpper (74545545032741732057911 / 988197866402021888000 : ℝ) ≤ (108378000951046973274633327 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (901401 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_120 : rowCell 3 120 ≤ (51488300289546897245503417 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (898186699911813536946975211 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (108378000951046973274633327 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_120_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_120_1
  · norm_num [gridPoint]

theorem exp_3_121_0 : expNegUpper (8339246536714533207671 / 110547525838995968000 : ℝ) ≤ (867023457655449931980305189 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (901401 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_121_1 : expNegUpper (834323276265609787159 / 11054752583899596800 : ℝ) ≤ (418158236847893152030645583 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (180331 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_121 : rowCell 3 121 ≤ (4968363125544068788338361 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (867023457655449931980305189 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (418158236847893152030645583 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_121_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_121_1
  · norm_num [gridPoint]

theorem exp_3_122_0 : expNegUpper (7559873498391727638911 / 100168043700566067200 : ℝ) ≤ (418157975180401404075273609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (180331 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_122_1 : expNegUpper (75635595843942797186061 / 1001680437005660672000 : ℝ) ≤ (806099715336244945468296899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1803829 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_122 : rowCell 3 122 ≤ (23953285190090674377045451 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (418157975180401404075273609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (806099715336244945468296899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_122_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_122_1
  · norm_num [gridPoint]

theorem exp_3_123_0 : expNegUpper (76147208947837619283909 / 1008455979766112768000 : ℝ) ≤ (806099217676541823388768057 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1803829 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_123_1 : expNegUpper (19046264491298531953057 / 252113994941528192000 : ℝ) ≤ (48525355787115563949005427 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902179 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_123 : rowCell 3 123 ≤ (230795359677344443172737593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (806099217676541823388768057 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (48525355787115563949005427 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_123_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_123_1
  · norm_num [gridPoint]

theorem exp_3_124_0 : expNegUpper (3408828920645798857 / 45122416036992000 : ℝ) ≤ (310562087869945294958548041 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902179 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_124_1 : expNegUpper (13642220661332892347 / 180489664147968000 : ℝ) ≤ (298905336139549756351475359 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804897 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_124 : rowCell 3 124 ≤ (222214560635805688361185339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (310562087869945294958548041 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (298905336139549756351475359 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_124_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_124_1
  · norm_num [gridPoint]

theorem exp_3_125_0 : expNegUpper (77253070276334488113947 / 1022075580204282368000 : ℝ) ≤ (149452578249238055417784611 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804897 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_125_1 : expNegUpper (38646452800345809417033 / 511037790102141184000 : ℝ) ≤ (1437397266016754061613762721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1805447 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_125 : rowCell 3 125 ≤ (53449615711724997777288873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (149452578249238055417784611 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1437397266016754061613762721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_125_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_125_1
  · norm_num [gridPoint]

theorem exp_3_126_0 : expNegUpper (38905238812794153753657 / 514459818940999936000 : ℝ) ≤ (143739641361919508144510169 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1805447 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_126_1 : expNegUpper (15570262219923014537573 / 205783927576399974400 : ℝ) ≤ (1381469317029486319440081749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806007 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_126 : rowCell 3 126 ≤ (41110844330716345485448737 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (143739641361919508144510169 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1381469317029486319440081749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_126_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_126_1
  · norm_num [gridPoint]

theorem exp_3_127_0 : expNegUpper (1741575172325123982037 / 23017478530343833600 : ℝ) ≤ (690734254321188399728072857 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806007 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_127_1 : expNegUpper (68066595233599416443 / 899120255091556000 : ℝ) ≤ (66339170064734242270448313 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806577 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_127 : rowCell 3 127 ≤ (49372040616921467305596381 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (690734254321188399728072857 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (66339170064734242270448313 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_127_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_127_1
  · norm_num [gridPoint]

theorem sum_3_96_2 : blockSum (rowCell 3) 96 2 ≤ (942018044771369221937289731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_96) (by simpa only [blockSum_one] using cell_3_97) (by norm_num)

theorem sum_3_98_2 : blockSum (rowCell 3) 98 2 ≤ (455961787542615666805849817 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_98) (by simpa only [blockSum_one] using cell_3_99) (by norm_num)

theorem sum_3_96_4 : blockSum (rowCell 3) 96 4 ≤ (370788323971320111109797873 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_96_2 sum_3_98_2 (by norm_num)

theorem sum_3_100_2 : blockSum (rowCell 3) 100 2 ≤ (439732902355462253978158599 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_100) (by simpa only [blockSum_one] using cell_3_101) (by norm_num)

theorem sum_3_102_2 : blockSum (rowCell 3) 102 2 ≤ (42251903222918728021673879 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_102) (by simpa only [blockSum_one] using cell_3_103) (by norm_num)

theorem sum_3_100_4 : blockSum (rowCell 3) 100 4 ≤ (862251934584649534194897389 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_100_2 sum_3_102_2 (by norm_num)

theorem sum_3_96_8 : blockSum (rowCell 3) 96 8 ≤ (3578445489025899623938784143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_96_4 sum_3_100_4 (by norm_num)

theorem sum_3_104_2 : blockSum (rowCell 3) 104 2 ≤ (25282201913497640583779051 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_104) (by simpa only [blockSum_one] using cell_3_105) (by norm_num)

theorem sum_3_106_2 : blockSum (rowCell 3) 106 2 ≤ (771823983601635917105132387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_106) (by simpa only [blockSum_one] using cell_3_107) (by norm_num)

theorem sum_3_104_4 : blockSum (rowCell 3) 104 4 ≤ (1580854444833560415786062019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_104_2 sum_3_106_2 (by norm_num)

theorem sum_3_108_2 : blockSum (rowCell 3) 108 2 ≤ (733785320454206121960141789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_108) (by simpa only [blockSum_one] using cell_3_109) (by norm_num)

theorem sum_3_110_2 : blockSum (rowCell 3) 110 2 ≤ (27810497621044740308662973 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_110) (by simpa only [blockSum_one] using cell_3_111) (by norm_num)

theorem sum_3_108_4 : blockSum (rowCell 3) 108 4 ≤ (714523880490162314838358057 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_108_2 sum_3_110_2 (by norm_num)

theorem sum_3_104_8 : blockSum (rowCell 3) 104 8 ≤ (3009902205813885045462778133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_104_4 sum_3_108_4 (by norm_num)

theorem sum_3_96_16 : blockSum (rowCell 3) 96 16 ≤ (1647086923709946167350390569 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_96_8 sum_3_104_8 (by norm_num)

theorem sum_3_112_2 : blockSum (rowCell 3) 112 2 ≤ (656580954783888090402818057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_112) (by simpa only [blockSum_one] using cell_3_113) (by norm_num)

theorem sum_3_114_2 : blockSum (rowCell 3) 114 2 ≤ (61804126029525739771835407 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_114) (by simpa only [blockSum_one] using cell_3_115) (by norm_num)

theorem sum_3_112_4 : blockSum (rowCell 3) 112 4 ≤ (1274622215079145488121172127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_112_2 sum_3_114_2 (by norm_num)

theorem sum_3_116_2 : blockSum (rowCell 3) 116 2 ≤ (579916443886836835204483721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_116) (by simpa only [blockSum_one] using cell_3_117) (by norm_num)

theorem sum_3_118_2 : blockSum (rowCell 3) 118 2 ≤ (135612726696730834073132957 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_118) (by simpa only [blockSum_one] using cell_3_119) (by norm_num)

theorem sum_3_116_4 : blockSum (rowCell 3) 116 4 ≤ (1122367350673760171497015549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_116_2 sum_3_118_2 (by norm_num)

theorem sum_3_112_8 : blockSum (rowCell 3) 112 8 ≤ (599247391438226414904546919 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_112_4 sum_3_116_4 (by norm_num)

theorem sum_3_120_2 : blockSum (rowCell 3) 120 2 ≤ (101171931544987585128887027 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_120) (by simpa only [blockSum_one] using cell_3_121) (by norm_num)

theorem sum_3_122_2 : blockSum (rowCell 3) 122 2 ≤ (470328211578251186943192103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_122) (by simpa only [blockSum_one] using cell_3_123) (by norm_num)

theorem sum_3_120_4 : blockSum (rowCell 3) 120 4 ≤ (488093934651594556293813619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_120_2 sum_3_122_2 (by norm_num)

theorem sum_3_124_2 : blockSum (rowCell 3) 124 2 ≤ (436013023482705679470340831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_124) (by simpa only [blockSum_one] using cell_3_125) (by norm_num)

theorem sum_3_126_2 : blockSum (rowCell 3) 126 2 ≤ (403042384121267596649629209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_126) (by simpa only [blockSum_one] using cell_3_127) (by norm_num)

theorem sum_3_124_4 : blockSum (rowCell 3) 124 4 ≤ (20976385190099331902999251 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_124_2 sum_3_126_2 (by norm_num)

theorem sum_3_120_8 : blockSum (rowCell 3) 120 8 ≤ (907621638453581194353798639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_120_4 sum_3_124_4 (by norm_num)

theorem sum_3_112_16 : blockSum (rowCell 3) 112 16 ≤ (2106116421330034024162892477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_112_8 sum_3_120_8 (by norm_num)

theorem sum_3_96_32 : blockSum (rowCell 3) 96 32 ≤ (1080058053749985271772734723 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_96_16 sum_3_112_16 (by norm_num)

#print axioms sum_3_96_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
