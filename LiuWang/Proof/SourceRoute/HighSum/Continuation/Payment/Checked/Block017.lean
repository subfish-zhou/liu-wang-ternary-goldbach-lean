import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_32_0 : expNegUpper (213278095079686681427 / 3033777816451587200 : ℝ) ≤ (36807717704966488549875339769 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (346383 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_32_1 : expNegUpper (34100624923879535174511 / 485404450632253952000 : ℝ) ≤ (309304171561262789235201945827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1731249 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_32 : rowCell 1 32 ≤ (44027152836554174870159859829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36807717704966488549875339769 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (309304171561262789235201945827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_32_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_32_1
  · norm_num [gridPoint]

theorem exp_1_33_0 : expNegUpper (34432222085262222098919 / 490124545874743808000 : ℝ) ≤ (15465173444098924169360013447 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1731249 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_33_1 : expNegUpper (17204520091781737052279 / 245062272937371904000 : ℝ) ≤ (162142194784964607746123244983 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (173061 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_33 : rowCell 1 33 ≤ (46201795877404687288112469663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15465173444098924169360013447 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (162142194784964607746123244983 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_33_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_33_1
  · norm_num [gridPoint]

theorem exp_1_34_0 : expNegUpper (231613449667125877717 / 3299116529486592000 : ℝ) ≤ (81070916736530840801102156469 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (173061 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_34_1 : expNegUpper (462927030217616912431 / 6598233058973184000 : ℝ) ≤ (169680685306166001794703430169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (345999 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_34 : rowCell 1 34 ≤ (24196796191175498385674314537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (81070916736530840801102156469 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (169680685306166001794703430169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_34_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_34_1
  · norm_num [gridPoint]

theorem exp_1_35_0 : expNegUpper (35053891299508494433277 / 499633251276988928000 : ℝ) ≤ (84840157195855038704781371329 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (345999 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_35_1 : expNegUpper (8758024041122891221719 / 124908312819247232000 : ℝ) ≤ (177245970187010360247443724327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (864703 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_35 : rowCell 1 35 ≤ (50596352726128191016184238079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (84840157195855038704781371329 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (177245970187010360247443724327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_35_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_35_1
  · norm_num [gridPoint]

theorem exp_1_36_0 : expNegUpper (8841963406479926788791 / 126105465359186048000 : ℝ) ≤ (177245590073992331970805660553 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (864703 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_36_1 : expNegUpper (1413870274816520407891 / 20176874457469767680 : ℝ) ≤ (369631698470003075041218263779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1728841 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_36 : rowCell 1 36 ≤ (13200922721993106068746793929 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (177245590073992331970805660553 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (369631698470003075041218263779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_36_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_36_1
  · norm_num [gridPoint]

theorem exp_1_37_0 : expNegUpper (475785525621882220697 / 6789777465363394560 : ℝ) ≤ (73926184143964786549557566189 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1728841 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_37_1 : expNegUpper (5943919896070708515431 / 84872218317042432000 : ℝ) ≤ (384735270785479149717321278813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (17283 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_37 : rowCell 1 37 ≤ (55009060435441881319093908531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (73926184143964786549557566189 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (384735270785479149717321278813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_37_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_37_1
  · norm_num [gridPoint]

theorem exp_1_38_0 : expNegUpper (18001041839505759676837 / 257033798336760064000 : ℝ) ≤ (384734476445184825227474382337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (17283 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_38_1 : expNegUpper (35982393674863934301873 / 514067596673520128000 : ℝ) ≤ (399756570725419462975707774477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1727783 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_38 : rowCell 1 38 ≤ (28602895987927828517783112711 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (384734476445184825227474382337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (399756570725419462975707774477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_38_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_38_1
  · norm_num [gridPoint]

theorem exp_1_39_0 : expNegUpper (1452894855614776491537 / 20756988870021632000 : ℝ) ≤ (199877880392891070663330943217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1727783 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_39_1 : expNegUpper (181516948790353532771 / 2594623608752704000 : ℝ) ≤ (10366226674750575479918037087 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (172729 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_39 : rowCell 1 39 ≤ (29693565866624583565157011531 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (199877880392891070663330943217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10366226674750575479918037087 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_39_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_39_1
  · norm_num [gridPoint]

theorem exp_1_40_0 : expNegUpper (1526866147835562170233 / 21825195213888192000 : ℝ) ≤ (25915515155871556012231160569 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (172729 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_40_1 : expNegUpper (12208839206127738192877 / 174601561711105536000 : ℝ) ≤ (214683027724296950024628766367 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1726819 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_40 : rowCell 1 40 ≤ (30773140450032868385940975137 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25915515155871556012231160569 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (214683027724296950024628766367 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_40_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_40_1
  · norm_num [gridPoint]

theorem exp_1_41_0 : expNegUpper (36969342144402405474239 / 528707486821847552000 : ℝ) ≤ (214682608743110657153422473477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1726819 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_41_1 : expNegUpper (3695178724814010510423 / 52870748682184755200 : ℝ) ≤ (27741308291860237349444484667 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1726371 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_41 : rowCell 1 41 ≤ (994944303257714298866765211 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (214682608743110657153422473477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27741308291860237349444484667 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_41_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_41_1
  · norm_num [gridPoint]

theorem exp_1_42_0 : expNegUpper (3729604517175479918343 / 53363312681613363200 : ℝ) ≤ (17754403294934857803993549471 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1726371 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_42_1 : expNegUpper (37279208639680024860061 / 533633126816133632000 : ℝ) ≤ (18323498747227312501621516731 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (862973 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_42 : rowCell 1 42 ≤ (65770825766364536594008364463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17754403294934857803993549471 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18323498747227312501621516731 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_42_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_42_1
  · norm_num [gridPoint]

theorem exp_1_43_0 : expNegUpper (12541635540816439980743 / 179527201705391616000 : ℝ) ≤ (114521651804842685163346040811 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (862973 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_43_1 : expNegUpper (3134065982111801714599 / 44881800426347904000 : ℝ) ≤ (472000076570805292933745791777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (862771 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_43 : rowCell 1 43 ≤ (33911378303367302052726846129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (114521651804842685163346040811 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (472000076570805292933745791777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_43_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_43_1
  · norm_num [gridPoint]

theorem exp_1_44_0 : expNegUpper (29196874222172780369 / 418117632093824000 : ℝ) ≤ (29499950321565744095039623349 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (862771 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_44_1 : expNegUpper (116740143622964735319 / 1672470528375296000 : ℝ) ≤ (485554076625832247913097115479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1725161 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_44 : rowCell 1 44 ≤ (69825645608509463497119271633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29499950321565744095039623349 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (485554076625832247913097115479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_44_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_44_1
  · norm_num [gridPoint]

theorem exp_1_45_0 : expNegUpper (38289144763219329524907 / 548547076633522688000 : ℝ) ≤ (485553196461946619543049731547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1725161 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_45_1 : expNegUpper (19137241654192213399793 / 274273538316761344000 : ℝ) ≤ (498705952772513683820228807357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1078 / 625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_45 : rowCell 1 45 ≤ (71773061457506235656679074003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (485553196461946619543049731547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (498705952772513683820228807357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_45_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_45_1
  · norm_num [gridPoint]

theorem exp_1_46_0 : expNegUpper (6437423572995351967819 / 92260678308471552000 : ℝ) ≤ (24935253255851504848381699169 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1078 / 625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_46_1 : expNegUpper (2574040778029528717799 / 36904271323388620800 : ℝ) ≤ (511413599233338533558714123733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1724461 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_46 : rowCell 1 46 ≤ (73658760532916382822297792487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24935253255851504848381699169 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (511413599233338533558714123733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_46_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_46_1
  · norm_num [gridPoint]

theorem exp_1_47_0 : expNegUpper (7792427301084321610957 / 111720780274778214400 : ℝ) ≤ (255706352673697671523797164139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1724461 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_47_1 : expNegUpper (2434308859748606100621 / 34912743835868192000 : ℝ) ≤ (523636555429366663646599729623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1724143 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_47 : rowCell 1 47 ≤ (37738361011455857325128010009 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (255706352673697671523797164139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (523636555429366663646599729623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_47_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_47_1
  · norm_num [gridPoint]

theorem exp_1_48_0 : expNegUpper (2456371247369154062349 / 35229160700169248000 : ℝ) ≤ (104727131316622077043572584043 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1724143 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_48_1 : expNegUpper (39289483557327374057503 / 563666571202707968000 : ℝ) ≤ (535336227327099067777784986631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (861923 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_48 : rowCell 1 48 ≤ (15444236238956884778249614229 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (104727131316622077043572584043 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (535336227327099067777784986631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_48_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_48_1
  · norm_num [gridPoint]

theorem exp_1_49_0 : expNegUpper (21143446286808175661 / 303334442313216000 : ℝ) ≤ (267667662397076507459122801619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (861923 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_49_1 : expNegUpper (10568599217821495157 / 151667221156608000 : ℝ) ≤ (68309511699836535058268593999 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (107723 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_49 : rowCell 1 49 ≤ (78886660569152491261375108301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (267667662397076507459122801619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (68309511699836535058268593999 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_49_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_49_1
  · norm_num [gridPoint]

theorem exp_1_50_0 : expNegUpper (644971161086078191681 / 9255813318993664000 : ℝ) ≤ (109295037730145434130114500927 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (107723 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_50_1 : expNegUpper (1289588460542775570411 / 18511626637987328000 : ℝ) ≤ (69627736893905598456437372249 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1723311 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_50 : rowCell 1 50 ≤ (80467998774001023533568339531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (109295037730145434130114500927 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (69627736893905598456437372249 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_50_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_50_1
  · norm_num [gridPoint]

theorem exp_1_51_0 : expNegUpper (40334700548959667286189 / 578991610523689472000 : ℝ) ≤ (111404197810537308690937043223 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1723311 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_51_1 : expNegUpper (2016223958982616415927 / 28949580526184473600 : ℝ) ≤ (283470903388749157355283112639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1723073 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_51 : rowCell 1 51 ≤ (1639207537645229170782372859 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (111404197810537308690937043223 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (283470903388749157355283112639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_51_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_51_1
  · norm_num [gridPoint]

theorem exp_1_52_0 : expNegUpper (678057291082873904989 / 9735760559592115200 : ℝ) ≤ (283470450390202918029002076739 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1723073 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_52_1 : expNegUpper (13557989255882703491737 / 194715211191842304000 : ℝ) ≤ (57620658988427120821717189537 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (344571 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_52 : rowCell 1 52 ≤ (83359342065841894114327803461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (283470450390202918029002076739 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (57620658988427120821717189537 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_52_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_52_1
  · norm_num [gridPoint]

theorem exp_1_53_0 : expNegUpper (41034432727713795652739 / 589322494933119488000 : ℝ) ≤ (14405142130585355739745544689 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (344571 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_53_1 : expNegUpper (20512859016576017940909 / 294661247466559744000 : ℝ) ≤ (584789725463468786200269774881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (53833 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_53 : rowCell 1 53 ≤ (21165207107275449626968243911 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14405142130585355739745544689 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (584789725463468786200269774881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_53_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_53_1
  · norm_num [gridPoint]

theorem exp_1_54_0 : expNegUpper (827753926590447961509 / 11890443891929344000 : ℝ) ≤ (116957764670326619501592128549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (53833 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_54_1 : expNegUpper (1655189598740110050697 / 23780887783858688000 : ℝ) ≤ (118533505336171931435485165721 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (430619 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_54 : rowCell 1 54 ≤ (85861174915308853989367669143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (116957764670326619501592128549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (118533505336171931435485165721 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_54_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_54_1
  · norm_num [gridPoint]

theorem exp_1_55_0 : expNegUpper (13914412754245629432179 / 199914910855190016000 : ℝ) ≤ (7408332853805049995964942287 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (430619 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_55_1 : expNegUpper (1739001815251620973379 / 24989363856898752000 : ℝ) ≤ (599819230667337057201251918743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (344463 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_55 : rowCell 1 55 ≤ (86957140210233277791182166471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7408332853805049995964942287 / 12500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (599819230667337057201251918743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_55_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_55_1
  · norm_num [gridPoint]

theorem exp_1_56_0 : expNegUpper (5262633564961989130633 / 75623763605053504000 : ℝ) ≤ (149954584295505736480095726081 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (344463 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_56_1 : expNegUpper (8418927763619827778379 / 120998021768085606400 : ℝ) ≤ (606227069303609251950982692587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (430543 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_56 : rowCell 1 56 ≤ (43972957298676094651978877191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (149954584295505736480095726081 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (606227069303609251950982692587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_56_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_56_1
  · norm_num [gridPoint]

theorem exp_1_57_0 : expNegUpper (653249186042124908463 / 9388589591092940800 : ℝ) ≤ (121245236366144372398012938991 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (430543 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_57_1 : expNegUpper (1632905219885465561111 / 23471473977732352000 : ℝ) ≤ (61187631898986053608470312337 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1722047 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_57 : rowCell 1 57 ≤ (22206282187200612364902584903 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (121245236366144372398012938991 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (61187631898986053608470312337 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_57_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_57_1
  · norm_num [gridPoint]

theorem exp_1_58_0 : expNegUpper (7137272329033692173449 / 102591562717901568000 : ℝ) ≤ (61187543861263565864539901383 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1722047 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_58_1 : expNegUpper (14272914751715482393711 / 205183125435803136000 : ℝ) ≤ (616755329584764808385489359849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (86097 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_58 : rowCell 1 58 ≤ (89592859464910244407874478273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (61187543861263565864539901383 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (616755329584764808385489359849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_58_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_58_1
  · norm_num [gridPoint]

theorem exp_1_59_0 : expNegUpper (1727535566257066469837 / 24834530699981312000 : ℝ) ≤ (308377228672566884020333705629 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (86097 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_59_1 : expNegUpper (431842744248108133977 / 6208632674995328000 : ℝ) ≤ (77606941610175038692438736151 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721851 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_59 : rowCell 1 59 ≤ (90247632402544459088856854691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (308377228672566884020333705629 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (77606941610175038692438736151 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_59_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_59_1
  · norm_num [gridPoint]

theorem exp_1_60_0 : expNegUpper (10888868157937572973713 / 156549999249352832000 : ℝ) ≤ (155213667444265417348685838819 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721851 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_60_1 : expNegUpper (43552136218353849967651 / 626199996997411328000 : ℝ) ≤ (156042857789854488933272113393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721779 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_60 : rowCell 1 60 ≤ (2837138183075801699460459259 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (155213667444265417348685838819 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (156042857789854488933272113393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_60_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_60_1
  · norm_num [gridPoint]

theorem exp_1_61_0 : expNegUpper (14641631464170563405513 / 210519854933681664000 : ℝ) ≤ (78021322267655231414290783119 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721779 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_61_1 : expNegUpper (292815597520761357467 / 4210397098673633280 : ℝ) ≤ (626700566511806314342673171201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (68869 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_61 : rowCell 1 61 ≤ (18242929539528859292533946269 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (78021322267655231414290783119 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (626700566511806314342673171201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_61_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_61_1
  · norm_num [gridPoint]

theorem exp_1_62_0 : expNegUpper (885933288620990068801 / 12738839418208675840 : ℝ) ≤ (626699724481574377018288252669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (68869 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_62_1 : expNegUpper (44294894646430521083961 / 636941970910433792000 : ℝ) ≤ (157110867947391946792437493901 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721687 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_62 : rowCell 1 62 ≤ (91526169539807086466879885297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (626699724481574377018288252669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (157110867947391946792437493901 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_62_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_62_1
  · norm_num [gridPoint]

theorem exp_1_63_0 : expNegUpper (44670792739702378294449 / 642347215325577728000 : ℝ) ≤ (125688528319609773479900942693 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721687 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_63_1 : expNegUpper (697965801025647642007 / 10036675239462152000 : ℝ) ≤ (31470180206880685017141096173 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721667 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_63 : rowCell 1 63 ≤ (45861639167640458787054332181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (125688528319609773479900942693 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31470180206880685017141096173 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_63_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_63_1
  · norm_num [gridPoint]

theorem sum_1_32_2 : blockSum (rowCell 1) 32 2 ≤ (22557237178489715539568082373 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_32) (by simpa only [blockSum_one] using cell_1_33) (by norm_num)

theorem sum_1_34_2 : blockSum (rowCell 1) 34 2 ≤ (98989945108479187787532867153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_34) (by simpa only [blockSum_one] using cell_1_35) (by norm_num)

theorem sum_1_32_4 : blockSum (rowCell 1) 32 4 ≤ (37843778764487609989161039329 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_32_2 sum_1_34_2 (by norm_num)

theorem sum_1_36_2 : blockSum (rowCell 1) 36 2 ≤ (107812751323414305594081084247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_36) (by simpa only [blockSum_one] using cell_1_37) (by norm_num)

theorem sum_1_38_2 : blockSum (rowCell 1) 38 2 ≤ (29148230927276206041470062121 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_38) (by simpa only [blockSum_one] using cell_1_39) (by norm_num)

theorem sum_1_36_4 : blockSum (rowCell 1) 36 4 ≤ (224405675032519129759961332731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_36_2 sum_1_38_2 (by norm_num)

theorem sum_1_32_8 : blockSum (rowCell 1) 32 8 ≤ (12925767776717411865805204043 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_32_4 sum_1_36_4 (by norm_num)

theorem sum_1_40_2 : blockSum (rowCell 1) 40 2 ≤ (62611358154279725949677461889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_40) (by simpa only [blockSum_one] using cell_1_41) (by norm_num)

theorem sum_1_42_2 : blockSum (rowCell 1) 42 2 ≤ (133593582373099140699462056721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_42) (by simpa only [blockSum_one] using cell_1_43) (by norm_num)

theorem sum_1_40_4 : blockSum (rowCell 1) 40 4 ≤ (258816298681658592598816980499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_40_2 sum_1_42_2 (by norm_num)

theorem sum_1_44_2 : blockSum (rowCell 1) 44 2 ≤ (35399676766503924788449586409 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_44) (by simpa only [blockSum_one] using cell_1_45) (by norm_num)

theorem sum_1_46_2 : blockSum (rowCell 1) 46 2 ≤ (29827096511165619494510762501 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_46) (by simpa only [blockSum_one] using cell_1_47) (by norm_num)

theorem sum_1_44_4 : blockSum (rowCell 1) 44 4 ≤ (290734189621843796626352158141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_44_2 sum_1_46_2 (by norm_num)

theorem sum_1_40_8 : blockSum (rowCell 1) 40 8 ≤ (6869381103793779865314614233 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_40_4 sum_1_44_4 (by norm_num)

theorem sum_1_32_16 : blockSum (rowCell 1) 32 16 ≤ (60198441072403723058183479251 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_32_8 sum_1_40_8 (by norm_num)

theorem sum_1_48_2 : blockSum (rowCell 1) 48 2 ≤ (78053920881968457576311589723 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_48) (by simpa only [blockSum_one] using cell_1_49) (by norm_num)

theorem sum_1_50_2 : blockSum (rowCell 1) 50 2 ≤ (162428375656262482072686982481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_50) (by simpa only [blockSum_one] using cell_1_51) (by norm_num)

theorem sum_1_48_4 : blockSum (rowCell 1) 48 4 ≤ (318536217420199397225310161927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_48_2 sum_1_50_2 (by norm_num)

theorem sum_1_52_2 : blockSum (rowCell 1) 52 2 ≤ (33604034098988738524440155821 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_52) (by simpa only [blockSum_one] using cell_1_53) (by norm_num)

theorem sum_1_54_2 : blockSum (rowCell 1) 54 2 ≤ (86409157562771065890274917807 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_54) (by simpa only [blockSum_one] using cell_1_55) (by norm_num)

theorem sum_1_52_4 : blockSum (rowCell 1) 52 4 ≤ (340838485620485824402750614719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_52_2 sum_1_54_2 (by norm_num)

theorem sum_1_48_8 : blockSum (rowCell 1) 48 8 ≤ (329687351520342610814030388323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_48_4 sum_1_52_4 (by norm_num)

theorem sum_1_56_2 : blockSum (rowCell 1) 56 2 ≤ (88385521673077319381784046997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_56) (by simpa only [blockSum_one] using cell_1_57) (by norm_num)

theorem sum_1_58_2 : blockSum (rowCell 1) 58 2 ≤ (44960122966863675874182833241 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_58) (by simpa only [blockSum_one] using cell_1_59) (by norm_num)

theorem sum_1_56_4 : blockSum (rowCell 1) 56 4 ≤ (178305767606804671130149713479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_56_2 sum_1_58_2 (by norm_num)

theorem sum_1_60_2 : blockSum (rowCell 1) 60 2 ≤ (182003069556069950845404427633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_60) (by simpa only [blockSum_one] using cell_1_61) (by norm_num)

theorem sum_1_62_2 : blockSum (rowCell 1) 62 2 ≤ (183249447875088004040988549659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_62) (by simpa only [blockSum_one] using cell_1_63) (by norm_num)

theorem sum_1_60_4 : blockSum (rowCell 1) 60 4 ≤ (91313129357789488721598244323 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_60_2 sum_1_62_2 (by norm_num)

theorem sum_1_56_8 : blockSum (rowCell 1) 56 8 ≤ (2887456210579069188586769617 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_56_4 sum_1_60_4 (by norm_num)

theorem sum_1_48_16 : blockSum (rowCell 1) 48 16 ≤ (43163711115170391211711036903 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_48_8 sum_1_56_8 (by norm_num)

theorem sum_1_32_32 : blockSum (rowCell 1) 32 32 ≤ (146525863302744505481605553057 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_32_16 sum_1_48_16 (by norm_num)

#print axioms sum_1_32_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
