import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_32_0 : expNegUpper (222684024718803481427 / 3033777816451587200 : ℝ) ≤ (2651988029420303791898381871 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1774377 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_32_1 : expNegUpper (35598291931818095174511 / 485404450632253952000 : ℝ) ≤ (7069415104335723581251643017 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110843 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_32 : rowCell 2 32 ≤ (998971475212853102195069939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2651988029420303791898381871 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7069415104335723581251643017 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_32_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_32_1
  · norm_num [gridPoint]

theorem exp_2_33_0 : expNegUpper (5134921794548719728417 / 70017792267820544000 : ℝ) ≤ (14138795617163270834657434341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110843 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_33_1 : expNegUpper (2565284923273011578897 / 35008896133910272000 : ℝ) ≤ (3009095262499033515956374203 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1772627 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_33 : rowCell 2 33 ≤ (13300895808468782073026107 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14138795617163270834657434341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3009095262499033515956374203 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_33_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_33_1
  · norm_num [gridPoint]

theorem exp_2_34_0 : expNegUpper (241743531073118837717 / 3299116529486592000 : ℝ) ≤ (7522720103354363269191666551 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1772627 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_34_1 : expNegUpper (483090103238667792431 / 6598233058973184000 : ℝ) ≤ (7989188448867624424037777063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (885897 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_34 : rowCell 2 34 ≤ (2262284616216734459064718329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7522720103354363269191666551 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7989188448867624424037777063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_34_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_34_1
  · norm_num [gridPoint]

theorem exp_2_35_0 : expNegUpper (36580685244727566433277 / 499633251276988928000 : ℝ) ≤ (7989169641471905622018683781 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (885897 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_35_1 : expNegUpper (9137902093847627221719 / 124908312819247232000 : ℝ) ≤ (3387162409018164419081697619 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (442747 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_35 : rowCell 2 35 ≤ (2400129486148119244228282703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7989169641471905622018683781 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3387162409018164419081697619 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_35_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_35_1
  · norm_num [gridPoint]

theorem exp_2_36_0 : expNegUpper (9225482326364726788791 / 126105465359186048000 : ℝ) ≤ (16935772931557812142217894189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (442747 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_36_1 : expNegUpper (1474942032625283287891 / 20176874457469767680 : ℝ) ≤ (17915881660571738089038968389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (177021 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_36 : rowCell 2 36 ≤ (508282792978301883851207263 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16935772931557812142217894189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17915881660571738089038968389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_36_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_36_1
  · norm_num [gridPoint]

theorem exp_2_37_0 : expNegUpper (496336957806673260697 / 6789777465363394560 : ℝ) ≤ (17915841063590095107836556841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (177021 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_37_1 : expNegUpper (6199599175993908515431 / 84872218317042432000 : ℝ) ≤ (18916512109519743849137803293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1769459 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_37 : rowCell 2 37 ≤ (335731035618809177826688531 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17915841063590095107836556841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18916512109519743849137803293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_37_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_37_1
  · norm_num [gridPoint]

theorem exp_2_38_0 : expNegUpper (18775361413595487676837 / 257033798336760064000 : ℝ) ≤ (18916470049419557427801101599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1769459 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_38_1 : expNegUpper (37523751088723262301873 / 514067596673520128000 : ℝ) ≤ (3987092867351336125397350347 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (884367 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_38 : rowCell 2 38 ≤ (1416558980737385679584503807 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18916470049419557427801101599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3987092867351336125397350347 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_38_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_38_1
  · norm_num [gridPoint]

theorem exp_2_39_0 : expNegUpper (1515131690914759851537 / 20756988870021632000 : ℝ) ≤ (797416833555240430144687927 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (884367 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_39_1 : expNegUpper (189260144531250812771 / 2594623608752704000 : ℝ) ≤ (327661615866343814938603831 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (884017 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_39 : rowCell 2 39 ≤ (2982885080698098174141895461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (797416833555240430144687927 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (327661615866343814938603831 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_39_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_39_1
  · norm_num [gridPoint]

theorem exp_2_40_0 : expNegUpper (227428512886150024319 / 3117885030555456000 : ℝ) ≤ (20970298510095098079953892753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (884017 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_40_1 : expNegUpper (1818211357184895170411 / 24943080244443648000 : ℝ) ≤ (11009304725796741389670021053 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1767361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_40 : rowCell 2 40 ≤ (1567394895706664072922039751 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20970298510095098079953892753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11009304725796741389670021053 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_40_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_40_1
  · norm_num [gridPoint]

theorem exp_2_41_0 : expNegUpper (38539826495542245474239 / 528707486821847552000 : ℝ) ≤ (22018563173937896230524728161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1767361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_41_1 : expNegUpper (3851498986495981710423 / 52870748682184755200 : ℝ) ≤ (5769397439104777701412164159 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (220839 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_41 : rowCell 2 41 ≤ (1644225993878265660350636141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22018563173937896230524728161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5769397439104777701412164159 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_41_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_41_1
  · norm_num [gridPoint]

theorem exp_2_42_0 : expNegUpper (3887381125721476718343 / 53363312681613363200 : ℝ) ≤ (23077542146382526511811851353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (220839 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_42_1 : expNegUpper (38849692990819864860061 / 533633126816133632000 : ℝ) ≤ (24144492185295718985227943817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1766089 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_42 : rowCell 2 42 ≤ (3443473169512447528817830611 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23077542146382526511811851353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24144492185295718985227943817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_42_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_42_1
  · norm_num [gridPoint]

theorem exp_2_43_0 : expNegUpper (13069984814076471980743 / 179527201705391616000 : ℝ) ≤ (241444432874085268663509999 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1766089 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_43_1 : expNegUpper (3265546489233465714599 / 44881800426347904000 : ℝ) ≤ (25216419529739548770480777113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1765489 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_43 : rowCell 2 43 ≤ (1799719232138312478455989073 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (241444432874085268663509999 / 10000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25216419529739548770480777113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_43_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_43_1
  · norm_num [gridPoint]

theorem exp_2_44_0 : expNegUpper (395482660429248384797 / 5435529217219712000 : ℝ) ≤ (5043273878592901354991432579 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1765489 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_44_1 : expNegUpper (1581023779889745399147 / 21742116868878848000 : ℝ) ≤ (26290384838199482067927471261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (882457 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_44 : rowCell 2 44 ≤ (234744924633498914238710847 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5043273878592901354991432579 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26290384838199482067927471261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_44_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_44_1
  · norm_num [gridPoint]

theorem exp_2_45_0 : expNegUpper (39888756051639681524907 / 548547076633522688000 : ℝ) ≤ (26290333515731011681076767809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (882457 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_45_1 : expNegUpper (19933406431242325399793 / 274273538316761344000 : ℝ) ≤ (13681663766122249826596549903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1764363 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_45 : rowCell 2 45 ≤ (391247316807947207699342313 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26290333515731011681076767809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13681663766122249826596549903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_45_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_45_1
  · norm_num [gridPoint]

theorem exp_2_46_0 : expNegUpper (6705239076785431967819 / 92260678308471552000 : ℝ) ≤ (27363275081283383366602244609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1764363 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_46_1 : expNegUpper (2680681530590885517799 / 36904271323388620800 : ℝ) ≤ (5686426035457285788650599121 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (352767 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_46 : rowCell 2 46 ≤ (1017162770034830677487597813 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27363275081283383366602244609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5686426035457285788650599121 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_46_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_46_1
  · norm_num [gridPoint]

theorem exp_2_47_0 : expNegUpper (1159323178928063315851 / 15960111467825459200 : ℝ) ≤ (28432076658791866508864200699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (352767 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_47_1 : expNegUpper (362105667667126585803 / 4987534833695456000 : ℝ) ≤ (1179745430450518360408411517 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (176333 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_47 : rowCell 2 47 ≤ (1055998748075662567464553501 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28432076658791866508864200699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1179745430450518360408411517 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_47_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_47_1
  · norm_num [gridPoint]

theorem exp_2_48_0 : expNegUpper (2557712278080450062349 / 35229160700169248000 : ℝ) ≤ (29493581239684103598627106003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (176333 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_48_1 : expNegUpper (40903658314387982057503 / 563666571202707968000 : ℝ) ≤ (15272332665391298697463687759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1762847 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_48 : rowCell 2 48 ≤ (437804288053058499012666669 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29493581239684103598627106003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15272332665391298697463687759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_48_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_48_1
  · norm_num [gridPoint]

theorem exp_2_49_0 : expNegUpper (22012106673848636461 / 303334442313216000 : ℝ) ≤ (3054460987377183071384061777 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1762847 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_49_1 : expNegUpper (11000987615523024757 / 151667221156608000 : ℝ) ≤ (31582035832109937909011814669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1762387 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_49 : rowCell 2 49 ≤ (1132582705445287486532474117 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3054460987377183071384061777 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31582035832109937909011814669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_49_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_49_1
  · norm_num [gridPoint]

theorem exp_2_50_0 : expNegUpper (671358579796094191681 / 9255813318993664000 : ℝ) ≤ (31581979510220254192567561023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1762387 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_50_1 : expNegUpper (1342128403307319570411 / 18511626637987328000 : ℝ) ≤ (254707640656493676692290051 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (35239 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_50 : rowCell 2 50 ≤ (936079119950521413153580297 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31581979510220254192567561023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (254707640656493676692290051 / 7812500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_50_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_50_1
  · norm_num [gridPoint]

theorem exp_2_51_0 : expNegUpper (41978002243300787286189 / 578991610523689472000 : ℝ) ≤ (32602520890400142835958078789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (35239 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_51_1 : expNegUpper (2098024956983666015927 / 28949580526184473600 : ℝ) ≤ (1050098567845193092917310183 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (880767 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_51 : rowCell 2 51 ≤ (4827777307141853804514781933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32602520890400142835958078789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1050098567845193092917310183 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_51_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_51_1
  · norm_num [gridPoint]

theorem exp_2_52_0 : expNegUpper (705567014893894704989 / 9735760559592115200 : ℝ) ≤ (672061926821377933653431343 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (880767 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_52_1 : expNegUpper (14105756487329743491737 / 194715211191842304000 : ℝ) ≤ (345806757884202154356064711 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1761139 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_52 : rowCell 2 52 ≤ (994404384508023728707800663 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (672061926821377933653431343 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (345806757884202154356064711 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_52_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_52_1
  · norm_num [gridPoint]

theorem exp_2_53_0 : expNegUpper (42692297890695171652739 / 589322494933119488000 : ℝ) ≤ (17290308659707016375809121541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1761139 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_53_1 : expNegUpper (21338150730906641940909 / 294661247466559744000 : ℝ) ≤ (35532120595312132099598914903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (880383 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_53 : rowCell 2 53 ≤ (1278170960163700550684872169 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17290308659707016375809121541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35532120595312132099598914903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_53_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_53_1
  · norm_num [gridPoint]

theorem exp_2_54_0 : expNegUpper (123008123505211148787 / 1698634841704192000 : ℝ) ≤ (3553206156617536714144875739 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (880383 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_54_1 : expNegUpper (245929172179909298671 / 3397269683408384000 : ℝ) ≤ (4556818654796075387613199721 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1760413 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_54 : rowCell 2 54 ≤ (2624664167668995508772872097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3553206156617536714144875739 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4556818654796075387613199721 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_54_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_54_1
  · norm_num [gridPoint]

theorem exp_2_55_0 : expNegUpper (14471888964786173432179 / 199914910855190016000 : ℝ) ≤ (36454489729236007820271191021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1760413 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_55_1 : expNegUpper (1808382935972516973379 / 24989363856898752000 : ℝ) ≤ (18672560617859069935210544369 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1760081 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_55 : rowCell 2 55 ≤ (5381533935902432775597346897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36454489729236007820271191021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18672560617859069935210544369 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_55_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_55_1
  · norm_num [gridPoint]

theorem exp_2_56_0 : expNegUpper (5472597360704709130633 / 75623763605053504000 : ℝ) ≤ (9336265331903873219853082427 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1760081 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_56_1 : expNegUpper (8753413489944154178379 / 120998021768085606400 : ℝ) ≤ (38201110160074798370103463503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (175977 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_56 : rowCell 2 56 ≤ (43038239831217359450474501 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9336265331903873219853082427 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38201110160074798370103463503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_56_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_56_1
  · norm_num [gridPoint]

theorem exp_2_57_0 : expNegUpper (8829637838600001410019 / 122051664684208230400 : ℝ) ≤ (38201049934575044666698878129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (175977 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_57_1 : expNegUpper (22067623041481932294443 / 305129161710520576000 : ℝ) ≤ (19509958964762036598120159671 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879739 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_57 : rowCell 2 57 ≤ (1126204470972684615223346253 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38201049934575044666698878129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19509958964762036598120159671 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_57_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_57_1
  · norm_num [gridPoint]

theorem exp_2_58_0 : expNegUpper (7419651301464028173449 / 102591562717901568000 : ℝ) ≤ (7803971493681465067468604553 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879739 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_58_1 : expNegUpper (14835245451802778393711 / 205183125435803136000 : ℝ) ≤ (2487443006584694568747283349 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879603 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_58 : rowCell 2 58 ≤ (5747548325135170938038667161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7803971493681465067468604553 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2487443006584694568747283349 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_58_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_58_1
  · norm_num [gridPoint]

theorem exp_2_59_0 : expNegUpper (1795597789013152229837 / 24834530699981312000 : ℝ) ≤ (39799027490274720292456607133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879603 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_59_1 : expNegUpper (448785482593928293977 / 6208632674995328000 : ℝ) ≤ (40536318107861552906578829107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879477 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_59 : rowCell 2 59 ≤ (585812557730315786723161627 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (39799027490274720292456607133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40536318107861552906578829107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_59_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_59_1
  · norm_num [gridPoint]

theorem exp_2_60_0 : expNegUpper (11316077483743140973713 / 156549999249352832000 : ℝ) ≤ (1013406435500457993024794147 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879477 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_60_1 : expNegUpper (45253691787255993967651 / 626199996997411328000 : ℝ) ≤ (2061473513659586342270179701 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1758721 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_60 : rowCell 2 60 ≤ (149060758119621274100569041 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1013406435500457993024794147 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2061473513659586342270179701 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_60_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_60_1
  · norm_num [gridPoint]

theorem exp_2_61_0 : expNegUpper (2173381591907337629359 / 30074264990525952000 : ℝ) ≤ (20614704796509111972466847843 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1758721 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_61_1 : expNegUpper (43458263744129976781 / 601485299810519040 : ℝ) ≤ (41876581686920758158986859217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1758507 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_61 : rowCell 2 61 ≤ (1212032709934438229039424171 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20614704796509111972466847843 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41876581686920758158986859217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_61_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_61_1
  · norm_num [gridPoint]

theorem exp_2_62_0 : expNegUpper (920401304058240628801 / 12738839418208675840 : ℝ) ≤ (20938260546888757890463502979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1758507 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_62_1 : expNegUpper (46011013683972921083961 / 636941970910433792000 : ℝ) ≤ (2123793637143828956534039939 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (219789 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_62 : rowCell 2 62 ≤ (615105234392265421986783827 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20938260546888757890463502979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2123793637143828956534039939 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_62_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_62_1
  · norm_num [gridPoint]

theorem exp_2_63_0 : expNegUpper (46401475245885034294449 / 642347215325577728000 : ℝ) ≤ (5309476539345224035827768819 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (219789 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_63_1 : expNegUpper (724893938085999642007 / 10036675239462152000 : ℝ) ≤ (2689109649294864076330246121 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (351627 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_63 : rowCell 2 63 ≤ (1558712765457892216536341683 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5309476539345224035827768819 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2689109649294864076330246121 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_63_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_63_1
  · norm_num [gridPoint]

theorem sum_2_32_2 : blockSum (rowCell 2) 32 2 ≤ (2063043139890355668037158499 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_32) (by simpa only [blockSum_one] using cell_2_33) (by norm_num)

theorem sum_2_34_2 : blockSum (rowCell 2) 34 2 ≤ (582801762795606712911625129 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_34) (by simpa only [blockSum_one] using cell_2_35) (by norm_num)

theorem sum_2_32_4 : blockSum (rowCell 2) 32 4 ≤ (878850038214556503936731803 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_32_2 sum_2_34_2 (by norm_num)

theorem sum_2_36_2 : blockSum (rowCell 2) 36 2 ≤ (5227262249841982841869544563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_36) (by simpa only [blockSum_one] using cell_2_37) (by norm_num)

theorem sum_2_38_2 : blockSum (rowCell 2) 38 2 ≤ (232640121686914781332436123 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_38) (by simpa only [blockSum_one] using cell_2_39) (by norm_num)

theorem sum_2_36_4 : blockSum (rowCell 2) 36 4 ≤ (5521632646007426187590223819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_36_2 sum_2_38_2 (by norm_num)

theorem sum_2_32_8 : blockSum (rowCell 2) 32 8 ≤ (4957941418540104353636941417 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_32_4 sum_2_36_4 (by norm_num)

theorem sum_2_40_2 : blockSum (rowCell 2) 40 2 ≤ (802905222396232433318168973 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_40) (by simpa only [blockSum_one] using cell_2_41) (by norm_num)

theorem sum_2_42_2 : blockSum (rowCell 2) 42 2 ≤ (7042911633789072485729808757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_42) (by simpa only [blockSum_one] using cell_2_43) (by norm_num)

theorem sum_2_40_4 : blockSum (rowCell 2) 40 4 ≤ (13466153412958931952275160541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_40_2 sum_2_42_2 (by norm_num)

theorem sum_2_44_2 : blockSum (rowCell 2) 44 2 ≤ (3834195981107727352406398341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_44) (by simpa only [blockSum_one] using cell_2_45) (by norm_num)

theorem sum_2_46_2 : blockSum (rowCell 2) 46 2 ≤ (1036580759055246622476075657 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_46) (by simpa only [blockSum_one] using cell_2_47) (by norm_num)

theorem sum_2_44_4 : blockSum (rowCell 2) 44 4 ≤ (7980519017328713842310700969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_44_2 sum_2_46_2 (by norm_num)

theorem sum_2_40_8 : blockSum (rowCell 2) 40 8 ≤ (29427191447616359636896562479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_40_4 sum_2_44_4 (by norm_num)

theorem sum_2_32_16 : blockSum (rowCell 2) 32 16 ≤ (49258957121776777051444328147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_32_8 sum_2_40_8 (by norm_num)

theorem sum_2_48_2 : blockSum (rowCell 2) 48 2 ≤ (4454186851155867468128281579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_48) (by simpa only [blockSum_one] using cell_2_49) (by norm_num)

theorem sum_2_50_2 : blockSum (rowCell 2) 50 2 ≤ (4754086453447230435141341709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_50) (by simpa only [blockSum_one] using cell_2_51) (by norm_num)

theorem sum_2_48_4 : blockSum (rowCell 2) 48 4 ≤ (1151034163075387237908702911 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_48_2 sum_2_50_2 (by norm_num)

theorem sum_2_52_2 : blockSum (rowCell 2) 52 2 ≤ (10084705763194920846278491991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_52) (by simpa only [blockSum_one] using cell_2_53) (by norm_num)

theorem sum_2_54_2 : blockSum (rowCell 2) 54 2 ≤ (10630862271240423793143091091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_54) (by simpa only [blockSum_one] using cell_2_55) (by norm_num)

theorem sum_2_52_4 : blockSum (rowCell 2) 52 4 ≤ (10357784017217672319710791541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_52_2 sum_2_54_2 (by norm_num)

theorem sum_2_48_8 : blockSum (rowCell 2) 48 8 ≤ (19566057321820770222980414829 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_48_4 sum_2_52_4 (by norm_num)

theorem sum_2_56_2 : blockSum (rowCell 2) 56 2 ≤ (11139917053259245085777467393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_56) (by simpa only [blockSum_one] using cell_2_57) (by norm_num)

theorem sum_2_58_2 : blockSum (rowCell 2) 58 2 ≤ (11605673902438328805270283431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_58) (by simpa only [blockSum_one] using cell_2_59) (by norm_num)

theorem sum_2_56_4 : blockSum (rowCell 2) 56 4 ≤ (2843198869462196736380968853 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_56_2 sum_2_58_2 (by norm_num)

theorem sum_2_60_2 : blockSum (rowCell 2) 60 2 ≤ (2404518774891408421843976499 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_60) (by simpa only [blockSum_one] using cell_2_61) (by norm_num)

theorem sum_2_62_2 : blockSum (rowCell 2) 62 2 ≤ (6192951702877111543006602501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_62) (by simpa only [blockSum_one] using cell_2_63) (by norm_num)

theorem sum_2_60_4 : blockSum (rowCell 2) 60 4 ≤ (24408497280211265195233087497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_60_2 sum_2_62_2 (by norm_num)

theorem sum_2_56_8 : blockSum (rowCell 2) 56 8 ≤ (47154088235908839086280838321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_56_4 sum_2_60_4 (by norm_num)

theorem sum_2_48_16 : blockSum (rowCell 2) 48 16 ≤ (86286202879550379532241667979 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_48_8 sum_2_56_8 (by norm_num)

theorem sum_2_32_32 : blockSum (rowCell 2) 32 32 ≤ (67772580000663578291842998063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_32_16 sum_2_48_16 (by norm_num)

#print axioms sum_2_32_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
