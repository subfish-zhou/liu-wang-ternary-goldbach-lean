import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_32_0 : expNegUpper (239928229057184281427 / 3033777816451587200 : ℝ) ≤ (9015949824408183865471091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1854947 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_32_1 : expNegUpper (38344014779705455174511 / 485404450632253952000 : ℝ) ≤ (49408036945583790187793311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1853619 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_32 : rowCell 6 32 ≤ (1722533562855372237354901 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9015949824408183865471091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (49408036945583790187793311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_32_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_32_1
  · norm_num [gridPoint]

theorem exp_6_33_0 : expNegUpper (38716875102235534098919 / 490124545874743808000 : ℝ) ≤ (1235197505908609404140853 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1853619 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_33_1 : expNegUpper (19336530809981545052279 / 245062272937371904000 : ℝ) ≤ (27014012239817137724434123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (74093 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_33 : rowCell 6 33 ≤ (7542640561002775287799323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1235197505908609404140853 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27014012239817137724434123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_33_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_33_1
  · norm_num [gridPoint]

theorem exp_6_34_0 : expNegUpper (780946040952317793151 / 9897349588459776000 : ℝ) ≤ (5402787784579466295630831 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (74093 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_34_1 : expNegUpper (1560167211331783217293 / 19794699176919552000 : ℝ) ≤ (2947348345029003207873337 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (231383 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_34 : rowCell 6 34 ≤ (514889198733920120136273 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5402787784579466295630831 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2947348345029003207873337 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_34_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_34_1
  · norm_num [gridPoint]

theorem exp_6_35_0 : expNegUpper (39379807477629198433277 / 499633251276988928000 : ℝ) ≤ (14736702490319865502003029 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (370213 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_35_1 : expNegUpper (9834345190509643221719 / 124908312819247232000 : ℝ) ≤ (64170989257914021928178903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1849837 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_35 : rowCell 6 35 ≤ (4488930266355662421386387 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14736702490319865502003029 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64170989257914021928178903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_35_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_35_1
  · norm_num [gridPoint]

theorem exp_6_36_0 : expNegUpper (9928600346153526788791 / 126105465359186048000 : ℝ) ≤ (64170821646338258583291379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1849837 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_36_1 : expNegUpper (1586906921941348567891 / 20176874457469767680 : ℝ) ≤ (34852557130795451642439851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (924321 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_36 : rowCell 6 36 ≤ (4881176762783680881766701 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (64170821646338258583291379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34852557130795451642439851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_36_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_36_1
  · norm_num [gridPoint]

theorem exp_6_37_0 : expNegUpper (1602043750436370502091 / 20369332396090183680 : ℝ) ≤ (69704935627453009655714653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (924321 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_37_1 : expNegUpper (20005033567559325546293 / 254616654951127296000 : ℝ) ≤ (75553167008150871481227467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1847479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_37 : rowCell 6 37 ≤ (10592351349514821687867779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (69704935627453009655714653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (75553167008150871481227467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_37_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_37_1
  · norm_num [gridPoint]

theorem exp_6_38_0 : expNegUpper (20194947299426655676837 / 257033798336760064000 : ℝ) ≤ (75552977020151416601089331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1847479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_38_1 : expNegUpper (40349573014132030301873 / 514067596673520128000 : ℝ) ≤ (40858842463385913669337399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1846347 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_38 : rowCell 6 38 ≤ (5734158983514992943469789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (75552977020151416601089331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40858842463385913669337399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_38_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_38_1
  · norm_num [gridPoint]

theorem exp_6_39_0 : expNegUpper (1629232555631396011537 / 20756988870021632000 : ℝ) ≤ (81717483275017986444984283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1846347 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_39_1 : expNegUpper (203456003389562492771 / 2594623608752704000 : ℝ) ≤ (88199834025178834831670061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (922623 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_39 : rowCell 6 39 ≤ (12390523437620114103075251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (81717483275017986444984283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (88199834025178834831670061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_39_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_39_1
  · norm_num [gridPoint]

theorem exp_6_40_0 : expNegUpper (5134232703630334510699 / 65475585641664576000 : ℝ) ≤ (2204990510588529556517687 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (922623 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_40_1 : expNegUpper (41034960118798702578631 / 523804685133316608000 : ℝ) ≤ (18999866495314924036863611 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (115261 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_40 : rowCell 6 40 ≤ (6679516119142845256041261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2204990510588529556517687 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18999866495314924036863611 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_40_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_40_1
  · norm_num [gridPoint]

theorem exp_6_41_0 : expNegUpper (41419047805965285474239 / 528707486821847552000 : ℝ) ≤ (94999106664960895187773407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (115261 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_41_1 : expNegUpper (4138086132912928910423 / 52870748682184755200 : ℝ) ≤ (102114382535741470284114377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28799 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_41 : rowCell 6 41 ≤ (56147237213537774399381 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (94999106664960895187773407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (102114382535741470284114377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_41_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_41_1
  · norm_num [gridPoint]

theorem exp_6_42_0 : expNegUpper (4176638241389137518343 / 53363312681613363200 : ℝ) ≤ (102114144282267059521077099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28799 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_42_1 : expNegUpper (41728914301242904860061 / 533633126816133632000 : ℝ) ≤ (109541611705781563479544639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (14737 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_42 : rowCell 6 42 ≤ (3086825577223355220328013 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (102114144282267059521077099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (109541611705781563479544639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_42_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_42_1
  · norm_num [gridPoint]

theorem exp_6_43_0 : expNegUpper (42115875445159591942229 / 538581605116174848000 : ℝ) ≤ (109541360808817173099861647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (14737 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_43_1 : expNegUpper (10519782256869549143797 / 134645401279043712000 : ℝ) ≤ (58638011998705343264334869 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1841143 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_43 : rowCell 6 43 ≤ (2067465935164287171181893 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (109541360808817173099861647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (58638011998705343264334869 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_43_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_43_1
  · norm_num [gridPoint]

theorem exp_6_44_0 : expNegUpper (424675368921085824797 / 5435529217219712000 : ℝ) ≤ (58637880143744314830126777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1841143 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_44_1 : expNegUpper (1697260620006952439147 / 21742116868878848000 : ℝ) ≤ (62655481015653303048035747 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (184019 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_44 : rowCell 6 44 ≤ (2211205217561860235493231 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (58637880143744314830126777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (62655481015653303048035747 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_44_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_44_1
  · norm_num [gridPoint]

theorem exp_6_45_0 : expNegUpper (42821376747076993524907 / 548547076633522688000 : ℝ) ≤ (7831917835804268452955089 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (184019 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_45_1 : expNegUpper (21393041855834197399793 / 274273538316761344000 : ℝ) ≤ (133638080631932993744053177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (919633 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_45 : rowCell 6 45 ≤ (9441388333176033715953099 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7831917835804268452955089 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (133638080631932993744053177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_45_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_45_1
  · norm_num [gridPoint]

theorem exp_6_46_0 : expNegUpper (21588702501201735903457 / 276782034925414656000 : ℝ) ≤ (26727558184980317262968019 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (919633 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_46_1 : expNegUpper (8628568730860118953397 / 110712813970165862400 : ℝ) ≤ (71123666224936767039980399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1838369 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_46 : rowCell 6 46 ≤ (20117791062029133803711111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26727558184980317262968019 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (71123666224936767039980399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_46_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_46_1
  · norm_num [gridPoint]

theorem exp_6_47_0 : expNegUpper (8707126330085332810957 / 111720780274778214400 : ℝ) ≤ (142247029631037214446504389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1838369 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_47_1 : expNegUpper (2718862832525566100621 / 34912743835868192000 : ℝ) ≤ (75563483015260332453943931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1837499 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_47 : rowCell 6 47 ≤ (5348273835460006935857379 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (142247029631037214446504389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (75563483015260332453943931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_47_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_47_1
  · norm_num [gridPoint]

theorem exp_6_48_0 : expNegUpper (2743504167717826062349 / 35229160700169248000 : ℝ) ≤ (75563325037356868887999163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1837499 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_48_1 : expNegUpper (43862978702332430057503 / 563666571202707968000 : ℝ) ≤ (80131768310792811587099327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1836657 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_48 : rowCell 6 48 ≤ (5676713044628752339236367 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (75563325037356868887999163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (80131768310792811587099327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_48_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_48_1
  · norm_num [gridPoint]

theorem exp_6_49_0 : expNegUpper (3727050113172023357 / 47894911944192000 : ℝ) ≤ (160263207542656417597479317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1836657 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_49_1 : expNegUpper (1862163107048815109 / 23947455972096000 : ℝ) ≤ (169641929882033248416079427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835841 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_49 : rowCell 6 49 ≤ (24056979020155275440330513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (160263207542656417597479317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (169641929882033248416079427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_49_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_49_1
  · norm_num [gridPoint]

theorem exp_6_50_0 : expNegUpper (719735514097790191681 / 9255813318993664000 : ℝ) ≤ (169641587733589766089817331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835841 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_50_1 : expNegUpper (1438451631708983570411 / 18511626637987328000 : ℝ) ≤ (89622699261227394619834467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835051 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_50 : rowCell 6 50 ≤ (12720576245471241694828159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (169641587733589766089817331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (89622699261227394619834467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_50_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_50_1
  · norm_num [gridPoint]

theorem exp_6_51_0 : expNegUpper (44990722016259507286189 / 578991610523689472000 : ℝ) ≤ (35849008679676209878879439 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835051 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_51_1 : expNegUpper (2247993453318923615927 / 28949580526184473600 : ℝ) ≤ (3781112235467192545081857 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114643 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_51 : rowCell 6 51 ≤ (26856814670243211001972071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35849008679676209878879439 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3781112235467192545081857 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_51_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_51_1
  · norm_num [gridPoint]

theorem exp_6_52_0 : expNegUpper (2268004525642298514967 / 29207281678776345600 : ℝ) ≤ (47263810952024434504513087 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114643 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_52_1 : expNegUpper (45329989234947950475211 / 584145633575526912000 : ℝ) ≤ (99526358722586952509017291 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1833549 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_52 : rowCell 6 52 ≤ (113204724901340026785733 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47263810952024434504513087 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (99526358722586952509017291 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_52_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_52_1
  · norm_num [gridPoint]

theorem exp_6_53_0 : expNegUpper (45731717356161027652739 / 589322494933119488000 : ℝ) ≤ (49763084203442250396962183 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1833549 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_53_1 : expNegUpper (22851185540512785940909 / 294661247466559744000 : ℝ) ≤ (104607708106814876744575719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458209 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_53 : rowCell 6 53 ≤ (29771251353817277773783867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (49763084203442250396962183 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (104607708106814876744575719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_53_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_53_1
  · norm_num [gridPoint]

theorem exp_6_54_0 : expNegUpper (922112250770866521509 / 11890443891929344000 : ℝ) ≤ (209215023131537061090767401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458209 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_54_1 : expNegUpper (1843080983877999330697 / 23780887783858688000 : ℝ) ≤ (6860032738700076052764027 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458037 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_54 : rowCell 6 54 ≤ (31263819473107570326815291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (209215023131537061090767401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6860032738700076052764027 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_54_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_54_1
  · norm_num [gridPoint]

theorem exp_6_55_0 : expNegUpper (46481786052331512296537 / 599744732565570048000 : ℝ) ≤ (13720040147566113306808491 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458037 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_55_1 : expNegUpper (5806744971882478920137 / 74968091570696256000 : ℝ) ≤ (229945687302907669385764199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (457871 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_55 : rowCell 6 55 ≤ (4096936072062740054739691 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13720040147566113306808491 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (229945687302907669385764199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_55_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_55_1
  · norm_num [gridPoint]

theorem exp_6_56_0 : expNegUpper (5857530986233029130633 / 75623763605053504000 : ℝ) ≤ (17964474228520707709843 / 78125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (457871 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_56_1 : expNegUpper (9366637321538752578379 / 120998021768085606400 : ℝ) ≤ (48092850870120335737603363 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (457711 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_56 : rowCell 6 56 ≤ (17151342579161382298073483 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17964474228520707709843 / 78125000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (48092850870120335737603363 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_56_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_56_1
  · norm_num [gridPoint]

theorem exp_6_57_0 : expNegUpper (9448201608696027010019 / 122051664684208230400 : ℝ) ≤ (24046382560544284066168633 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (457711 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_57_1 : expNegUpper (23607357543595212294443 / 305129161710520576000 : ℝ) ≤ (251050628589295249396349291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (457557 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_57 : rowCell 6 57 ≤ (4480209449362217764004343 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24046382560544284066168633 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (251050628589295249396349291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_57_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_57_1
  · norm_num [gridPoint]

theorem exp_6_58_0 : expNegUpper (23812038252758932520347 / 307774688153704704000 : ℝ) ≤ (251050188647319132032602451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (457557 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_58_1 : expNegUpper (47598555205888463181133 / 615549376307409408000 : ℝ) ≤ (52335555248223038716440079 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (365927 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_58 : rowCell 6 58 ≤ (9347145963423896369136461 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (251050188647319132032602451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (52335555248223038716440079 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_58_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_58_1
  · norm_num [gridPoint]

theorem exp_6_59_0 : expNegUpper (1920378530732642789837 / 24834530699981312000 : ℝ) ≤ (130838662754408007800364779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (365927 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_59_1 : expNegUpper (479847169561265253977 / 6208632674995328000 : ℝ) ≤ (54463576666574466182843003 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (365813 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_59 : rowCell 6 59 ≤ (38939410390056357932243581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (130838662754408007800364779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (54463576666574466182843003 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_59_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_59_1
  · norm_num [gridPoint]

theorem exp_6_60_0 : expNegUpper (12099294581053348973713 / 156549999249352832000 : ℝ) ≤ (27231742225121717335003929 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (365813 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_60_1 : expNegUpper (48373210330243257967651 / 626199996997411328000 : ℝ) ≤ (141471247825299879763196969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828519 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_60 : rowCell 6 60 ≤ (40490052079732980659000143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27231742225121717335003929 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (141471247825299879763196969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_60_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_60_1
  · norm_num [gridPoint]

theorem exp_6_61_0 : expNegUpper (48787231665548490216539 / 631559564801044992000 : ℝ) ≤ (2829420246933179784931261 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828519 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_61_1 : expNegUpper (975280906411546152401 / 12631191296020899840 : ℝ) ≤ (146761332061799691824856947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (913997 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_61 : rowCell 6 61 ≤ (42036323026023472996648443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2829420246933179784931261 / 10000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (146761332061799691824856947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_61_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_61_1
  · norm_num [gridPoint]

theorem exp_6_62_0 : expNegUpper (983592665693199988801 / 12738839418208675840 : ℝ) ≤ (293522183795297538258968939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (913997 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_62_1 : expNegUpper (49157231919467321083961 / 636941970910433792000 : ℝ) ≤ (304029094457980019733834569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456873 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_62 : rowCell 6 62 ≤ (43573976072705555207891241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (293522183795297538258968939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (304029094457980019733834569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_62_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_62_1
  · norm_num [gridPoint]

theorem exp_6_63_0 : expNegUpper (49574393173886570294449 / 642347215325577728000 : ℝ) ≤ (304028605292097223548337739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456873 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_63_1 : expNegUpper (774262189363311642007 / 10036675239462152000 : ℝ) ≤ (314432299807697390592750249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456753 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_63 : rowCell 6 63 ≤ (45098724848346448859891779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (304028605292097223548337739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (314432299807697390592750249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_63_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_63_1
  · norm_num [gridPoint]

theorem sum_6_32_2 : blockSum (rowCell 6) 32 2 ≤ (14432774812424264237218927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_32) (by simpa only [blockSum_one] using cell_6_33) (by norm_num)

theorem sum_6_34_2 : blockSum (rowCell 6) 34 2 ≤ (8608043856227023382476571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_34) (by simpa only [blockSum_one] using cell_6_35) (by norm_num)

theorem sum_6_32_4 : blockSum (rowCell 6) 32 4 ≤ (31648862524878311002172069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_32_2 sum_6_34_2 (by norm_num)

theorem sum_6_36_2 : blockSum (rowCell 6) 36 2 ≤ (20354704875082183451401181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_36) (by simpa only [blockSum_one] using cell_6_37) (by norm_num)

theorem sum_6_38_2 : blockSum (rowCell 6) 38 2 ≤ (23858841404650099990014829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_38) (by simpa only [blockSum_one] using cell_6_39) (by norm_num)

theorem sum_6_36_4 : blockSum (rowCell 6) 36 4 ≤ (4421354627973228344141601 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_36_2 sum_6_38_2 (by norm_num)

theorem sum_6_32_8 : blockSum (rowCell 6) 32 8 ≤ (75862408804610594443588079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_32_4 sum_6_36_4 (by norm_num)

theorem sum_6_40_2 : blockSum (rowCell 6) 40 2 ≤ (13866362482475680379162029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_40) (by simpa only [blockSum_one] using cell_6_41) (by norm_num)

theorem sum_6_42_2 : blockSum (rowCell 6) 42 2 ≤ (31973855367431073471095209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_42) (by simpa only [blockSum_one] using cell_6_43) (by norm_num)

theorem sum_6_40_4 : blockSum (rowCell 6) 40 4 ≤ (59706580332382434229419267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_40_2 sum_6_42_2 (by norm_num)

theorem sum_6_44_2 : blockSum (rowCell 6) 44 2 ≤ (18286209203423474657926023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_44) (by simpa only [blockSum_one] using cell_6_45) (by norm_num)

theorem sum_6_46_2 : blockSum (rowCell 6) 46 2 ≤ (41510886403869161547140627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_46) (by simpa only [blockSum_one] using cell_6_47) (by norm_num)

theorem sum_6_44_4 : blockSum (rowCell 6) 44 4 ≤ (78083304810716110862992673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_44_2 sum_6_46_2 (by norm_num)

theorem sum_6_40_8 : blockSum (rowCell 6) 40 8 ≤ (6889494257154927254620597 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_40_4 sum_6_44_4 (by norm_num)

theorem sum_6_32_16 : blockSum (rowCell 6) 32 16 ≤ (213652293947709139536000019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_32_8 sum_6_40_8 (by norm_num)

theorem sum_6_48_2 : blockSum (rowCell 6) 48 2 ≤ (46763831198670284797275981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_48) (by simpa only [blockSum_one] using cell_6_49) (by norm_num)

theorem sum_6_50_2 : blockSum (rowCell 6) 50 2 ≤ (52297967161185694391628389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_50) (by simpa only [blockSum_one] using cell_6_51) (by norm_num)

theorem sum_6_48_4 : blockSum (rowCell 6) 48 4 ≤ (9906179835985597918890437 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_48_2 sum_6_50_2 (by norm_num)

theorem sum_6_52_2 : blockSum (rowCell 6) 52 2 ≤ (58072432579152284470217117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_52) (by simpa only [blockSum_one] using cell_6_53) (by norm_num)

theorem sum_6_54_2 : blockSum (rowCell 6) 54 2 ≤ (64039308049609490764732819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_54) (by simpa only [blockSum_one] using cell_6_55) (by norm_num)

theorem sum_6_52_4 : blockSum (rowCell 6) 52 4 ≤ (7631983789297610952184371 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_52_2 sum_6_54_2 (by norm_num)

theorem sum_6_48_8 : blockSum (rowCell 6) 48 8 ≤ (110586769494308877211927153 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_48_4 sum_6_52_4 (by norm_num)

theorem sum_6_56_2 : blockSum (rowCell 6) 56 2 ≤ (7014436075322050670818171 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_56) (by simpa only [blockSum_one] using cell_6_57) (by norm_num)

theorem sum_6_58_2 : blockSum (rowCell 6) 58 2 ≤ (3053119769750077736351577 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_58) (by simpa only [blockSum_one] using cell_6_59) (by norm_num)

theorem sum_6_56_4 : blockSum (rowCell 6) 56 4 ≤ (29294470999394490023394227 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_56_2 sum_6_58_2 (by norm_num)

theorem sum_6_60_2 : blockSum (rowCell 6) 60 2 ≤ (41263187552878226827824293 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_60) (by simpa only [blockSum_one] using cell_6_61) (by norm_num)

theorem sum_6_62_2 : blockSum (rowCell 6) 62 2 ≤ (4433635046052600203389151 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_62) (by simpa only [blockSum_one] using cell_6_63) (by norm_num)

theorem sum_6_60_4 : blockSum (rowCell 6) 60 4 ≤ (85599538013404228861715803 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_60_2 sum_6_62_2 (by norm_num)

theorem sum_6_56_8 : blockSum (rowCell 6) 56 8 ≤ (317671431023780907840402741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_56_4 sum_6_60_4 (by norm_num)

theorem sum_6_48_16 : blockSum (rowCell 6) 48 16 ≤ (538844970012398662264257047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_48_8 sum_6_56_8 (by norm_num)

theorem sum_6_32_32 : blockSum (rowCell 6) 32 32 ≤ (376248631980053900900128533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_32_16 sum_6_48_16 (by norm_num)

#print axioms sum_6_32_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
