import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_32_0 : expNegUpper (235225264237625881427 / 3033777816451587200 : ℝ) ≤ (212434547905221505561720609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1832617 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_32_1 : expNegUpper (37595181275736175174511 / 485404450632253952000 : ℝ) ≤ (7221605660366198063434083 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1831413 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_32 : rowCell 4 32 ≤ (32342309225700522520341021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (212434547905221505561720609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7221605660366198063434083 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_32_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_32_1
  · norm_num [gridPoint]

theorem exp_4_33_0 : expNegUpper (1650467820171570699953 / 21309762864119296000 : ℝ) ≤ (46218152381407711137706567 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1831413 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_33_1 : expNegUpper (824360592365951002273 / 10654881432059648000 : ℝ) ≤ (250829804043581532465422127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11439 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_33 : rowCell 4 33 ≤ (35142080644627688088421847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (46218152381407711137706567 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (250829804043581532465422127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_33_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_33_1
  · norm_num [gridPoint]

theorem exp_4_34_0 : expNegUpper (765750918843328353151 / 9897349588459776000 : ℝ) ≤ (125414572390445672877323047 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11439 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_34_1 : expNegUpper (1529922601800206897293 / 19794699176919552000 : ℝ) ≤ (54332079968432908395718091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (18291 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_34 : rowCell 4 34 ≤ (7620081403622696522056349 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (125414572390445672877323047 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (54332079968432908395718091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_34_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_34_1
  · norm_num [gridPoint]

theorem exp_4_35_0 : expNegUpper (38616410505019662433277 / 499633251276988928000 : ℝ) ≤ (135829849709238325307539849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (18291 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_35_1 : expNegUpper (9644406164147275221719 / 124908312819247232000 : ℝ) ≤ (36698551056065708954560289 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1827991 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_35 : rowCell 4 35 ≤ (103045999664396802746207 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (135829849709238325307539849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36698551056065708954560289 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_35_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_35_1
  · norm_num [gridPoint]

theorem exp_4_36_0 : expNegUpper (9736840886211126788791 / 126105465359186048000 : ℝ) ≤ (36698458228185698028776821 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1827991 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_36_1 : expNegUpper (1556371043036967127891 / 20176874457469767680 : ℝ) ≤ (316614029364855837851542881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1826913 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_36 : rowCell 4 36 ≤ (8899291168273043814114631 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36698458228185698028776821 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (316614029364855837851542881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_36_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_36_1
  · norm_num [gridPoint]

theorem exp_4_37_0 : expNegUpper (1571216602159183942091 / 20369332396090183680 : ℝ) ≤ (247354096560226021176671 / 781250000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1826913 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_37_1 : expNegUpper (19621514647674525546293 / 254616654951127296000 : ℝ) ≤ (68146434670957182596809563 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912933 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_37 : rowCell 4 37 ≤ (5991777298487972968671183 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (247354096560226021176671 / 781250000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (68146434670957182596809563 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_37_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_37_1
  · norm_num [gridPoint]

theorem exp_4_38_0 : expNegUpper (19807787512381791676837 / 257033798336760064000 : ℝ) ≤ (170365671798937012754436159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912933 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_38_1 : expNegUpper (39578894307202366301873 / 514067596673520128000 : ℝ) ≤ (91483061678400278200183863 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114053 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_38 : rowCell 4 38 ≤ (25765271949291093775740587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (170365671798937012754436159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (91483061678400278200183863 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_38_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_38_1
  · norm_num [gridPoint]

theorem exp_4_39_0 : expNegUpper (1598114137981404331537 / 20756988870021632000 : ℝ) ≤ (182965686115804985736621031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114053 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_39_1 : expNegUpper (199584405519113852771 / 2594623608752704000 : ℝ) ≤ (78439594246030156690020431 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91193 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_39 : rowCell 4 39 ≤ (107975532923952364599001 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (182965686115804985736621031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (78439594246030156690020431 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_39_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_39_1
  · norm_num [gridPoint]

theorem exp_4_40_0 : expNegUpper (5036532540079102510699 / 65475585641664576000 : ℝ) ≤ (392197051402646240884384367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91193 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_40_1 : expNegUpper (40256999677548910578631 / 523804685133316608000 : ℝ) ≤ (26219202663390400158549017 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822901 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_40 : rowCell 4 40 ≤ (59190206385288467360255941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (392197051402646240884384367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26219202663390400158549017 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_40_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_40_1
  · norm_num [gridPoint]

theorem exp_4_41_0 : expNegUpper (40633805630395365474239 / 528707486821847552000 : ℝ) ≤ (104876569235682157519336479 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822901 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_41_1 : expNegUpper (4059926002071943310423 / 52870748682184755200 : ℝ) ≤ (447832029795316635630533991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821971 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_41 : rowCell 4 41 ≤ (63247088576598220737962013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (104876569235682157519336479 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (447832029795316635630533991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_41_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_41_1
  · norm_num [gridPoint]

theorem exp_4_42_0 : expNegUpper (4097749937116139118343 / 53363312681613363200 : ℝ) ≤ (22391550895450719153553043 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821971 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_42_1 : expNegUpper (40943672125672984860061 / 533633126816133632000 : ℝ) ≤ (95427663419008786437550833 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821069 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_42 : rowCell 4 42 ≤ (67449594935632850057315407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22391550895450719153553043 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (95427663419008786437550833 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_42_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_42_1
  · norm_num [gridPoint]

theorem exp_4_43_0 : expNegUpper (41323351535269543942229 / 538581605116174848000 : ℝ) ≤ (59642157344501759842193963 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821069 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_43_1 : expNegUpper (10322561496187053143797 / 134645401279043712000 : ℝ) ≤ (5073860908441920617830707 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (364039 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_43 : rowCell 4 43 ≤ (448702044909649613762301 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (59642157344501759842193963 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5073860908441920617830707 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_43_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_43_1
  · norm_num [gridPoint]

theorem exp_4_44_0 : expNegUpper (416713721150584704797 / 5435529217219712000 : ℝ) ≤ (507384985951676399596301413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (364039 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_44_1 : expNegUpper (1665559663611350519147 / 21742116868878848000 : ℝ) ≤ (269264685778918886031737537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454837 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_44 : rowCell 4 44 ≤ (76269014638274348351569503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (507384985951676399596301413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (269264685778918886031737537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_44_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_44_1
  · norm_num [gridPoint]

theorem exp_4_45_0 : expNegUpper (42021571102866817524907 / 548547076633522688000 : ℝ) ≤ (134632055037958953400907509 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454837 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_45_1 : expNegUpper (20994959467309141399793 / 274273538316761344000 : ℝ) ≤ (570516292310063843258290061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (56829 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_45 : rowCell 4 45 ≤ (5054532640993805497896511 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (134632055037958953400907509 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (570516292310063843258290061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_45_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_45_1
  · norm_num [gridPoint]

theorem exp_4_46_0 : expNegUpper (21186979245516615903457 / 276782034925414656000 : ℝ) ≤ (570515094574087710901653209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (56829 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_46_1 : expNegUpper (8468607602018083753397 / 110712813970165862400 : ℝ) ≤ (301644611732698215847395029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908867 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_46 : rowCell 4 46 ≤ (2674839545664255383661469 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (570515094574087710901653209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (301644611732698215847395029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_46_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_46_1
  · norm_num [gridPoint]

theorem exp_4_47_0 : expNegUpper (8545708854379272010957 / 111720780274778214400 : ℝ) ≤ (603287979728381476200140541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908867 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_47_1 : expNegUpper (2668647425564926100621 / 34912743835868192000 : ℝ) ≤ (636784943436523954663907667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_47 : rowCell 4 47 ≤ (45213615842600904994164719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (603287979728381476200140541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (636784943436523954663907667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_47_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_47_1
  · norm_num [gridPoint]

theorem exp_4_48_0 : expNegUpper (2692833652362178062349 / 35229160700169248000 : ℝ) ≤ (15919591354346913997253861 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_48_1 : expNegUpper (43055891323802126057503 / 563666571202707968000 : ℝ) ≤ (335467427326379002292646613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908113 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_48 : rowCell 4 48 ≤ (19072001713397193274208233 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15919591354346913997253861 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (335467427326379002292646613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_48_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_48_1
  · norm_num [gridPoint]

theorem exp_4_49_0 : expNegUpper (69510961569707752583 / 910003326939648000 : ℝ) ≤ (335466760243264984840555771 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908113 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_49_1 : expNegUpper (34732516437375192671 / 455001663469824000 : ℝ) ≤ (176416310861952933336783517 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181551 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_49 : rowCell 4 49 ≤ (20076563730808833848988697 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (335466760243264984840555771 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (176416310861952933336783517 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_49_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_49_1
  · norm_num [gridPoint]

theorem exp_4_50_0 : expNegUpper (706541804742782191681 / 9255813318993664000 : ℝ) ≤ (705663865145998581796283679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181551 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_50_1 : expNegUpper (1412181660326711570411 / 18511626637987328000 : ℝ) ≤ (740897582115078118628660323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1814819 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_50 : rowCell 4 50 ≤ (21096912075865597323716991 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (705663865145998581796283679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (740897582115078118628660323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_50_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_50_1
  · norm_num [gridPoint]

theorem exp_4_51_0 : expNegUpper (44169071169088947286189 / 578991610523689472000 : ℝ) ≤ (148179232118009313879448901 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1814819 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_51_1 : expNegUpper (2207092954318398815927 / 28949580526184473600 : ℝ) ≤ (97068608867458608550878267 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1814153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_51 : rowCell 4 51 ≤ (27663363757166841175850267 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (148179232118009313879448901 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (97068608867458608550878267 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_51_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_51_1
  · norm_num [gridPoint]

theorem exp_4_52_0 : expNegUpper (2226739939925767314967 / 29207281678776345600 : ℝ) ≤ (38827370362286321246832581 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1814153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_52_1 : expNegUpper (44508338387777390475211 / 584145633575526912000 : ℝ) ≤ (812532017604592954445537091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1813511 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_52 : rowCell 4 52 ≤ (23175419869726210620673323 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38827370362286321246832581 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (812532017604592954445537091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_52_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_52_1
  · norm_num [gridPoint]

theorem exp_4_53_0 : expNegUpper (44902784774670339652739 / 589322494933119488000 : ℝ) ≤ (812530512934720034122767883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1813511 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_53_1 : expNegUpper (22438539683347473940909 / 294661247466559744000 : ℝ) ≤ (848756250988689604499747891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812893 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_53 : rowCell 4 53 ≤ (121142523387621993286701051 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (812530512934720034122767883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (848756250988689604499747891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_53_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_53_1
  · norm_num [gridPoint]

theorem exp_4_54_0 : expNegUpper (905460781797851481509 / 11890443891929344000 : ℝ) ≤ (33950188266818470489003413 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812893 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_54_1 : expNegUpper (1809923680618371810697 / 23780887783858688000 : ℝ) ≤ (442563783015401027953666003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812299 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_54 : rowCell 4 54 ≤ (31609063277557634414981869 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33950188266818470489003413 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (442563783015401027953666003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_54_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_54_1
  · norm_num [gridPoint]

theorem exp_4_55_0 : expNegUpper (45645571736520696296537 / 599744732565570048000 : ℝ) ≤ (885125983521536575164178069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812299 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_55_1 : expNegUpper (5702673290801134920137 / 74968091570696256000 : ℝ) ≤ (921549196032086899575450423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (113233 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_55 : rowCell 4 55 ≤ (131744377277781853986604297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (885125983521536575164178069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (921549196032086899575450423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_55_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_55_1
  · norm_num [gridPoint]

theorem exp_4_56_0 : expNegUpper (250110829928768223071 / 3287989721958848000 : ℝ) ≤ (921547576913254265438955439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (113233 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_56_1 : expNegUpper (399973672103329972973 / 5260783555134156800 : ℝ) ≤ (478961054254769927119661943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (90559 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_56 : rowCell 4 56 ≤ (137052618047075644248532027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (921547576913254265438955439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (478961054254769927119661943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_56_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_56_1
  · norm_num [gridPoint]

theorem exp_4_57_0 : expNegUpper (9279502398669838210019 / 122051664684208230400 : ℝ) ≤ (38316818179219453040820377 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (90559 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_57_1 : expNegUpper (23187429952109772294443 / 305129161710520576000 : ℝ) ≤ (994145520501330229375746597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (362131 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_57 : rowCell 4 57 ≤ (71173202352474230472653239 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38316818179219453040820377 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (994145520501330229375746597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_57_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_57_1
  · norm_num [gridPoint]

theorem exp_4_58_0 : expNegUpper (23388469794113428520347 / 307774688153704704000 : ℝ) ≤ (198828766674472569201430173 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (362131 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_58_1 : expNegUpper (46755059155757519181133 / 615549376307409408000 : ℝ) ≤ (1030117429060209954318636913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226269 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_58 : rowCell 4 58 ≤ (73805474964405587682190869 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (198828766674472569201430173 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1030117429060209954318636913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_58_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_58_1
  · norm_num [gridPoint]

theorem exp_4_59_0 : expNegUpper (1886347419354599909837 / 24834530699981312000 : ℝ) ≤ (1030115710745099792421751801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226269 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_59_1 : expNegUpper (471375800388355173977 / 6208632674995328000 : ℝ) ≤ (133216894069527323791644389 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226209 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_59 : rowCell 4 59 ≤ (152831327942942133748722319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1030115710745099792421751801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (133216894069527323791644389 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_59_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_59_1
  · norm_num [gridPoint]

theorem exp_4_60_0 : expNegUpper (11885689918150564973713 / 156549999249352832000 : ℝ) ≤ (53286670253209096097053999 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226209 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_60_1 : expNegUpper (47522432545792185967651 / 626199996997411328000 : ℝ) ≤ (220179175668910425093450743 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1809213 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_60 : rowCell 4 60 ≤ (39498138481790424817877853 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (53286670253209096097053999 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (220179175668910425093450743 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_60_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_60_1
  · norm_num [gridPoint]

theorem exp_4_61_0 : expNegUpper (47929172146777290216539 / 631559564801044992000 : ℝ) ≤ (275223525942943066978721401 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1809213 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_61_1 : expNegUpper (958192533379323432401 / 12631191296020899840 : ℝ) ≤ (56774860616925826718123527 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72351 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_61 : rowCell 4 61 ≤ (163079664028585327299660607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (275223525942943066978721401 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (56774860616925826718123527 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_61_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_61_1
  · norm_num [gridPoint]

theorem exp_4_62_0 : expNegUpper (966358657974574708801 / 12738839418208675840 : ℝ) ≤ (283873853214817909153061869 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72351 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_62_1 : expNegUpper (48299172400696121083961 / 636941970910433792000 : ℝ) ≤ (1169437726059998569657119359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1808359 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_62 : rowCell 4 62 ≤ (6723111813134407248919527 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (283873853214817909153061869 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1169437726059998569657119359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_62_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_62_1
  · norm_num [gridPoint]

theorem exp_4_63_0 : expNegUpper (48709051920795242294449 / 642347215325577728000 : ℝ) ≤ (292358975979365583538073201 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1808359 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_63_1 : expNegUpper (760798120833135642007 / 10036675239462152000 : ℝ) ≤ (601308748409640636192913943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451991 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_63 : rowCell 4 63 ≤ (2162153314043132102585547 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (292358975979365583538073201 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (601308748409640636192913943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_63_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_63_1
  · norm_num [gridPoint]

theorem sum_4_32_2 : blockSum (rowCell 4) 32 2 ≤ (16871097467582052652190717 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_32) (by simpa only [blockSum_one] using cell_4_33) (by norm_num)

theorem sum_4_34_2 : blockSum (rowCell 4) 34 2 ≤ (15863761376774440741752909 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_34) (by simpa only [blockSum_one] using cell_4_35) (by norm_num)

theorem sum_4_32_4 : blockSum (rowCell 4) 32 4 ≤ (146803196754200414317527413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_32_2 sum_4_34_2 (by norm_num)

theorem sum_4_36_2 : blockSum (rowCell 4) 36 2 ≤ (92430674229269002819942619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_36) (by simpa only [blockSum_one] using cell_4_37) (by norm_num)

theorem sum_4_38_2 : blockSum (rowCell 4) 38 2 ≤ (53407008377822899113084843 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_38) (by simpa only [blockSum_one] using cell_4_39) (by norm_num)

theorem sum_4_36_4 : blockSum (rowCell 4) 36 4 ≤ (39848938196982960209222461 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_36_2 sum_4_38_2 (by norm_num)

theorem sum_4_32_8 : blockSum (rowCell 4) 32 8 ≤ (173023943869557607681819859 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_32_4 sum_4_36_4 (by norm_num)

theorem sum_4_40_2 : blockSum (rowCell 4) 40 2 ≤ (61218647480943344049108977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_40) (by simpa only [blockSum_one] using cell_4_41) (by norm_num)

theorem sum_4_42_2 : blockSum (rowCell 4) 42 2 ≤ (139241922121176788259283567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_42) (by simpa only [blockSum_one] using cell_4_43) (by norm_num)

theorem sum_4_40_4 : blockSum (rowCell 4) 40 4 ≤ (261679217083063476357501521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_40_2 sum_4_42_2 (by norm_num)

theorem sum_4_44_2 : blockSum (rowCell 4) 44 2 ≤ (157141536894175236317913679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_44) (by simpa only [blockSum_one] using cell_4_45) (by norm_num)

theorem sum_4_46_2 : blockSum (rowCell 4) 46 2 ≤ (88011048573228991132748223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_46) (by simpa only [blockSum_one] using cell_4_47) (by norm_num)

theorem sum_4_44_4 : blockSum (rowCell 4) 44 4 ≤ (2665309072325065748667281 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_44_2 sum_4_46_2 (by norm_num)

theorem sum_4_40_8 : blockSum (rowCell 4) 40 8 ≤ (297421425561848347470455823 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_40_4 sum_4_44_4 (by norm_num)

theorem sum_4_32_16 : blockSum (rowCell 4) 32 16 ≤ (235222684715702977576137841 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_32_8 sum_4_40_8 (by norm_num)

theorem sum_4_48_2 : blockSum (rowCell 4) 48 2 ≤ (3914856544420602712319693 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_48) (by simpa only [blockSum_one] using cell_4_49) (by norm_num)

theorem sum_4_50_2 : blockSum (rowCell 4) 50 2 ≤ (216138015407995351321986023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_50) (by simpa only [blockSum_one] using cell_4_51) (by norm_num)

theorem sum_4_48_4 : blockSum (rowCell 4) 48 4 ≤ (411880842629025486937970673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_48_2 sum_4_50_2 (by norm_num)

theorem sum_4_52_2 : blockSum (rowCell 4) 52 2 ≤ (118509811368126523195033833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_52) (by simpa only [blockSum_one] using cell_4_53) (by norm_num)

theorem sum_4_54_2 : blockSum (rowCell 4) 54 2 ≤ (258180630388012391646531773 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_54) (by simpa only [blockSum_one] using cell_4_55) (by norm_num)

theorem sum_4_52_4 : blockSum (rowCell 4) 52 4 ≤ (495200253124265438036599439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_52_2 sum_4_54_2 (by norm_num)

theorem sum_4_48_8 : blockSum (rowCell 4) 48 8 ≤ (7086571060572585351363829 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_48_4 sum_4_52_4 (by norm_num)

theorem sum_4_56_2 : blockSum (rowCell 4) 56 2 ≤ (55879804550404821038767701 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_56) (by simpa only [blockSum_one] using cell_4_57) (by norm_num)

theorem sum_4_58_2 : blockSum (rowCell 4) 58 2 ≤ (300442277871753309113104057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_58) (by simpa only [blockSum_one] using cell_4_59) (by norm_num)

theorem sum_4_56_4 : blockSum (rowCell 4) 56 4 ≤ (289920650311888707153471281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_56_2 sum_4_58_2 (by norm_num)

theorem sum_4_60_2 : blockSum (rowCell 4) 60 2 ≤ (321072217955747026571172019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_60) (by simpa only [blockSum_one] using cell_4_61) (by norm_num)

theorem sum_4_62_2 : blockSum (rowCell 4) 62 2 ≤ (68210012090362149885966387 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_62) (by simpa only [blockSum_one] using cell_4_63) (by norm_num)

theorem sum_4_60_4 : blockSum (rowCell 4) 60 4 ≤ (331061139203778888000501977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_60_2 sum_4_62_2 (by norm_num)

theorem sum_4_56_8 : blockSum (rowCell 4) 56 8 ≤ (310490894757833797576986629 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_56_4 sum_4_60_4 (by norm_num)

theorem sum_4_48_16 : blockSum (rowCell 4) 48 16 ≤ (537261168696156528820629157 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_48_8 sum_4_56_8 (by norm_num)

theorem sum_4_32_32 : blockSum (rowCell 4) 32 32 ≤ (386241926705929753198383499 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_32_16 sum_4_48_16 (by norm_num)

#print axioms sum_4_32_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
