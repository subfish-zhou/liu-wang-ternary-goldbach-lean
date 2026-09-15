import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_32_0 : expNegUpper (232089954357920281427 / 3033777816451587200 : ℝ) ≤ (298554935737346629795229131 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817881 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_32_1 : expNegUpper (37095958939756655174511 / 485404450632253952000 : ℝ) ≤ (646310454400210043609568557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454189 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_32 : rowCell 3 32 ≤ (3626853091929879084111297 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (298554935737346629795229131 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (646310454400210043609568557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_32_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_32_1
  · norm_num [gridPoint]

theorem exp_3_33_0 : expNegUpper (37456683038419854098919 / 490124545874743808000 : ℝ) ≤ (646308760216955913588236063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454189 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_33_1 : expNegUpper (18709468834040425052279 / 245062272937371904000 : ℝ) ≤ (139609777559791649748499911 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (113479 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_33 : rowCell 3 33 ≤ (98031767514644850015037461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (646308760216955913588236063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (139609777559791649748499911 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_33_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_33_1
  · norm_num [gridPoint]

theorem exp_3_34_0 : expNegUpper (83957870826370599239 / 1099705509828864000 : ℝ) ≤ (349023546491559745503217971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (113479 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_34_1 : expNegUpper (167751058753239557477 / 2199411019657728000 : ℝ) ≤ (376160268072658908975946811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (907301 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_34 : rowCell 3 34 ≤ (330506595564726386405113 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (349023546491559745503217971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (376160268072658908975946811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_34_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_34_1
  · norm_num [gridPoint]

theorem exp_3_35_0 : expNegUpper (38107479189946638433277 / 499633251276988928000 : ℝ) ≤ (752318638600243761189163307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (907301 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_35_1 : expNegUpper (9517780146572363221719 / 124908312819247232000 : ℝ) ≤ (202276622512221844546489919 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1813571 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_35 : rowCell 3 35 ≤ (113860523223983663386992001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (752318638600243761189163307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (202276622512221844546489919 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_35_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_35_1
  · norm_num [gridPoint]

theorem exp_3_36_0 : expNegUpper (9609001246249526788791 / 126105465359186048000 : ℝ) ≤ (161820897585971664840266897 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1813571 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_36_1 : expNegUpper (1536013790434046167891 / 20176874457469767680 : ℝ) ≤ (217093675274754141677636383 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812569 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_36 : rowCell 3 36 ≤ (24464657914838890035015819 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (161820897585971664840266897 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (217093675274754141677636383 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_36_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_36_1
  · norm_num [gridPoint]

theorem exp_3_37_0 : expNegUpper (172296129997154766899 / 2263259155121131520 : ℝ) ≤ (43418629641528053907916167 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812569 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_37_1 : expNegUpper (2151759485305702838477 / 28290739439014144000 : ℝ) ≤ (930079609439105930478646181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1811597 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_37 : rowCell 3 37 ≤ (13114475038640459492376089 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43418629641528053907916167 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (930079609439105930478646181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_37_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_37_1
  · norm_num [gridPoint]

theorem exp_3_38_0 : expNegUpper (19549680987685215676837 / 257033798336760064000 : ℝ) ≤ (465038696865485498443856687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (905799 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_38_1 : expNegUpper (39065108502582590301873 / 514067596673520128000 : ℝ) ≤ (994161866059920198971669067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (362131 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_38 : rowCell 3 38 ≤ (35079313908165438595218737 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (465038696865485498443856687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (994161866059920198971669067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_38_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_38_1
  · norm_num [gridPoint]

theorem exp_3_39_0 : expNegUpper (1577368526214743211537 / 20756988870021632000 : ℝ) ≤ (994159541921543416524526037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (362131 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_39_1 : expNegUpper (197003340272148092771 / 2594623608752704000 : ℝ) ≤ (1060548154983116485447596263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1809741 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_39 : rowCell 3 39 ≤ (149831131284734237832187837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (994159541921543416524526037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1060548154983116485447596263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_39_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_39_1
  · norm_num [gridPoint]

theorem exp_3_40_0 : expNegUpper (552377677523512723411 / 7275065071296064000 : ℝ) ≤ (1060545721736462936492882001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1809741 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_40_1 : expNegUpper (4415373264820264730959 / 58200520570368512000 : ℝ) ≤ (1129151119492367760725213371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (361771 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_40 : rowCell 3 40 ≤ (159674660968162125968723047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1060545721736462936492882001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1129151119492367760725213371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_40_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_40_1
  · norm_num [gridPoint]

theorem exp_3_41_0 : expNegUpper (40110310846682085474239 / 528707486821847552000 : ℝ) ≤ (1129148576783009364454210693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (361771 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_41_1 : expNegUpper (4007819248177952910423 / 52870748682184755200 : ℝ) ≤ (1199869395493341574535024697 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451999 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_41 : rowCell 3 41 ≤ (169834083015475977505141793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1129148576783009364454210693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1199869395493341574535024697 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_41_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_41_1
  · norm_num [gridPoint]

theorem exp_3_42_0 : expNegUpper (4045157734267473518343 / 53363312681613363200 : ℝ) ≤ (599933371649836545607448991 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451999 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_42_1 : expNegUpper (40420177341959704860061 / 533633126816133632000 : ℝ) ≤ (636293876980255473950579329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (361433 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_42 : rowCell 3 42 ≤ (90146801643025001164470247 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (599933371649836545607448991 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (636293876980255473950579329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_42_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_42_1
  · norm_num [gridPoint]

theorem exp_3_43_0 : expNegUpper (4532778029112167993581 / 59842400568463872000 : ℝ) ≤ (1272584992601014330702081681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (361433 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_43_1 : expNegUpper (1132342332118376571533 / 14960600142115968000 : ℝ) ≤ (1347177353274100240165131943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_43 : rowCell 3 43 ≤ (191035423953945976680884481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1272584992601014330702081681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1347177353274100240165131943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_43_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_43_1
  · norm_num [gridPoint]

theorem exp_3_44_0 : expNegUpper (411405955970250624797 / 5435529217219712000 : ℝ) ≤ (67358724170629370235286471 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_44_1 : expNegUpper (1644425692680949239147 / 21742116868878848000 : ℝ) ≤ (1423496101080530198407034629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112849 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_44 : rowCell 3 44 ≤ (101019894147795695577164651 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (67358724170629370235286471 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1423496101080530198407034629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_44_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_44_1
  · norm_num [gridPoint]

theorem exp_3_45_0 : expNegUpper (41488367340060033524907 / 548547076633522688000 : ℝ) ≤ (284698624745862655417016557 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112849 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_45_1 : expNegUpper (20729571208292437399793 / 274273538316761344000 : ℝ) ≤ (375347281035181136192963251 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804833 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_45 : rowCell 3 45 ≤ (213285041338577728706913333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (284698624745862655417016557 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (375347281035181136192963251 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_45_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_45_1
  · norm_num [gridPoint]

theorem exp_3_46_0 : expNegUpper (2324351526858503989273 / 30753559436157184000 : ℝ) ≤ (300277208132336412771019723 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804833 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_46_1 : expNegUpper (929107427717414105933 / 12301423774462873600 : ℝ) ≤ (395172335869644076433788341 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804107 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_46 : rowCell 3 46 ≤ (28093463257951322352987513 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (300277208132336412771019723 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (395172335869644076433788341 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_46_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_46_1
  · norm_num [gridPoint]

theorem exp_3_47_0 : expNegUpper (8438097203908564810957 / 111720780274778214400 : ℝ) ≤ (1580686155582103221822840803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804107 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_47_1 : expNegUpper (2635170487591166100621 / 34912743835868192000 : ℝ) ≤ (1661218151022282217409505287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1803407 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_47 : rowCell 3 47 ≤ (118201287342996125553182869 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1580686155582103221822840803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1661218151022282217409505287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_47_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_47_1
  · norm_num [gridPoint]

theorem exp_3_48_0 : expNegUpper (2659053308791746062349 / 35229160700169248000 : ℝ) ≤ (1661214860764131134446359663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1803407 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_48_1 : expNegUpper (42517833071448590057503 / 563666571202707968000 : ℝ) ≤ (174278618285896168985404743 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (450683 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_48 : rowCell 3 48 ≤ (124111407191591779435222509 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1661214860764131134446359663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (174278618285896168985404743 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_48_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_48_1
  · norm_num [gridPoint]

theorem exp_3_49_0 : expNegUpper (7626922353629699087 / 101111480771072000 : ℝ) ≤ (8713913963175008073029627 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (450683 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_49_1 : expNegUpper (3811125337741518119 / 50555740385536000 : ℝ) ≤ (1825194183211865391423387071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1802081 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_49 : rowCell 3 49 ≤ (52036017336613555899846639 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8713913963175008073029627 / 5000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1825194183211865391423387071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_49_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_49_1
  · norm_num [gridPoint]

theorem exp_3_50_0 : expNegUpper (697745998506110191681 / 9255813318993664000 : ℝ) ≤ (182519069575080285172966407 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1802081 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_50_1 : expNegUpper (1394668346071863570411 / 18511626637987328000 : ℝ) ≤ (477058488078070959011229013 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (360291 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_50 : rowCell 3 50 ≤ (27224467958546752545196843 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (182519069575080285172966407 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (477058488078070959011229013 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_50_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_50_1
  · norm_num [gridPoint]

theorem exp_3_51_0 : expNegUpper (43621303937641907286189 / 578991610523689472000 : ℝ) ≤ (954115185333204437015678897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (360291 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_51_1 : expNegUpper (2179825954984715615927 / 28949580526184473600 : ℝ) ≤ (248961171310800082050935073 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (450213 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_51 : rowCell 3 51 ≤ (284385651359005312936912599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (954115185333204437015678897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (248961171310800082050935073 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_51_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_51_1
  · norm_num [gridPoint]

theorem exp_3_52_0 : expNegUpper (244358912901638501663 / 3245253519864038400 : ℝ) ≤ (497921424505109231704572971 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (450213 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_52_1 : expNegUpper (4884507906258927830579 / 64905070397280768000 : ℝ) ≤ (1037668745010368927475958553 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (900137 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_52 : rowCell 3 52 ≤ (296570984838107970829651637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (497921424505109231704572971 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1037668745010368927475958553 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_52_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_52_1
  · norm_num [gridPoint]

theorem exp_3_53_0 : expNegUpper (44350163053676547652739 / 589322494933119488000 : ℝ) ≤ (1037666865199445817273611419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (900137 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_53_1 : expNegUpper (22163442445237265940909 / 294661247466559744000 : ℝ) ≤ (2158949685716859670418682829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (899859 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_53 : rowCell 3 53 ≤ (308767750942167251653426897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1037666865199445817273611419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2158949685716859670418682829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_53_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_53_1
  · norm_num [gridPoint]

theorem exp_3_54_0 : expNegUpper (894359802482508121509 / 11890443891929344000 : ℝ) ≤ (2158945842888176866545191721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (899859 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_54_1 : expNegUpper (1787818811778620130697 / 23780887783858688000 : ℝ) ≤ (1121146427251654544185670971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (899593 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_54 : rowCell 3 54 ≤ (10029446251614979484239883 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2158945842888176866545191721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1121146427251654544185670971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_54_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_54_1
  · norm_num [gridPoint]

theorem exp_3_55_0 : expNegUpper (5009788391775572477393 / 66638303618396672000 : ℝ) ≤ (2242288932685462194135930401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (899593 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_55_1 : expNegUpper (625921352231137657793 / 8329787952299584000 : ℝ) ≤ (1162565327022643237026510733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (449669 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_55 : rowCell 3 55 ≤ (333060339805441146291344947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2242288932685462194135930401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1162565327022643237026510733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_55_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_55_1
  · norm_num [gridPoint]

theorem exp_3_56_0 : expNegUpper (5682561156447429130633 / 75623763605053504000 : ℝ) ≤ (1162563328853462373985227021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (449669 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_56_1 : expNegUpper (9087899216268480578379 / 120998021768085606400 : ℝ) ≤ (1203612384991764756928002207 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (449547 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_56 : rowCell 3 56 ≤ (345087317829173740414886211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1162563328853462373985227021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1203612384991764756928002207 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_56_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_56_1
  · norm_num [gridPoint]

theorem exp_3_57_0 : expNegUpper (9167036258652379010019 / 122051664684208230400 : ℝ) ≤ (1203610351912667690532711733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (449547 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_57_1 : expNegUpper (22907478224452812294443 / 305129161710520576000 : ℝ) ≤ (497667240248931624489089063 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1797723 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_57 : rowCell 3 57 ≤ (356988407869610825098300863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1203610351912667690532711733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (497667240248931624489089063 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_57_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_57_1
  · norm_num [gridPoint]

theorem exp_3_58_0 : expNegUpper (2567343424631454724483 / 34197187572633856000 : ℝ) ≤ (1244166035089630422045280219 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1797723 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_58_1 : expNegUpper (5132525383963358131237 / 68394375145267712000 : ℝ) ≤ (2568226552795639221942031517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1797279 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_58 : rowCell 3 58 ≤ (184364398894608770913437341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1244166035089630422045280219 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2568226552795639221942031517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_58_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_58_1
  · norm_num [gridPoint]

theorem exp_3_59_0 : expNegUpper (1863660011769237989837 / 24834530699981312000 : ℝ) ≤ (128411118096327161208129827 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1797279 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_59_1 : expNegUpper (465728220939748453977 / 6208632674995328000 : ℝ) ≤ (1323329662631546045636018343 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1796857 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_59 : rowCell 3 59 ≤ (190136928937567020819736083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (128411118096327161208129827 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1323329662631546045636018343 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_59_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_59_1
  · norm_num [gridPoint]

theorem exp_3_60_0 : expNegUpper (11743286809548708973713 / 156549999249352832000 : ℝ) ≤ (2646655079862781973508858981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1796857 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_60_1 : expNegUpper (46955247356158137967651 / 626199996997411328000 : ℝ) ≤ (2723401191000427631820262077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (359291 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_60 : rowCell 3 60 ≤ (3059291624463094516292807 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2646655079862781973508858981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2723401191000427631820262077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_60_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_60_1
  · norm_num [gridPoint]

theorem exp_3_61_0 : expNegUpper (5261903607510721135171 / 70173284977893888000 : ℝ) ≤ (272339689648781479588711219 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224557 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_61_1 : expNegUpper (105200031632352772489 / 1403465699557877760 : ℝ) ≤ (2798223246457381825047747557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (71843 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_61 : rowCell 3 61 ≤ (201320750827080457461829547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (272339689648781479588711219 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2798223246457381825047747557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_61_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_61_1
  · norm_num [gridPoint]

theorem exp_3_62_0 : expNegUpper (954869319495491188801 / 12738839418208675840 : ℝ) ≤ (1399109454187379456296679367 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (71843 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_62_1 : expNegUpper (47727132721515321083961 / 636941970910433792000 : ℝ) ≤ (89715694721285520563343639 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (359143 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_62 : rowCell 3 62 ≤ (41339740684014763491581303 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1399109454187379456296679367 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (89715694721285520563343639 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_62_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_62_1
  · norm_num [gridPoint]

theorem exp_3_63_0 : expNegUpper (48132157752067690294449 / 642347215325577728000 : ℝ) ≤ (2870897855070805604882173601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (359143 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_63_1 : expNegUpper (751822075146351642007 / 10036675239462152000 : ℝ) ≤ (18382635646553260717164629 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112211 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_63 : rowCell 3 63 ≤ (105956245008348801338862497 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2870897855070805604882173601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18382635646553260717164629 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_63_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_63_1
  · norm_num [gridPoint]

theorem sum_3_32_2 : blockSum (rowCell 3) 32 2 ≤ (94351547406445913558909943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_32) (by simpa only [blockSum_one] using cell_3_33) (by norm_num)

theorem sum_3_34_2 : blockSum (rowCell 3) 34 2 ≤ (219622633804696107036628161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_34) (by simpa only [blockSum_one] using cell_3_35) (by norm_num)

theorem sum_3_32_4 : blockSum (rowCell 3) 32 4 ≤ (408325728617587934154448047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_32_2 sum_3_34_2 (by norm_num)

theorem sum_3_36_2 : blockSum (rowCell 3) 36 2 ≤ (50693607992119809019767997 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_36) (by simpa only [blockSum_one] using cell_3_37) (by norm_num)

theorem sum_3_38_2 : blockSum (rowCell 3) 38 2 ≤ (58029677383479198442612557 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_38) (by simpa only [blockSum_one] using cell_3_39) (by norm_num)

theorem sum_3_36_4 : blockSum (rowCell 3) 36 4 ≤ (54361642687799503731190277 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_36_2 sum_3_38_2 (by norm_num)

theorem sum_3_32_8 : blockSum (rowCell 3) 32 8 ≤ (951942155495582971466350817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_32_4 sum_3_36_4 (by norm_num)

theorem sum_3_40_2 : blockSum (rowCell 3) 40 2 ≤ (8237718599590952586846621 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_40) (by simpa only [blockSum_one] using cell_3_41) (by norm_num)

theorem sum_3_42_2 : blockSum (rowCell 3) 42 2 ≤ (14853161089599839160392999 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_42) (by simpa only [blockSum_one] using cell_3_43) (by norm_num)

theorem sum_3_40_4 : blockSum (rowCell 3) 40 4 ≤ (140167554244726816496737963 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_40_2 sum_3_42_2 (by norm_num)

theorem sum_3_44_2 : blockSum (rowCell 3) 44 2 ≤ (83064965926833823972248527 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_44) (by simpa only [blockSum_one] using cell_3_45) (by norm_num)

theorem sum_3_46_2 : blockSum (rowCell 3) 46 2 ≤ (230575140374801414965132921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_46) (by simpa only [blockSum_one] using cell_3_47) (by norm_num)

theorem sum_3_44_4 : blockSum (rowCell 3) 44 4 ≤ (876475110383771949791508477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_44_2 sum_3_46_2 (by norm_num)

theorem sum_3_40_8 : blockSum (rowCell 3) 40 8 ≤ (394328220401851508068799573 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_40_4 sum_3_44_4 (by norm_num)

theorem sum_3_32_16 : blockSum (rowCell 3) 32 16 ≤ (2529255037102989003741549109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_32_8 sum_3_40_8 (by norm_num)

theorem sum_3_48_2 : blockSum (rowCell 3) 48 2 ≤ (508402901066251338369678213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_48) (by simpa only [blockSum_one] using cell_3_49) (by norm_num)

theorem sum_3_50_2 : blockSum (rowCell 3) 50 2 ≤ (556630330944472838388881029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_50) (by simpa only [blockSum_one] using cell_3_51) (by norm_num)

theorem sum_3_48_4 : blockSum (rowCell 3) 48 4 ≤ (532516616005362088379279621 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_48_2 sum_3_50_2 (by norm_num)

theorem sum_3_52_2 : blockSum (rowCell 3) 52 2 ≤ (302669367890137611241539267 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_52) (by simpa only [blockSum_one] using cell_3_53) (by norm_num)

theorem sum_3_54_2 : blockSum (rowCell 3) 54 2 ≤ (654002619857120489787021203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_54) (by simpa only [blockSum_one] using cell_3_55) (by norm_num)

theorem sum_3_52_4 : blockSum (rowCell 3) 52 4 ≤ (1259341355637395712270099737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_52_2 sum_3_54_2 (by norm_num)

theorem sum_3_48_8 : blockSum (rowCell 3) 48 8 ≤ (2324374587648119889028658979 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_48_4 sum_3_52_4 (by norm_num)

theorem sum_3_56_2 : blockSum (rowCell 3) 56 2 ≤ (351037862849392282756593537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_56) (by simpa only [blockSum_one] using cell_3_57) (by norm_num)

theorem sum_3_58_2 : blockSum (rowCell 3) 58 2 ≤ (23406332989510986983323339 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_58) (by simpa only [blockSum_one] using cell_3_59) (by norm_num)

theorem sum_3_56_4 : blockSum (rowCell 3) 56 4 ≤ (725539190681568074489766961 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_56_2 sum_3_58_2 (by norm_num)

theorem sum_3_60_2 : blockSum (rowCell 3) 60 2 ≤ (79423082958543701300913839 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_60) (by simpa only [blockSum_one] using cell_3_61) (by norm_num)

theorem sum_3_62_2 : blockSum (rowCell 3) 62 2 ≤ (418611193436771420135631509 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_62) (by simpa only [blockSum_one] using cell_3_63) (by norm_num)

theorem sum_3_60_4 : blockSum (rowCell 3) 60 4 ≤ (796608015849111256484571 / 488281250000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_60_2 sum_3_62_2 (by norm_num)

theorem sum_3_56_8 : blockSum (rowCell 3) 56 8 ≤ (308253159782211600225993533 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_56_4 sum_3_60_4 (by norm_num)

theorem sum_3_48_16 : blockSum (rowCell 3) 48 16 ≤ (5406906185470235891288594309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_48_8 sum_3_56_8 (by norm_num)

theorem sum_3_32_32 : blockSum (rowCell 3) 32 32 ≤ (3968080611286612447515071709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_32_16 sum_3_48_16 (by norm_num)

#print axioms sum_3_32_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
