import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_0_0 : (429767945098967060201619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (28327916840080233617 / 338298021018624000 : ℝ) := by
  apply lower_of_taylor (t := (480897 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_0 : (391738308453185661039 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 0 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (429767945098967060201619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_0_0
  · norm_num [gridPoint]

theorem exp_7_1_0 : (103645866435097215005841 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1463812407845672659209 / 17520322149069824000 : ℝ) := by
  apply lower_of_taylor (t := (1920777 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_1 : (94474371247255177511 / 1250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 1 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (103645866435097215005841 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_1_0
  · norm_num [gridPoint]

theorem exp_7_2_0 : (155635289548411562412277 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1477322993621606637869 / 17720927537273856000 : ℝ) := by
  apply lower_of_taylor (t := (1918027 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_2 : (9079252113960499825693 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 2 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (155635289548411562412277 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_2_0
  · norm_num [gridPoint]

theorem exp_7_3_0 : (745075113688138115648163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (120235612835229212389 / 1445377003287552000 : ℝ) := by
  apply lower_of_taylor (t := (1915337 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_3 : (13582886673390371394913 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 3 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (745075113688138115648163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_3_0
  · norm_num [gridPoint]

theorem exp_7_4_0 : (222118710052844838343253 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (24267882646263093273 / 292347807412019200 : ℝ) := by
  apply lower_of_taylor (t := (382541 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_4 : (25915353434931213943639 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 4 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (222118710052844838343253 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_4_0
  · norm_num [gridPoint]

theorem exp_7_5_0 : (211134821276017771415983 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7591924339864738111147 / 91647975968062464000 : ℝ) := by
  apply lower_of_taylor (t := (191013 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_5 : (153961408588882060638699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 5 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (211134821276017771415983 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_5_0
  · norm_num [gridPoint]

theorem exp_7_6_0 : (624957161804539742283417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1532250530487682087987 / 18534768242967552000 : ℝ) := by
  apply lower_of_taylor (t := (1907611 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_6 : (7291590035797935483757 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 6 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (624957161804539742283417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_6_0
  · norm_num [gridPoint]

theorem exp_7_7_0 : (1474761083094107551920877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (386551552807361879163 / 4685270801902592000 : ℝ) := by
  apply lower_of_taylor (t := (1905147 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_7 : (26885225789970728762081 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 7 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1474761083094107551920877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_7_0
  · norm_num [gridPoint]

theorem exp_7_8_0 : (3386951901037605930979 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1950315512268970305847 / 23685675109426176000 : ℝ) := by
  apply lower_of_taylor (t := (951369 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_8 : (63226771350594768118033 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 8 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3386951901037605930979 / 1953125000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_8_0
  · norm_num [gridPoint]

theorem exp_7_9_0 : (203224711881143559342909 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1574389625861800608517 / 19157138882759270400 : ℝ) := by
  apply lower_of_taylor (t := (1900381 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_9 : (29638657150150138124403 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 9 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (203224711881143559342909 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_9_0
  · norm_num [gridPoint]

theorem exp_7_10_0 : (474753333242376495583157 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7943091794931264723117 / 96834397966326784000 : ℝ) := by
  apply lower_of_taylor (t := (474519 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_10 : (69238879192463858011113 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 10 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (474753333242376495583157 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_10_0
  · norm_num [gridPoint]

theorem exp_7_11_0 : (1381836917546369918665939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (32058782176109311789 / 391555244381184000 : ℝ) := by
  apply lower_of_taylor (t := (947911 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_11 : (25191197380396725633961 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 11 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1381836917546369918665939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_11_0
  · norm_num [gridPoint]

theorem exp_7_12_0 : (1603672073206538226818713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (32347047498727417589 / 395795735202816000 : ℝ) := by
  apply lower_of_taylor (t := (946809 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_12 : (233882416754698077997617 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 12 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1603672073206538226818713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_12_0
  · norm_num [gridPoint]

theorem exp_7_13_0 : (3710535844650983010434649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8159293284979505755383 / 100014766082550784000 : ℝ) := by
  apply lower_of_taylor (t := (236433 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_13 : (270575607476497609738443 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 13 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3710535844650983010434649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_13_0
  · norm_num [gridPoint]

theorem exp_7_14_0 : (4279389338401738392556163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1646458454600988740783 / 20217261588167270400 : ℝ) := by
  apply lower_of_taylor (t := (1889357 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_14 : (39007114415014185487129 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 14 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (4279389338401738392556163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_14_0
  · norm_num [gridPoint]

theorem exp_7_15_0 : (984084540077021196645931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1038220167105353740639 / 12770444921945088000 : ℝ) := by
  apply lower_of_taylor (t := (943649 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_15 : (358801644004351805540763 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 15 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (984084540077021196645931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_15_0
  · norm_num [gridPoint]

theorem exp_7_16_0 : (1410130722761623198346613 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (209492574364445652531 / 2581163009668096000 : ℝ) := by
  apply lower_of_taylor (t := (377057 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_16 : (411311996872395179077109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 16 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1410130722761623198346613 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_16_0
  · norm_num [gridPoint]

theorem exp_7_17_0 : (6446932400483741796809143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1690823936858918782913 / 20867038194865152000 : ℝ) := by
  apply lower_of_taylor (t := (941659 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_17 : (470116102809103011435093 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 17 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (6446932400483741796809143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_17_0
  · norm_num [gridPoint]

theorem exp_7_18_0 : (1469446208245435889179033 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8529013964077795047353 / 105429571138366464000 : ℝ) := by
  apply lower_of_taylor (t := (470349 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_18 : (1071533377108349055477417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 18 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1469446208245435889179033 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_18_0
  · norm_num [gridPoint]

theorem exp_7_19_0 : (8349312669253047498125499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (860438831201209118187 / 10652966087884595200 : ℝ) := by
  apply lower_of_taylor (t := (1879517 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_19 : (243535752471013402239269 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 19 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (8349312669253047498125499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_19_0
  · norm_num [gridPoint]

theorem exp_7_20_0 : (9461356662176855932513803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4340122613091072000191 / 53817730097882112000 : ℝ) := by
  apply lower_of_taylor (t := (938841 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_20 : (172482657060890627279477 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 20 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (9461356662176855932513803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_20_0
  · norm_num [gridPoint]

theorem exp_7_21_0 : (2138358808272124953445949 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1751317440934523037031 / 21749393817824256000 : ℝ) := by
  apply lower_of_taylor (t := (187589 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_21 : (779655227404725792962707 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 21 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2138358808272124953445949 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_21_0
  · norm_num [gridPoint]

theorem exp_7_22_0 : (6024634094018731923243329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1766683349113633283691 / 21972837511783424000 : ℝ) := by
  apply lower_of_taylor (t := (1874139 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_22 : (1757286923572159107189463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 22 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (6024634094018731923243329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_22_0
  · norm_num [gridPoint]

theorem exp_7_23_0 : (3385647542932742498744941 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2227684086738364845637 / 27746778901287936000 : ℝ) := by
  apply lower_of_taylor (t := (1872429 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_23 : (987537842493479746577279 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 23 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3385647542932742498744941 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_23_0
  · norm_num [gridPoint]

theorem exp_7_24_0 : (948793048832529704642009 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (89885485069131557597 / 1121157532278251520 : ℝ) := by
  apply lower_of_taylor (t := (1870759 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_24 : (2213978929667932049228857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 24 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (948793048832529704642009 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_24_0
  · norm_num [gridPoint]

theorem exp_7_25_0 : (16972555424057949385858489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (9066855723531917232177 / 113250100426937344000 : ℝ) := by
  apply lower_of_taylor (t := (1869129 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_25 : (618826995151284735640351 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 25 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (16972555424057949385858489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_25_0
  · norm_num [gridPoint]

theorem exp_7_26_0 : (18927184134563937432481599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1829132098978881096449 / 22878031440497664000 : ℝ) := by
  apply lower_of_taylor (t := (933769 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_26 : (276037454396879642972819 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 26 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (18927184134563937432481599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_26_0
  · norm_num [gridPoint]

theorem exp_7_27_0 : (328961047080118158673413 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (922496531908528219217 / 11553592355447808000 : ℝ) := by
  apply lower_of_taylor (t := (373197 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_27 : (1535240646657468939143901 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 27 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (328961047080118158673413 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_27_0
  · norm_num [gridPoint]

theorem exp_7_28_0 : (5840081372316041625519917 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4652386347094604522109 / 58343699741453312000 : ℝ) := by
  apply lower_of_taylor (t := (186447 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_28 : (1703455922469574782106241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 28 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5840081372316041625519917 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_28_0
  · norm_num [gridPoint]

theorem exp_7_29_0 : (12928118940583777791556791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1877017023658169544131 / 23568916997554790400 : ℝ) := by
  apply lower_of_taylor (t := (116437 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_29 : (3770920193016919029192723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 29 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (12928118940583777791556791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_29_0
  · norm_num [gridPoint]

theorem exp_7_30_0 : (28549563793149700339986291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (9465905089474859903747 / 119007480069080064000 : ℝ) := by
  apply lower_of_taylor (t := (1861551 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_30 : (4163719683590393113451399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 30 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (28549563793149700339986291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_30_0
  · norm_num [gridPoint]

theorem exp_7_31_0 : (15724132980062891071456763 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (119340438822823840947 / 1502201059085312000 : ℝ) := by
  apply lower_of_taylor (t := (372029 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_31 : (286654476014227573046081 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 31 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (15724132980062891071456763 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_31_0
  · norm_num [gridPoint]

theorem sum_7_0_2 : (432055082344730774297 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 0 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_0) (by simpa only [blockSum_one] using cell_7_1) (by norm_num)

theorem sum_7_2_2 : (99727807263363984708117 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 2 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_2) (by simpa only [blockSum_one] using cell_7_3) (by norm_num)

theorem sum_7_0_4 : (168856620438520908595637 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 0 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_0_2 sum_7_2_2 (by norm_num)

theorem sum_7_4_2 : (141769087881769065178447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 4 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_4) (by simpa only [blockSum_one] using cell_7_5) (by norm_num)

theorem sum_7_6_2 : (397371557214714217190573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 6 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_6) (by simpa only [blockSum_one] using cell_7_7) (by norm_num)

theorem sum_7_4_4 : (680909732978252347547467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 4 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_4_2 sum_7_6_2 (by norm_num)

theorem sum_7_0_8 : (1018622973855294164738741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 0 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_0_4 sum_7_4_4 (by norm_num)

theorem sum_7_8_2 : (274646828451940226858081 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 8 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_8) (by simpa only [blockSum_one] using cell_7_9) (by norm_num)

theorem sum_7_10_2 : (749253554048666900198941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 10 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_10) (by simpa only [blockSum_one] using cell_7_11) (by norm_num)

theorem sum_7_8_4 : (1298547210952547353915103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 8 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_8_2 sum_7_10_2 (by norm_num)

theorem sum_7_12_2 : (25222901211559784386803 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 12 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_12) (by simpa only [blockSum_one] using cell_7_13) (by norm_num)

theorem sum_7_14_2 : (134171711864893057887559 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 14 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_14) (by simpa only [blockSum_one] using cell_7_15) (by norm_num)

theorem sum_7_12_4 : (235063316711132195434771 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 12 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_12_2 sum_7_14_2 (by norm_num)

theorem sum_7_8_8 : (3649180378063869308262813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 8 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_8_4 sum_7_12_4 (by norm_num)

theorem sum_7_0_16 : (2333901675959581736500777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 0 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_0_8 sum_7_8_8 (by norm_num)

theorem sum_7_16_2 : (440714049840749095256101 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 16 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_16) (by simpa only [blockSum_one] using cell_7_17) (by norm_num)

theorem sum_7_18_2 : (1144606069731708033336881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 18 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_18) (by simpa only [blockSum_one] using cell_7_19) (by norm_num)

theorem sum_7_16_4 : (2026034169413206223849083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 16 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_16_2 sum_7_18_2 (by norm_num)

theorem sum_7_20_2 : (293917171129657660416123 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 20 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_20) (by simpa only [blockSum_one] using cell_7_21) (by norm_num)

theorem sum_7_22_2 : (3732362608559118600344021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 22 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_22) (by simpa only [blockSum_one] using cell_7_23) (by norm_num)

theorem sum_7_20_4 : (6671534319855695204505251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 20 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_20_2 sum_7_22_2 (by norm_num)

theorem sum_7_16_8 : (10723602658682107652203417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 16 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_16_4 sum_7_20_4 (by norm_num)

theorem sum_7_24_2 : (4689286910273070991790261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 24 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_24) (by simpa only [blockSum_one] using cell_7_25) (by norm_num)

theorem sum_7_26_2 : (728856979660466788501999 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 26 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_26) (by simpa only [blockSum_one] using cell_7_27) (by norm_num)

theorem sum_7_24_4 : (10520142747556805299806253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 24 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_24_2 sum_7_26_2 (by norm_num)

theorem sum_7_28_2 : (1435566407591213718681041 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 28 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_28) (by simpa only [blockSum_one] using cell_7_29) (by norm_num)

theorem sum_7_30_2 : (1750038259963606856437739 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 30 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_30) (by simpa only [blockSum_one] using cell_7_31) (by norm_num)

theorem sum_7_28_4 : (159280233377741028755939 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 28 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_28_2 sum_7_30_2 (by norm_num)

theorem sum_7_24_8 : (26448166085330908175400153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 24 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_24_4 sum_7_28_4 (by norm_num)

theorem sum_7_16_16 : (3717176874401301582760357 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 16 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_16_8 sum_7_24_8 (by norm_num)

theorem sum_7_0_32 : (10459893023983044825151281 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 0 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_0_16 sum_7_16_16 (by norm_num)

#print axioms sum_7_0_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
