import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_96_0 : expNegUpper (1999683090917369535677 / 26047892829811216000 : ℝ) ≤ (28559734441263160694423897 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455421 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_96_1 : expNegUpper (12799225734092778444707 / 166706514110791782400 : ℝ) ≤ (90706292701522398925473309 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_96 : rowCell 6 96 ≤ (66393545702142459771712223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28559734441263160694423897 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (90706292701522398925473309 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_96_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_96_1
  · norm_num [gridPoint]

theorem exp_6_97_0 : expNegUpper (12894149084797859047867 / 167942863472955494400 : ℝ) ≤ (90706207392658977344119969 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_97_1 : expNegUpper (32238958371080039200343 / 419857158682388736000 : ℝ) ≤ (89934857748747916341034739 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (227739 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_97 : rowCell 6 97 ≤ (65862543824091768351387633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (90706207392658977344119969 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (89934857748747916341034739 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_97_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_97_1
  · norm_num [gridPoint]

theorem exp_6_98_0 : expNegUpper (32477169970295231242567 / 422959451240675584000 : ℝ) ≤ (44967387201961466958977667 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (227739 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_98_1 : expNegUpper (64962416146603510635653 / 845918902481351168000 : ℝ) ≤ (222700574198881741874278149 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (56939 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_98 : rowCell 6 98 ≤ (1631741866444971779490397 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (44967387201961466958977667 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (222700574198881741874278149 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_98_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_98_1
  · norm_num [gridPoint]

theorem exp_6_99_0 : expNegUpper (104705043922396757773 / 1363434121445888000 : ℝ) ≤ (445400741655496803386609771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (56939 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_99_1 : expNegUpper (26179854750453134263 / 340858530361472000 : ℝ) ≤ (44072942190642892146366447 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911099 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_99 : rowCell 6 99 ≤ (32308703829752224511862709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (445400741655496803386609771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44072942190642892146366447 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_99_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_99_1
  · norm_num [gridPoint]

theorem exp_6_100_0 : expNegUpper (16482423237262618834343 / 214599146907940992000 : ℝ) ≤ (860798877501576653262551 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911099 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_100_1 : expNegUpper (65939588923086700195291 / 858396587631763968000 : ℝ) ≤ (435677282220210696124771333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822363 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_100 : rowCell 6 100 ≤ (63908335339266123819849599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (860798877501576653262551 / 1953125000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (435677282220210696124771333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_100_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_100_1
  · norm_num [gridPoint]

theorem exp_6_101_0 : expNegUpper (66421471425586614401939 / 864669687665603072000 : ℝ) ≤ (217838447909899189475283707 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822363 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_101_1 : expNegUpper (6643228227980375097809 / 86466968766560307200 : ℝ) ≤ (215131797442704910911563369 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822541 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_101 : rowCell 6 101 ≤ (63145158575633399960910661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (217838447909899189475283707 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (215131797442704910911563369 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_101_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_101_1
  · norm_num [gridPoint]

theorem exp_6_102_0 : expNegUpper (6691599787344503753089 / 87096562600519731200 : ℝ) ≤ (430263218793286542022876057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822541 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_102_1 : expNegUpper (66927726938622634734961 / 870965626005197312000 : ℝ) ≤ (212253908663513216213177923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455683 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_102 : rowCell 6 102 ≤ (62330671912245986440525973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (430263218793286542022876057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (212253908663513216213177923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_102_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_102_1
  · norm_num [gridPoint]

theorem exp_6_103_0 : expNegUpper (67413282284964391453289 / 877284402650546688000 : ℝ) ≤ (424507451601597761299366931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455683 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_103_1 : expNegUpper (8428241611485249774371 / 109660550331318336000 : ℝ) ≤ (41842989894914362946160771 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911469 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_103 : rowCell 6 103 ≤ (61467748928685947646008533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (424507451601597761299366931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41842989894914362946160771 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_103_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_103_1
  · norm_num [gridPoint]

theorem exp_6_104_0 : expNegUpper (339566673262416614491 / 4418130088008256000 : ℝ) ≤ (418429543625016323708821783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911469 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_104_1 : expNegUpper (2717076405276819523487 / 35345040704066048000 : ℝ) ≤ (206025091316749738621707619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823157 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_104 : rowCell 6 104 ≤ (30279663886450016295363521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (418429543625016323708821783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (206025091316749738621707619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_104_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_104_1
  · norm_num [gridPoint]

theorem exp_6_105_0 : expNegUpper (68416164968340478594687 / 889990470858510848000 : ℝ) ≤ (412049837722413477025958143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823157 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_105_1 : expNegUpper (34215334325538375570323 / 444995235429255424000 : ℝ) ≤ (81077861635609389441433991 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823389 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_105 : rowCell 6 105 ≤ (29804198468522109539996049 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (412049837722413477025958143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (81077861635609389441433991 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_105_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_105_1
  · norm_num [gridPoint]

theorem exp_6_106_0 : expNegUpper (1813731137496697507153 / 23588888484766464000 : ℝ) ≤ (40538897366985617150742181 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823389 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_106_1 : expNegUpper (725654930965151937731 / 9435555393906585600 : ℝ) ≤ (398468118176132857654759003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911817 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_106 : rowCell 6 106 ≤ (58617981352765475387274613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (40538897366985617150742181 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (398468118176132857654759003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_106_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_106_1
  · norm_num [gridPoint]

theorem exp_6_107_0 : expNegUpper (13886039882884809931729 / 180557578457899110400 : ℝ) ≤ (79693558807965411474114783 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911817 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_107_1 : expNegUpper (17361642374024295911909 / 225696973072373888000 : ℝ) ≤ (78261513358796842849035217 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455973 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_107 : rowCell 6 107 ≤ (57591128875802267053534833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (79693558807965411474114783 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (78261513358796842849035217 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_107_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_107_1
  · norm_num [gridPoint]

theorem exp_6_108_0 : expNegUpper (17485355882331939621061 / 227305215115905152000 : ℝ) ≤ (97826813244686089026907233 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455973 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_108_1 : expNegUpper (69958731806638646559283 / 909220860463620608000 : ℝ) ≤ (38392863185997513976857577 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456041 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_108 : rowCell 6 108 ≤ (14132724305857427606584981 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (97826813244686089026907233 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38392863185997513976857577 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_108_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_108_1
  · norm_num [gridPoint]

theorem exp_6_109_0 : expNegUpper (2818218622476971139107 / 36627066677740032000 : ℝ) ≤ (191964164148127523514259789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456041 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_109_1 : expNegUpper (1409474307313049390969 / 18313533338870016000 : ℝ) ≤ (2940251801829222597205119 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28507 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_109 : rowCell 6 109 ≤ (55440341421769106765451393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (191964164148127523514259789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2940251801829222597205119 / 7812500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_109_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_109_1
  · norm_num [gridPoint]

theorem exp_6_110_0 : expNegUpper (35486167752276128184001 / 461077655864568064000 : ℝ) ≤ (188175968617383878193882951 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28507 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_110_1 : expNegUpper (70991530165477299344201 / 922155311729136128000 : ℝ) ≤ (5759361555954055500337997 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (364949 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_110 : rowCell 6 110 ≤ (54322501813393204049060681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (188175968617383878193882951 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5759361555954055500337997 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_110_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_110_1
  · norm_num [gridPoint]

theorem exp_6_111_0 : expNegUpper (71492043349550338884289 / 928656794820526592000 : ℝ) ≤ (184299428121174523443111541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (364949 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_111_1 : expNegUpper (178780465496129456689 / 2321641987051316480 : ℝ) ≤ (180344959211991660924892781 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912527 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_111 : rowCell 6 111 ≤ (53180392669052445611217287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (184299428121174523443111541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (180344959211991660924892781 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_111_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_111_1
  · norm_num [gridPoint]

theorem exp_6_112_0 : expNegUpper (5807628958811062319 / 75417831953038080 : ℝ) ≤ (90172411256714249941795471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912527 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_112_1 : expNegUpper (2323732046997244073281 / 30167132781215232000 : ℝ) ≤ (70528967742664035386572993 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (14603 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_112 : rowCell 6 112 ≤ (6502123930097994380049951 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (90172411256714249941795471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (70528967742664035386572993 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_112_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_112_1
  · norm_num [gridPoint]

theorem exp_6_113_0 : expNegUpper (72540012716011404710999 / 941728275920572928000 : ℝ) ≤ (35264457512442718464366293 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (14603 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_113_1 : expNegUpper (36281030966602148430799 / 470864137960286464000 : ℝ) ≤ (344483817098692413842573347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825709 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_113 : rowCell 6 113 ≤ (10167045737439953816126123 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35264457512442718464366293 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (344483817098692413842573347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_113_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_113_1
  · norm_num [gridPoint]

theorem exp_6_114_0 : expNegUpper (1461365884443033629591 / 18965965478584576000 : ℝ) ≤ (344483563171523954390703669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825709 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_114_1 : expNegUpper (2923652064786384846973 / 37931930957169152000 : ℝ) ≤ (336226353451062318799505313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (365211 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_114 : rowCell 6 114 ≤ (49637978695434706645884859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (344483563171523954390703669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (336226353451062318799505313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_114_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_114_1
  · norm_num [gridPoint]

theorem exp_6_115_0 : expNegUpper (73599453600016649790317 / 954891110243639808000 : ℝ) ≤ (336226109027056075205643447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (365211 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_115_1 : expNegUpper (18405855627154796484739 / 238722777560909952000 : ℝ) ≤ (327891473940197197478619569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (913207 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_115 : rowCell 6 115 ≤ (48428050818113055785748637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (336226109027056075205643447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (327891473940197197478619569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_115_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_115_1
  · norm_num [gridPoint]

theorem exp_6_116_0 : expNegUpper (18533375210486239093091 / 240376696215951488000 : ℝ) ≤ (327891238849826537306834309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (913207 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_116_1 : expNegUpper (14831686918484327576911 / 192301356972761190400 : ℝ) ≤ (79874419783314837736437367 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (57087 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_116 : rowCell 6 116 ≤ (5901022692225952925013267 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (327891238849826537306834309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (79874419783314837736437367 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_116_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_116_1
  · norm_num [gridPoint]

theorem exp_6_117_0 : expNegUpper (14934089188055049590951 / 193629059557945446400 : ℝ) ≤ (159748726598551468501119719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (57087 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_117_1 : expNegUpper (37348173931702811870093 / 484072648894863616000 : ℝ) ≤ (155531448571397266086701817 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (913583 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_117 : rowCell 6 117 ≤ (11495256816462520488480089 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (159748726598551468501119719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (155531448571397266086701817 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_117_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_117_1
  · norm_num [gridPoint]

theorem exp_6_118_0 : expNegUpper (37605149443673085633277 / 487403324510701824000 : ℝ) ≤ (15553134008629118588599209 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (913583 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_118_1 : expNegUpper (75237172313909790234913 / 974806649021403648000 : ℝ) ≤ (302604441817040973910475787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1827559 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_118 : rowCell 6 118 ≤ (22374578938519123459694809 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15553134008629118588599209 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (302604441817040973910475787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_118_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_118_1
  · norm_num [gridPoint]

theorem exp_6_119_0 : expNegUpper (3030122787019854921473 / 39259633542353408000 : ℝ) ≤ (151302116808336671983206503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1827559 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_119_1 : expNegUpper (378904589681363920489 / 4907454192794176000 : ℝ) ≤ (73534743983111518084344259 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456991 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_119 : rowCell 6 119 ≤ (10878762744199779280961989 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (151302116808336671983206503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (73534743983111518084344259 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_119_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_119_1
  · norm_num [gridPoint]

theorem exp_6_120_0 : expNegUpper (9537346037133062499329 / 123524733300252736000 : ℝ) ≤ (294138776298982157052787449 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456991 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_120_1 : expNegUpper (76327594722833252057911 / 988197866402021888000 : ℝ) ≤ (71420619829420294026358107 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_120 : rowCell 6 120 ≤ (21140543446363216674930389 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (294138776298982157052787449 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (71420619829420294026358107 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_120_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_120_1
  · norm_num [gridPoint]

theorem exp_6_121_0 : expNegUpper (76847404744389198869039 / 994927732550963712000 : ℝ) ≤ (57136457608458929103787603 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_121_1 : expNegUpper (7687721266592984084431 / 99492773255096371200 : ℝ) ≤ (27725022181037646761192411 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828809 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_121 : rowCell 6 121 ≤ (4104954437813359832870567 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (57136457608458929103787603 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27725022181037646761192411 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_121_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_121_1
  · norm_num [gridPoint]

theorem exp_6_122_0 : expNegUpper (7739898900980911638911 / 100168043700566067200 : ℝ) ≤ (69312509669818901606446549 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828809 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_122_1 : expNegUpper (77429781757901197186061 / 1001680437005660672000 : ℝ) ≤ (134428370461158457086182469 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28582 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_122 : rowCell 6 122 ≤ (19911298505678962453898703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (69312509669818901606446549 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (134428370461158457086182469 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_122_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_122_1
  · norm_num [gridPoint]

theorem exp_6_123_0 : expNegUpper (77953531085662899283909 / 1008455979766112768000 : ℝ) ≤ (268856565717627278952521769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28582 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_123_1 : expNegUpper (19496327997771491953057 / 252113994941528192000 : ℝ) ≤ (260515824065977297084730119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1829699 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_123 : rowCell 6 123 ≤ (9650577567756722972968173 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (268856565717627278952521769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (260515824065977297084730119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_123_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_123_1
  · norm_num [gridPoint]

theorem exp_6_124_0 : expNegUpper (31404416385715677713 / 406101744332928000 : ℝ) ≤ (260515656566585234345587267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1829699 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_124_1 : expNegUpper (125670101372516479123 / 1624406977331712000 : ℝ) ≤ (252240495175033278618660193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (22877 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_124 : rowCell 6 124 ≤ (37390639264353902325735667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (260515656566585234345587267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (252240495175033278618660193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_124_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_124_1
  · norm_num [gridPoint]

theorem exp_6_125_0 : expNegUpper (4161659402001402532313 / 53793451589699072000 : ℝ) ≤ (7882510473668405466304603 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (22877 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_125_1 : expNegUpper (2081718311853956285107 / 26896725794849536000 : ℝ) ≤ (12202150276692281982236053 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1830633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_125 : rowCell 6 125 ≤ (18094713541384365187642949 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7882510473668405466304603 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12202150276692281982236053 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_125_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_125_1
  · norm_num [gridPoint]

theorem exp_6_126_0 : expNegUpper (39817502049606953753657 / 514459818940999936000 : ℝ) ≤ (244042852772724696389105907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1830633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_126_1 : expNegUpper (15933953892261446537573 / 205783927576399974400 : ℝ) ≤ (117967414307916570860006579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (457779 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_126 : rowCell 6 126 ≤ (35000403756801760087349639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (244042852772724696389105907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (117967414307916570860006579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_126_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_126_1
  · norm_num [gridPoint]

theorem exp_6_127_0 : expNegUpper (16040295468037923838333 / 207157306773094502400 : ℝ) ≤ (921619855019749885803061 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (457779 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_127_1 : expNegUpper (626853470177594747987 / 8092082295824004000 : ℝ) ≤ (28490832339757845285222143 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (183161 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_127 : rowCell 6 127 ≤ (33825185780123514565800269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (921619855019749885803061 / 3906250000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28490832339757845285222143 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_127_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_127_1
  · norm_num [gridPoint]

theorem sum_6_96_2 : blockSum (rowCell 6) 96 2 ≤ (8266005595389639257693741 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_96) (by simpa only [blockSum_one] using cell_6_97) (by norm_num)

theorem sum_6_98_2 : blockSum (rowCell 6) 98 2 ≤ (64943541158651660101670649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_98) (by simpa only [blockSum_one] using cell_6_99) (by norm_num)

theorem sum_6_96_4 : blockSum (rowCell 6) 96 4 ≤ (131071585921768774163220577 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_96_2 sum_6_98_2 (by norm_num)

theorem sum_6_100_2 : blockSum (rowCell 6) 100 2 ≤ (6352674695744976189038013 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_100) (by simpa only [blockSum_one] using cell_6_101) (by norm_num)

theorem sum_6_102_2 : blockSum (rowCell 6) 102 2 ≤ (61899210420465967043267253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_102) (by simpa only [blockSum_one] using cell_6_103) (by norm_num)

theorem sum_6_100_4 : blockSum (rowCell 6) 100 4 ≤ (125425957377915728933647383 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_100_2 sum_6_102_2 (by norm_num)

theorem sum_6_96_8 : blockSum (rowCell 6) 96 8 ≤ (6412438582492112577421699 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_96_4 sum_6_100_4 (by norm_num)

theorem sum_6_104_2 : blockSum (rowCell 6) 104 2 ≤ (6008386235497212583535957 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_104) (by simpa only [blockSum_one] using cell_6_105) (by norm_num)

theorem sum_6_106_2 : blockSum (rowCell 6) 106 2 ≤ (58104555114283871220404723 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_106) (by simpa only [blockSum_one] using cell_6_107) (by norm_num)

theorem sum_6_104_4 : blockSum (rowCell 6) 104 4 ≤ (118188417469255997055764293 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_104_2 sum_6_106_2 (by norm_num)

theorem sum_6_108_2 : blockSum (rowCell 6) 108 2 ≤ (111971238645198817191791317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_108) (by simpa only [blockSum_one] using cell_6_109) (by norm_num)

theorem sum_6_110_2 : blockSum (rowCell 6) 110 2 ≤ (6718930905152853103767373 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_110) (by simpa only [blockSum_one] using cell_6_111) (by norm_num)

theorem sum_6_108_4 : blockSum (rowCell 6) 108 4 ≤ (43894826625528893370413857 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_108_2 sum_6_110_2 (by norm_num)

theorem sum_6_104_8 : blockSum (rowCell 6) 104 8 ≤ (455850968066156460963597871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_104_4 sum_6_108_4 (by norm_num)

theorem sum_6_96_16 : blockSum (rowCell 6) 96 16 ≤ (968846054665525467157333791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_96_8 sum_6_104_8 (by norm_num)

theorem sum_6_112_2 : blockSum (rowCell 6) 112 2 ≤ (102852220127983724121030223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_112) (by simpa only [blockSum_one] using cell_6_113) (by norm_num)

theorem sum_6_114_2 : blockSum (rowCell 6) 114 2 ≤ (12258253689193470303954187 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_114) (by simpa only [blockSum_one] using cell_6_115) (by norm_num)

theorem sum_6_112_4 : blockSum (rowCell 6) 112 4 ≤ (200918249641531486552663719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_112_2 sum_6_114_2 (by norm_num)

theorem sum_6_116_2 : blockSum (rowCell 6) 116 2 ≤ (23297302200914426338506623 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_116) (by simpa only [blockSum_one] using cell_6_117) (by norm_num)

theorem sum_6_118_2 : blockSum (rowCell 6) 118 2 ≤ (44132104426918682021618787 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_118) (by simpa only [blockSum_one] using cell_6_119) (by norm_num)

theorem sum_6_116_4 : blockSum (rowCell 6) 116 4 ≤ (90726708828747534698632033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_116_2 sum_6_118_2 (by norm_num)

theorem sum_6_112_8 : blockSum (rowCell 6) 112 8 ≤ (76474333459805311189985557 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_112_4 sum_6_116_4 (by norm_num)

theorem sum_6_120_2 : blockSum (rowCell 6) 120 2 ≤ (5208164454428751979910403 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_120) (by simpa only [blockSum_one] using cell_6_121) (by norm_num)

theorem sum_6_122_2 : blockSum (rowCell 6) 122 2 ≤ (39212453641192408399835049 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_122) (by simpa only [blockSum_one] using cell_6_123) (by norm_num)

theorem sum_6_120_4 : blockSum (rowCell 6) 120 4 ≤ (80877769276622424239118273 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_120_2 sum_6_122_2 (by norm_num)

theorem sum_6_124_2 : blockSum (rowCell 6) 124 2 ≤ (14716013269424526540204313 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_124) (by simpa only [blockSum_one] using cell_6_125) (by norm_num)

theorem sum_6_126_2 : blockSum (rowCell 6) 126 2 ≤ (17206397384231318663287477 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_126) (by simpa only [blockSum_one] using cell_6_127) (by norm_num)

theorem sum_6_124_4 : blockSum (rowCell 6) 124 4 ≤ (142405655884047907354171473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_124_2 sum_6_126_2 (by norm_num)

theorem sum_6_120_8 : blockSum (rowCell 6) 120 8 ≤ (304161194437292755832408019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_120_4 sum_6_124_4 (by norm_num)

theorem sum_6_112_16 : blockSum (rowCell 6) 112 16 ≤ (171633215434079827945583951 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_112_8 sum_6_120_8 (by norm_num)

theorem sum_6_96_32 : blockSum (rowCell 6) 96 32 ≤ (331075783280368955787933919 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_96_16 sum_6_112_16 (by norm_num)

#print axioms sum_6_96_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
