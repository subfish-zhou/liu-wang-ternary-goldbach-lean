import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_96_0 : expNegUpper (1989417571444729535677 / 26047892829811216000 : ℝ) ≤ (677688867731459857864274529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454021 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_96_1 : expNegUpper (12733769133945220044707 / 166706514110791782400 : ℝ) ≤ (671631865857615649270409257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816211 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_96 : rowCell 5 96 ≤ (98393680173661969915287083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (677688867731459857864274529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (671631865857615649270409257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_96_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_96_1
  · norm_num [gridPoint]

theorem exp_5_97_0 : expNegUpper (12828207035695625447867 / 167942863472955494400 : ℝ) ≤ (671631240839964436641209349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816211 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_97_1 : expNegUpper (32074710059517799200343 / 419857158682388736000 : ℝ) ≤ (664958061345775146545072923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816353 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_97 : rowCell 5 97 ≤ (97465292757335312906350473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (671631240839964436641209349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (664958061345775146545072923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_97_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_97_1
  · norm_num [gridPoint]

theorem exp_5_98_0 : expNegUpper (32311708036346303242567 / 422959451240675584000 : ℝ) ≤ (132991490319917765435659051 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816353 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_98_1 : expNegUpper (64632705901092342635653 / 845918902481351168000 : ℝ) ≤ (3288474410253151815792887 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816509 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_98 : rowCell 5 98 ≤ (96448996490229997228168573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (132991490319917765435659051 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3288474410253151815792887 / 5000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_98_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_98_1
  · norm_num [gridPoint]

theorem exp_5_99_0 : expNegUpper (104173623937941487373 / 1363434121445888000 : ℝ) ≤ (131538857552601653777721433 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816509 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_99_1 : expNegUpper (26047485203293991863 / 340858530361472000 : ℝ) ≤ (64987025266790583980961213 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908339 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_99 : rowCell 5 99 ≤ (19069756210647810041133737 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (131538857552601653777721433 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64987025266790583980961213 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_99_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_99_1
  · norm_num [gridPoint]

theorem exp_5_100_0 : expNegUpper (16399085459094810834343 / 214599146907940992000 : ℝ) ≤ (40616854624147718814820371 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908339 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_100_1 : expNegUpper (65607451432802156195291 / 858396587631763968000 : ℝ) ≤ (40094567592447704681062301 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908431 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_100 : rowCell 5 100 ≤ (18833758151048115212065797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (40616854624147718814820371 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40094567592447704681062301 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_100_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_100_1
  · norm_num [gridPoint]

theorem exp_5_101_0 : expNegUpper (66086906690528694401939 / 864669687665603072000 : ℝ) ≤ (25660500740512700635956163 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908431 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_101_1 : expNegUpper (6609893116713251897809 / 86466968766560307200 : ℝ) ≤ (316326553880598506231261899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (90853 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_101 : rowCell 5 101 ≤ (46456651113040497484021573 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25660500740512700635956163 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (316326553880598506231261899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_101_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_101_1
  · norm_num [gridPoint]

theorem exp_5_102_0 : expNegUpper (6658021951600042953089 / 87096562600519731200 : ℝ) ≤ (632652560582057112763311671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (90853 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_102_1 : expNegUpper (66593162203564714734961 / 870965626005197312000 : ℝ) ≤ (623320750839635316468610061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817271 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_102 : rowCell 5 102 ≤ (91586702282391792366383621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (632652560582057112763311671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (623320750839635316468610061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_102_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_102_1
  · norm_num [gridPoint]

theorem exp_5_103_0 : expNegUpper (1427155112875172243687 / 18665625588309504000 : ℝ) ≤ (311660109741993899956256651 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817271 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_103_1 : expNegUpper (178431262059673910093 / 2333203198538688000 : ℝ) ≤ (122709392329539377203453911 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (363499 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_103 : rowCell 5 103 ≤ (90193466095980495295959781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (311660109741993899956256651 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (122709392329539377203453911 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_103_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_103_1
  · norm_num [gridPoint]

theorem exp_5_104_0 : expNegUpper (337875645251326694491 / 4418130088008256000 : ℝ) ≤ (38346652882348227402817083 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (363499 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_104_1 : expNegUpper (2703596726083567683487 / 35345040704066048000 : ℝ) ≤ (150840769397448542303113833 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817733 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_104 : rowCell 5 104 ≤ (11092266973236415066356851 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38346652882348227402817083 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (150840769397448542303113833 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_104_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_104_1
  · norm_num [gridPoint]

theorem exp_5_105_0 : expNegUpper (68076745743735806594687 / 889990470858510848000 : ℝ) ≤ (603362577854499806290923179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817733 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_105_1 : expNegUpper (34046231524429383570323 / 444995235429255424000 : ℝ) ≤ (148200170361316461106729173 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_105 : rowCell 5 105 ≤ (87225299546067188383546701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (603362577854499806290923179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (148200170361316461106729173 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_105_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_105_1
  · norm_num [gridPoint]

theorem exp_5_106_0 : expNegUpper (34290575188941572635907 / 448188881210562816000 : ℝ) ≤ (29640009872149127284025819 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_106_1 : expNegUpper (13719559843416952416889 / 179275552484225126400 : ℝ) ≤ (58189146498074695480302877 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1818247 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_106 : rowCell 5 106 ≤ (21414892852744703498683301 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29640009872149127284025819 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (58189146498074695480302877 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_106_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_106_1
  · norm_num [gridPoint]

theorem exp_5_107_0 : expNegUpper (13817670589009200331729 / 180557578457899110400 : ℝ) ≤ (290945498310082670302942741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1818247 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_107_1 : expNegUpper (17276484162276455911909 / 225696973072373888000 : ℝ) ≤ (285333548935652434095202261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454631 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_107 : rowCell 5 107 ≤ (84045571751731027305691183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (290945498310082670302942741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (285333548935652434095202261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_107_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_107_1
  · norm_num [gridPoint]

theorem exp_5_108_0 : expNegUpper (17399590859390755621061 / 227305215115905152000 : ℝ) ≤ (285333322516649957850893791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454631 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_108_1 : expNegUpper (69616885337260598559283 / 909220860463620608000 : ℝ) ≤ (559159102461205963611768133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1818813 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_108 : rowCell 5 108 ≤ (82387908585119383314670429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (285333322516649957850893791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (559159102461205963611768133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_108_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_108_1
  · norm_num [gridPoint]

theorem exp_5_109_0 : expNegUpper (2804447673910914179107 / 36627066677740032000 : ℝ) ≤ (139789666250133856933925267 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1818813 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_109_1 : expNegUpper (1402613105477754670969 / 18313533338870016000 : ℝ) ≤ (109479746965142973889454721 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (363823 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_109 : rowCell 5 109 ≤ (80691159767994078067333889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (139789666250133856933925267 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (109479746965142973889454721 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_109_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_109_1
  · norm_num [gridPoint]

theorem exp_5_110_0 : expNegUpper (35313424084007072184001 / 461077655864568064000 : ℝ) ≤ (547398312572732188340193597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454779 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_110_1 : expNegUpper (70647256451325875344201 / 922155311729136128000 : ℝ) ≤ (267708436263151710390304661 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181943 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_110 : rowCell 5 110 ≤ (78959856139189539031894019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (547398312572732188340193597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (267708436263151710390304661 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_110_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_110_1
  · norm_num [gridPoint]

theorem exp_5_111_0 : expNegUpper (71145342390625538884289 / 928656794820526592000 : ℝ) ≤ (4182941135067778397508733 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181943 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_111_1 : expNegUpper (177916747154784176689 / 2321641987051316480 : ℝ) ≤ (20929756375345994099062503 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1819757 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_111 : rowCell 5 111 ≤ (77198465661286344205552103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4182941135067778397508733 / 7812500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20929756375345994099062503 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_111_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_111_1
  · norm_num [gridPoint]

theorem exp_5_112_0 : expNegUpper (5779571331285942319 / 75417831953038080 : ℝ) ≤ (523243516948071644394745799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1819757 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_112_1 : expNegUpper (2312548145096444073281 / 30167132781215232000 : ℝ) ≤ (510909657526378227612368723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28439 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_112 : rowCell 5 112 ≤ (75411378604669576555315673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (523243516948071644394745799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (510909657526378227612368723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_112_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_112_1
  · norm_num [gridPoint]

theorem exp_5_113_0 : expNegUpper (72190884512313228710999 / 941728275920572928000 : ℝ) ≤ (6386365995753422383706777 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28439 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_113_1 : expNegUpper (36107073675946404430799 / 470864137960286464000 : ℝ) ≤ (498443256909108395313240857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1820447 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_113 : rowCell 5 113 ≤ (73602893806808923058141121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6386365995753422383706777 / 12500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (498443256909108395313240857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_113_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_113_1
  · norm_num [gridPoint]

theorem exp_5_114_0 : expNegUpper (1454359047921336349591 / 18965965478584576000 : ℝ) ≤ (498442893362313454853389413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1820447 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_114_1 : expNegUpper (2909686936638457806973 / 37931930957169152000 : ℝ) ≤ (242936546215743955699157037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1820811 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_114 : rowCell 5 114 ≤ (71777206030477482245489211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (498442893362313454853389413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (242936546215743955699157037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_114_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_114_1
  · norm_num [gridPoint]

theorem exp_5_115_0 : expNegUpper (73247898151545097790317 / 954891110243639808000 : ℝ) ≤ (121468185734476212037079959 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1820811 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_115_1 : expNegUpper (18318270170633580484739 / 238722777560909952000 : ℝ) ≤ (47322671873083427583106051 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910593 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_115 : rowCell 5 115 ≤ (17484598608951762482095779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (121468185734476212037079959 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47322671873083427583106051 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_115_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_115_1
  · norm_num [gridPoint]

theorem exp_5_116_0 : expNegUpper (18445182942771679093091 / 240376696215951488000 : ℝ) ≤ (23661319150502696558053867 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910593 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_116_1 : expNegUpper (14761375828790017176911 / 192301356972761190400 : ℝ) ≤ (9210615853302972226301823 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_116 : rowCell 5 116 ≤ (68090412172698290087146463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23661319150502696558053867 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9210615853302972226301823 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_116_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_116_1
  · norm_num [gridPoint]

theorem exp_5_117_0 : expNegUpper (14863292649406063990951 / 193629059557945446400 : ℝ) ≤ (28783154401502061349518849 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_117_1 : expNegUpper (37171789396273691870093 / 484072648894863616000 : ℝ) ≤ (223905506725418289183464583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455493 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_117 : rowCell 5 117 ≤ (66237077092207407140347383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28783154401502061349518849 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (223905506725418289183464583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_117_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_117_1
  · norm_num [gridPoint]

theorem exp_5_118_0 : expNegUpper (37427551285857277633277 / 487403324510701824000 : ℝ) ≤ (447810704385057228299544439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455493 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_118_1 : expNegUpper (74883189620664862234913 / 974806649021403648000 : ℝ) ≤ (43509207037070233297479373 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911191 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_118 : rowCell 5 118 ≤ (16095515892037920458963893 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (447810704385057228299544439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43509207037070233297479373 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_118_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_118_1
  · norm_num [gridPoint]

theorem exp_5_119_0 : expNegUpper (3015866389499122761473 / 39259633542353408000 : ℝ) ≤ (43509177416622996928238803 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911191 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_119_1 : expNegUpper (377128608103205840489 / 4907454192794176000 : ℝ) ≤ (42239759792282940615612043 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822803 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_119 : rowCell 5 119 ≤ (31264447706670972960629329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43509177416622996928238803 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42239759792282940615612043 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_119_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_119_1
  · norm_num [gridPoint]

theorem exp_5_120_0 : expNegUpper (9492643092082438499329 / 123524733300252736000 : ℝ) ≤ (105599328564342662535975479 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822803 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_120_1 : expNegUpper (75971184784814948057911 / 988197866402021888000 : ℝ) ≤ (409750138239942844221686053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455809 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_120 : rowCell 5 120 ≤ (60680939868580953064231269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (105599328564342662535975479 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (409750138239942844221686053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_120_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_120_1
  · norm_num [gridPoint]

theorem exp_5_121_0 : expNegUpper (76488567561597518869039 / 994927732550963712000 : ℝ) ≤ (81949973356864164236515619 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455809 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_121_1 : expNegUpper (7651958910552484884431 / 99492773255096371200 : ℝ) ≤ (79434222114365678677969499 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823681 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_121 : rowCell 5 121 ≤ (29420701318437997070965621 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (81949973356864164236515619 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (79434222114365678677969499 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_121_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_121_1
  · norm_num [gridPoint]

theorem exp_5_122_0 : expNegUpper (7703893820463074838911 / 100168043700566067200 : ℝ) ≤ (19858542549565215761297183 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823681 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_122_1 : expNegUpper (77070944575109517186061 / 1001680437005660672000 : ℝ) ≤ (192340393795196391101765569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228017 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_122 : rowCell 5 122 ≤ (2280532957208355623521731 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19858542549565215761297183 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (192340393795196391101765569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_122_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_122_1
  · norm_num [gridPoint]

theorem exp_5_123_0 : expNegUpper (77592266658097843283909 / 1008455979766112768000 : ℝ) ≤ (384680539545926234670745507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228017 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_123_1 : expNegUpper (19406315296476899953057 / 252113994941528192000 : ℝ) ≤ (93074569561992631127472183 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912301 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_123 : rowCell 5 123 ≤ (27599787745843781691785713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (384680539545926234670745507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (93074569561992631127472183 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_123_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_123_1
  · norm_num [gridPoint]

theorem exp_5_124_0 : expNegUpper (31259425165734980113 / 406101744332928000 : ℝ) ≤ (9307451034935416997221049 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912301 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_124_1 : expNegUpper (125092078288412389523 / 1624406977331712000 : ℝ) ≤ (3600415168944672075794071 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_124 : rowCell 5 124 ≤ (53402858551966075938614869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9307451034935416997221049 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3600415168944672075794071 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_124_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_124_1
  · norm_num [gridPoint]

theorem exp_5_125_0 : expNegUpper (78707836965688216113947 / 1022075580204282368000 : ℝ) ≤ (36004129089370966560612599 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_125_1 : expNegUpper (39371408900249297417033 / 511037790102141184000 : ℝ) ≤ (347927258337794292491259303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825567 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_125 : rowCell 5 125 ≤ (51625702675454718803798689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36004129089370966560612599 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (347927258337794292491259303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_125_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_125_1
  · norm_num [gridPoint]

theorem exp_5_126_0 : expNegUpper (39635049402244393753657 / 514459818940999936000 : ℝ) ≤ (347927042841812705669627131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (57049 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_126_1 : expNegUpper (15861215557793760137573 / 205783927576399974400 : ℝ) ≤ (335971078514684198231778713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (913033 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_126 : rowCell 5 126 ≤ (24935232724517080230088807 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (347927042841812705669627131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (335971078514684198231778713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_126_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_126_1
  · norm_num [gridPoint]

theorem exp_5_127_0 : expNegUpper (15967071684615562238333 / 207157306773094502400 : ℝ) ≤ (6719417463571125223652503 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (913033 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_127_1 : expNegUpper (624002647562554747987 / 8092082295824004000 : ℝ) ≤ (324187380425239391354772301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114161 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_127 : rowCell 5 127 ≤ (48139332963719751143183599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6719417463571125223652503 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (324187380425239391354772301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_127_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_127_1
  · norm_num [gridPoint]

theorem sum_5_96_2 : blockSum (rowCell 5) 96 2 ≤ (48964743232749320705409389 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_96) (by simpa only [blockSum_one] using cell_5_97) (by norm_num)

theorem sum_5_98_2 : blockSum (rowCell 5) 98 2 ≤ (95898888771734523716918629 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_98) (by simpa only [blockSum_one] using cell_5_99) (by norm_num)

theorem sum_5_96_4 : blockSum (rowCell 5) 96 4 ≤ (193828375237233165127737407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_96_2 sum_5_98_2 (by norm_num)

theorem sum_5_100_2 : blockSum (rowCell 5) 100 2 ≤ (187082092981321571028372131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_100) (by simpa only [blockSum_one] using cell_5_101) (by norm_num)

theorem sum_5_102_2 : blockSum (rowCell 5) 102 2 ≤ (90890084189186143831171701 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_102) (by simpa only [blockSum_one] using cell_5_103) (by norm_num)

theorem sum_5_100_4 : blockSum (rowCell 5) 100 4 ≤ (368862261359693858690715533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_100_2 sum_5_102_2 (by norm_num)

theorem sum_5_96_8 : blockSum (rowCell 5) 96 8 ≤ (756519011834160188946190347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_96_4 sum_5_100_4 (by norm_num)

theorem sum_5_104_2 : blockSum (rowCell 5) 104 2 ≤ (175963435331958508914401509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_104) (by simpa only [blockSum_one] using cell_5_105) (by norm_num)

theorem sum_5_106_2 : blockSum (rowCell 5) 106 2 ≤ (169705143162709841300424387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_106) (by simpa only [blockSum_one] using cell_5_107) (by norm_num)

theorem sum_5_104_4 : blockSum (rowCell 5) 104 4 ≤ (43208572311833543776853237 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_104_2 sum_5_106_2 (by norm_num)

theorem sum_5_108_2 : blockSum (rowCell 5) 108 2 ≤ (81539534176556730691002159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_108) (by simpa only [blockSum_one] using cell_5_109) (by norm_num)

theorem sum_5_110_2 : blockSum (rowCell 5) 110 2 ≤ (78079160900237941618723061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_110) (by simpa only [blockSum_one] using cell_5_111) (by norm_num)

theorem sum_5_108_4 : blockSum (rowCell 5) 108 4 ≤ (7980934753839733615486261 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_108_2 sum_5_110_2 (by norm_num)

theorem sum_5_104_8 : blockSum (rowCell 5) 104 8 ≤ (41556623040516105927142271 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_104_4 sum_5_108_4 (by norm_num)

theorem sum_5_96_16 : blockSum (rowCell 5) 96 16 ≤ (1421424980482417883780466683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_96_8 sum_5_104_8 (by norm_num)

theorem sum_5_112_2 : blockSum (rowCell 5) 112 2 ≤ (74507136205739249806728397 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_112) (by simpa only [blockSum_one] using cell_5_113) (by norm_num)

theorem sum_5_114_2 : blockSum (rowCell 5) 114 2 ≤ (141715600466284532173872327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_114) (by simpa only [blockSum_one] using cell_5_115) (by norm_num)

theorem sum_5_112_4 : blockSum (rowCell 5) 112 4 ≤ (290729872877763031787329121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_112_2 sum_5_114_2 (by norm_num)

theorem sum_5_116_2 : blockSum (rowCell 5) 116 2 ≤ (67163744632452848613746923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_116) (by simpa only [blockSum_one] using cell_5_117) (by norm_num)

theorem sum_5_118_2 : blockSum (rowCell 5) 118 2 ≤ (12691095898149362775711423 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_118) (by simpa only [blockSum_one] using cell_5_119) (by norm_num)

theorem sum_5_116_4 : blockSum (rowCell 5) 116 4 ≤ (65309612061599831246152019 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_116_2 sum_5_118_2 (by norm_num)

theorem sum_5_112_8 : blockSum (rowCell 5) 112 8 ≤ (551968321124162356771937197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_112_4 sum_5_116_4 (by norm_num)

theorem sum_5_120_2 : blockSum (rowCell 5) 120 2 ≤ (119522342505456947206162511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_120) (by simpa only [blockSum_one] using cell_5_121) (by norm_num)

theorem sum_5_122_2 : blockSum (rowCell 5) 122 2 ≤ (112212899421896453971614701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_122) (by simpa only [blockSum_one] using cell_5_123) (by norm_num)

theorem sum_5_120_4 : blockSum (rowCell 5) 120 4 ≤ (57933810481838350294444303 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_120_2 sum_5_122_2 (by norm_num)

theorem sum_5_124_2 : blockSum (rowCell 5) 124 2 ≤ (52514280613710397371206779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_124) (by simpa only [blockSum_one] using cell_5_125) (by norm_num)

theorem sum_5_126_2 : blockSum (rowCell 5) 126 2 ≤ (98009798412753911603361213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_126) (by simpa only [blockSum_one] using cell_5_127) (by norm_num)

theorem sum_5_124_4 : blockSum (rowCell 5) 124 4 ≤ (203038359640174706345774771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_124_2 sum_5_126_2 (by norm_num)

theorem sum_5_120_8 : blockSum (rowCell 5) 120 8 ≤ (434773601567528107523551983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_120_4 sum_5_124_4 (by norm_num)

theorem sum_5_112_16 : blockSum (rowCell 5) 112 16 ≤ (49337096134584523214774459 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_112_8 sum_5_120_8 (by norm_num)

theorem sum_5_96_32 : blockSum (rowCell 5) 96 32 ≤ (2408166903174108348075955863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_96_16 sum_5_112_16 (by norm_num)

#print axioms sum_5_96_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
