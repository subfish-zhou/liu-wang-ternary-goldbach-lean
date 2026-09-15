import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_96_0 : expNegUpper (1968886532499449535677 / 26047892829811216000 : ℝ) ≤ (1490536995395152476979472647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (360987 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_96_1 : expNegUpper (12602855933650103244707 / 166706514110791782400 : ℝ) ≤ (294583917021959194906863619 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1805103 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_96 : rowCell 4 96 ≤ (54024479082735597124752507 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1490536995395152476979472647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (294583917021959194906863619 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_96_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_96_1
  · norm_num [gridPoint]

theorem exp_4_97_0 : expNegUpper (12696322937491158247867 / 167942863472955494400 : ℝ) ≤ (1472918243580984647117883291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1805103 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_97_1 : expNegUpper (31746213436393319200343 / 419857158682388736000 : ℝ) ≤ (1454074483304355520894830357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451321 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_97 : rowCell 4 97 ≤ (213438939364507066099294279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1472918243580984647117883291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1454074483304355520894830357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_97_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_97_1
  · norm_num [gridPoint]

theorem exp_4_98_0 : expNegUpper (31980784168448447242567 / 422959451240675584000 : ℝ) ≤ (363518294582882118687727133 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451321 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_98_1 : expNegUpper (63973285410070006635653 / 845918902481351168000 : ℝ) ≤ (179258903312176815661643717 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45137 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_98 : rowCell 4 98 ≤ (210606084817365237066689331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (363518294582882118687727133 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (179258903312176815661643717 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_98_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_98_1
  · norm_num [gridPoint]

theorem exp_4_99_0 : expNegUpper (103110783969030946573 / 1363434121445888000 : ℝ) ≤ (717034979126552300623446669 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45137 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_99_1 : expNegUpper (25782746108975707063 / 340858530361472000 : ℝ) ≤ (706489790877218417841672733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1805689 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_99 : rowCell 4 99 ≤ (51902352588355255526615689 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (717034979126552300623446669 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (706489790877218417841672733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_99_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_99_1
  · norm_num [gridPoint]

theorem exp_4_100_0 : expNegUpper (16232409902759194834343 / 214599146907940992000 : ℝ) ≤ (44155573447717801141035133 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1805689 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_100_1 : expNegUpper (64943176452233068195291 / 858396587631763968000 : ℝ) ≤ (1390870578891326728547908641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1805911 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_100 : rowCell 4 100 ≤ (51114795750405128875847751 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (44155573447717801141035133 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1390870578891326728547908641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_100_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_100_1
  · norm_num [gridPoint]

theorem exp_4_101_0 : expNegUpper (65417777220412854401939 / 864669687665603072000 : ℝ) ≤ (1390869384288288262644216613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1805911 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_101_1 : expNegUpper (6543222894179005497809 / 86466968766560307200 : ℝ) ≤ (1367816172431286377986631999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806147 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_101 : rowCell 4 101 ≤ (201165829302546248037642673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1390869384288288262644216613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1367816172431286377986631999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_101_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_101_1
  · norm_num [gridPoint]

theorem exp_4_102_0 : expNegUpper (286559403483092232743 / 3786807069587814400 : ℝ) ≤ (273563002916631184385302189 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806147 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_102_1 : expNegUpper (2866262292758646727607 / 37868070695878144000 : ℝ) ≤ (335972228219619033528156781 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451599 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_102 : rowCell 4 102 ≤ (24717485835874942292053037 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (273563002916631184385302189 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (335972228219619033528156781 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_102_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_102_1
  · norm_num [gridPoint]

theorem exp_4_103_0 : expNegUpper (66402306345470503453289 / 877284402650546688000 : ℝ) ≤ (335971947910599019728046497 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451599 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_103_1 : expNegUpper (8302324727443521774371 / 109660550331318336000 : ℝ) ≤ (131916162888963162335336073 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (903329 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_103 : rowCell 4 103 ≤ (194191956328659219292842421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (335971947910599019728046497 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (131916162888963162335336073 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_103_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_103_1
  · norm_num [gridPoint]

theorem exp_4_104_0 : expNegUpper (334493589229146854491 / 4418130088008256000 : ℝ) ≤ (329790136013321735292756491 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (903329 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_104_1 : expNegUpper (2676637367697064003487 / 35345040704066048000 : ℝ) ≤ (646853560881663069501592289 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806933 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_104 : rowCell 4 104 ≤ (47633164422410233229904413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (329790136013321735292756491 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (646853560881663069501592289 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_104_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_104_1
  · norm_num [gridPoint]

theorem exp_4_105_0 : expNegUpper (67397907294526462594687 / 889990470858510848000 : ℝ) ≤ (1293706073048907120486336733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806933 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_105_1 : expNegUpper (33708025922211399570323 / 444995235429255424000 : ℝ) ≤ (633798936751468885805285359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807221 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_105 : rowCell 4 105 ≤ (37354516990815001940970347 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1293706073048907120486336733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (633798936751468885805285359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_105_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_105_1
  · norm_num [gridPoint]

theorem exp_4_106_0 : expNegUpper (33949942341950212635907 / 448188881210562816000 : ℝ) ≤ (316899215142790205064155883 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807221 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_106_1 : expNegUpper (13583792153575083616889 / 179275552484225126400 : ℝ) ≤ (620452884772612141052135439 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_106 : rowCell 4 106 ≤ (182922265520918546853896823 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (316899215142790205064155883 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (620452884772612141052135439 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_106_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_106_1
  · norm_num [gridPoint]

theorem exp_4_107_0 : expNegUpper (13680932001257981131729 / 180557578457899110400 : ℝ) ≤ (4847284343747604658574569 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_107_1 : expNegUpper (17106167738780775911909 / 225696973072373888000 : ℝ) ≤ (1213701837083252968644402249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (903917 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_107 : rowCell 4 107 ≤ (178992120703349407823744239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4847284343747604658574569 / 3906250000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1213701837083252968644402249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_107_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_107_1
  · norm_num [gridPoint]

theorem exp_4_108_0 : expNegUpper (17228060813508387621061 / 227305215115905152000 : ℝ) ≤ (606850447236649821614383571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (903917 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_108_1 : expNegUpper (68933192398504502559283 / 909220860463620608000 : ℝ) ≤ (1186055999751688955800211903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11301 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_108 : rowCell 4 108 ≤ (174992428758470823904387593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (606850447236649821614383571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1186055999751688955800211903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_108_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_108_1
  · norm_num [gridPoint]

theorem exp_4_109_0 : expNegUpper (2776905776778800259107 / 36627066677740032000 : ℝ) ≤ (593027545789134154586877051 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11301 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_109_1 : expNegUpper (1388890701807165230969 / 18313533338870016000 : ℝ) ≤ (1158036849285400958363886593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (904249 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_109 : rowCell 4 109 ≤ (170933290347881882691702313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (593027545789134154586877051 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1158036849285400958363886593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_109_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_109_1
  · norm_num [gridPoint]

theorem exp_4_110_0 : expNegUpper (34967936747468960184001 / 461077655864568064000 : ℝ) ≤ (115803597500389221059805987 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (904249 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_110_1 : expNegUpper (69958709023023027344201 / 922155311729136128000 : ℝ) ≤ (1129711434610157651149841403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (113053 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_110 : rowCell 4 110 ≤ (1334596772056958728332637 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (115803597500389221059805987 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1129711434610157651149841403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_110_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_110_1
  · norm_num [gridPoint]

theorem exp_4_111_0 : expNegUpper (70451940472775938884289 / 928656794820526592000 : ℝ) ≤ (141213824204331211795342009 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (113053 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_111_1 : expNegUpper (176189310472093616689 / 2321641987051316480 : ℝ) ≤ (1101145068677887951706021701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (180921 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_111 : rowCell 4 111 ≤ (162675999180214354071875207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (141213824204331211795342009 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1101145068677887951706021701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_111_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_111_1
  · norm_num [gridPoint]

theorem exp_4_112_0 : expNegUpper (5723456076235702319 / 75417831953038080 : ℝ) ≤ (110114426038509358458980503 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (180921 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_112_1 : expNegUpper (2290180341294844073281 / 30167132781215232000 : ℝ) ≤ (107240115321946000626767769 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1809583 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_112 : rowCell 4 112 ≤ (79248442177375791593222213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (110114426038509358458980503 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (107240115321946000626767769 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_112_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_112_1
  · norm_num [gridPoint]

theorem exp_4_113_0 : expNegUpper (71492628104916876710999 / 941728275920572928000 : ℝ) ≤ (1072400376952550147530234211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1809583 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_113_1 : expNegUpper (35759159094634916430799 / 470864137960286464000 : ℝ) ≤ (13044262768199497951730133 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1809969 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_113 : rowCell 4 113 ≤ (30859269562609736130961207 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1072400376952550147530234211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13044262768199497951730133 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_113_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_113_1
  · norm_num [gridPoint]

theorem exp_4_114_0 : expNegUpper (1440345374877941789591 / 18965965478584576000 : ℝ) ≤ (1043540276528303940670167857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1809969 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_114_1 : expNegUpper (2881756680342603726973 / 37931930957169152000 : ℝ) ≤ (507311899342827544918722607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1810367 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_114 : rowCell 4 114 ≤ (150083173496388217545931617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1043540276528303940670167857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (507311899342827544918722607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_114_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_114_1
  · norm_num [gridPoint]

theorem exp_4_115_0 : expNegUpper (72544787254601993790317 / 954891110243639808000 : ℝ) ≤ (31706971387014234011030977 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1810367 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_115_1 : expNegUpper (18143099257591148484739 / 238722777560909952000 : ℝ) ≤ (492853140274359749183768157 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226347 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_115 : rowCell 4 115 ≤ (145865814461840927181063003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31706971387014234011030977 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (492853140274359749183768157 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_115_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_115_1
  · norm_num [gridPoint]

theorem exp_4_116_0 : expNegUpper (18268798407342559093091 / 240376696215951488000 : ℝ) ≤ (492852798069264425937402109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226347 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_116_1 : expNegUpper (14620753649401396376911 / 192301356972761190400 : ℝ) ≤ (191368565733151023711183833 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452799 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_116 : rowCell 4 116 ≤ (141652376395078797222688033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (492852798069264425937402109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (191368565733151023711183833 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_116_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_116_1
  · norm_num [gridPoint]

theorem exp_4_117_0 : expNegUpper (14721699572108092790951 / 193629059557945446400 : ℝ) ≤ (478421086695933806931825119 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452799 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_117_1 : expNegUpper (36819020325415451870093 / 484072648894863616000 : ℝ) ≤ (464042641624725958202933637 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452907 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_117 : rowCell 4 117 ≤ (68725301813898423166384347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (478421086695933806931825119 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (464042641624725958202933637 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_117_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_117_1
  · norm_num [gridPoint]

theorem exp_4_118_0 : expNegUpper (37072354970225661633277 / 487403324510701824000 : ℝ) ≤ (928084656341160219687451393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452907 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_118_1 : expNegUpper (74175224234175006234913 / 974806649021403648000 : ℝ) ≤ (224870723050381951045097453 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_118 : rowCell 4 118 ≤ (5330714703798088180868577 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (928084656341160219687451393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (224870723050381951045097453 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_118_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_118_1
  · norm_num [gridPoint]

theorem exp_4_119_0 : expNegUpper (2987353594457658441473 / 39259633542353408000 : ℝ) ≤ (449741146437619564575231337 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_119_1 : expNegUpper (373576644946889680489 / 4907454192794176000 : ℝ) ≤ (871082256129454686580688589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72501 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_119 : rowCell 4 119 ≤ (64555578827504634723857811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (449741146437619564575231337 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (871082256129454686580688589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_119_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_119_1
  · norm_num [gridPoint]

theorem exp_4_120_0 : expNegUpper (9403237201981190499329 / 123524733300252736000 : ℝ) ≤ (871081683591660615950650033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72501 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_120_1 : expNegUpper (75258364908778340057911 / 988197866402021888000 : ℝ) ≤ (210731822162340147936134873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812991 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_120 : rowCell 4 120 ≤ (124987074185751264257624509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (871081683591660615950650033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (210731822162340147936134873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_120_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_120_1
  · norm_num [gridPoint]

theorem exp_4_121_0 : expNegUpper (75770893196014158869039 / 994927732550963712000 : ℝ) ≤ (842926742099456510167954239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812991 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_121_1 : expNegUpper (7580434198471486484431 / 99492773255096371200 : ℝ) ≤ (815059191282781319725958591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1813467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_121 : rowCell 4 121 ≤ (120901823858969805660164419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (842926742099456510167954239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (815059191282781319725958591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_121_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_121_1
  · norm_num [gridPoint]

theorem exp_4_122_0 : expNegUpper (7631883659427401238911 / 100168043700566067200 : ℝ) ≤ (815058669915732469267432377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1813467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_122_1 : expNegUpper (76353270209526157186061 / 1001680437005660672000 : ℝ) ≤ (393758221102707980601914573 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (906977 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_122 : rowCell 4 122 ≤ (7303826061840714993391087 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (815058669915732469267432377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (393758221102707980601914573 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_122_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_122_1
  · norm_num [gridPoint]

theorem exp_4_123_0 : expNegUpper (76869737802967731283909 / 1008455979766112768000 : ℝ) ≤ (98439493151783526654729763 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (906977 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_123_1 : expNegUpper (19226289893887715953057 / 252113994941528192000 : ℝ) ≤ (152066959613089673043276241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (453613 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_123 : rowCell 4 123 ≤ (112870666847109098271245127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (98439493151783526654729763 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (152066959613089673043276241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_123_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_123_1
  · norm_num [gridPoint]

theorem exp_4_124_0 : expNegUpper (30969442725773584913 / 406101744332928000 : ℝ) ≤ (380167162321841406616522343 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (453613 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_124_1 : expNegUpper (123936032120204210323 / 1624406977331712000 : ℝ) ≤ (733547308056999494778630987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (22687 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_124 : rowCell 4 124 ≤ (21787038163162626683894499 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (380167162321841406616522343 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (733547308056999494778630987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_124_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_124_1
  · norm_num [gridPoint]

theorem exp_4_125_0 : expNegUpper (3390454505261363135389 / 44438068704534016000 : ℝ) ≤ (733546857400730909305432759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (22687 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_125_1 : expNegUpper (1696040471752067539871 / 22219034352267008000 : ℝ) ≤ (7071843394104895018412751 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_125 : rowCell 4 125 ≤ (105059413278408827461656077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (733546857400730909305432759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7071843394104895018412751 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_125_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_125_1
  · norm_num [gridPoint]

theorem exp_4_126_0 : expNegUpper (39270144107519273753657 / 514459818940999936000 : ℝ) ≤ (707183910720509550802412527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_126_1 : expNegUpper (15715738888858387337573 / 205783927576399974400 : ℝ) ≤ (170318403361421263710937909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816009 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_126 : rowCell 4 126 ≤ (101247570104505778709184301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (707183910720509550802412527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (170318403361421263710937909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_126_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_126_1
  · norm_num [gridPoint]

theorem exp_4_127_0 : expNegUpper (15820624117770839038333 / 207157306773094502400 : ℝ) ≤ (136254641185870396016710813 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816009 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_127_1 : expNegUpper (618301002332474747987 / 8092082295824004000 : ℝ) ≤ (655840251324522665565761639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816549 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_127 : rowCell 4 127 ≤ (24375878653956072672187513 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (136254641185870396016710813 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (655840251324522665565761639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_127_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_127_1
  · norm_num [gridPoint]

theorem sum_4_96_2 : blockSum (rowCell 4) 96 2 ≤ (429536855695449454598304307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_96) (by simpa only [blockSum_one] using cell_4_97) (by norm_num)

theorem sum_4_98_2 : blockSum (rowCell 4) 98 2 ≤ (418215495170786259173152087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_98) (by simpa only [blockSum_one] using cell_4_99) (by norm_num)

theorem sum_4_96_4 : blockSum (rowCell 4) 96 4 ≤ (423876175433117856885728197 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_96_2 sum_4_98_2 (by norm_num)

theorem sum_4_100_2 : blockSum (rowCell 4) 100 2 ≤ (405625012304166763541033677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_100) (by simpa only [blockSum_one] using cell_4_101) (by norm_num)

theorem sum_4_102_2 : blockSum (rowCell 4) 102 2 ≤ (391931843015658757629266717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_102) (by simpa only [blockSum_one] using cell_4_103) (by norm_num)

theorem sum_4_100_4 : blockSum (rowCell 4) 100 4 ≤ (398778427659912760585150197 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_100_2 sum_4_102_2 (by norm_num)

theorem sum_4_96_8 : blockSum (rowCell 4) 96 8 ≤ (411327301546515308735439197 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_96_4 sum_4_100_4 (by norm_num)

theorem sum_4_104_2 : blockSum (rowCell 4) 104 2 ≤ (377305242643715942624469387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_104) (by simpa only [blockSum_one] using cell_4_105) (by norm_num)

theorem sum_4_106_2 : blockSum (rowCell 4) 106 2 ≤ (180957193112133977338820531 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_106) (by simpa only [blockSum_one] using cell_4_107) (by norm_num)

theorem sum_4_104_4 : blockSum (rowCell 4) 104 4 ≤ (739219628867983897302110449 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_104_2 sum_4_106_2 (by norm_num)

theorem sum_4_108_2 : blockSum (rowCell 4) 108 2 ≤ (172962859553176353298044953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_108) (by simpa only [blockSum_one] using cell_4_109) (by norm_num)

theorem sum_4_110_2 : blockSum (rowCell 4) 110 2 ≤ (20593787230458387194590927 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_110) (by simpa only [blockSum_one] using cell_4_111) (by norm_num)

theorem sum_4_108_4 : blockSum (rowCell 4) 108 4 ≤ (337713157396843450854772369 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_108_2 sum_4_110_2 (by norm_num)

theorem sum_4_104_8 : blockSum (rowCell 4) 104 8 ≤ (1414645943661670799011655187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_104_4 sum_4_108_4 (by norm_num)

theorem sum_4_96_16 : blockSum (rowCell 4) 96 16 ≤ (122398205993909281358136479 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_96_8 sum_4_104_8 (by norm_num)

theorem sum_4_112_2 : blockSum (rowCell 4) 112 2 ≤ (312793232167800263841250461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_112) (by simpa only [blockSum_one] using cell_4_113) (by norm_num)

theorem sum_4_114_2 : blockSum (rowCell 4) 114 2 ≤ (14797449397911457236349731 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_114) (by simpa only [blockSum_one] using cell_4_115) (by norm_num)

theorem sum_4_112_4 : blockSum (rowCell 4) 112 4 ≤ (608742220126029408568245081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_112_2 sum_4_114_2 (by norm_num)

theorem sum_4_116_2 : blockSum (rowCell 4) 116 2 ≤ (279102980022875643555456727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_116) (by simpa only [blockSum_one] using cell_4_117) (by norm_num)

theorem sum_4_118_2 : blockSum (rowCell 4) 118 2 ≤ (262379025249961473969430047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_118) (by simpa only [blockSum_one] using cell_4_119) (by norm_num)

theorem sum_4_116_4 : blockSum (rowCell 4) 116 4 ≤ (270741002636418558762443387 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_116_2 sum_4_118_2 (by norm_num)

theorem sum_4_112_8 : blockSum (rowCell 4) 112 8 ≤ (230044845079773305218626371 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_112_4 sum_4_116_4 (by norm_num)

theorem sum_4_120_2 : blockSum (rowCell 4) 120 2 ≤ (960503507987191679366363 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_120) (by simpa only [blockSum_one] using cell_4_121) (by norm_num)

theorem sum_4_122_2 : blockSum (rowCell 4) 122 2 ≤ (229731883836560538165502519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_122) (by simpa only [blockSum_one] using cell_4_123) (by norm_num)

theorem sum_4_120_4 : blockSum (rowCell 4) 120 4 ≤ (475620781881281608083291447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_120_2 sum_4_122_2 (by norm_num)

theorem sum_4_124_2 : blockSum (rowCell 4) 124 2 ≤ (53498651023555490220282143 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_124) (by simpa only [blockSum_one] using cell_4_125) (by norm_num)

theorem sum_4_126_2 : blockSum (rowCell 4) 126 2 ≤ (198751084720330069397934353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_126) (by simpa only [blockSum_one] using cell_4_127) (by norm_num)

theorem sum_4_124_4 : blockSum (rowCell 4) 124 4 ≤ (16509827552582081211162517 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_124_2 sum_4_126_2 (by norm_num)

theorem sum_4_120_8 : blockSum (rowCell 4) 120 8 ≤ (222091617673958409590588593 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_120_4 sum_4_124_4 (by norm_num)

theorem sum_4_112_16 : blockSum (rowCell 4) 112 16 ≤ (2038590696094700164455486227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_112_8 sum_4_120_8 (by norm_num)

theorem sum_4_96_32 : blockSum (rowCell 4) 96 32 ≤ (2549272922971216099204449101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_96_16 sum_4_112_16 (by norm_num)

#print axioms sum_4_96_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
