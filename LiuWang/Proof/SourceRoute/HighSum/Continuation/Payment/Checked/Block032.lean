import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_0_0 : expNegUpper (51917067018165940881 / 676601617795489000 : ℝ) ≤ (237177717773068835751325039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (56911 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_0_1 : expNegUpper (26530116552221576690191 / 346420028311290368000 : ℝ) ≤ (550261992478463768654099117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1819041 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_0 : rowCell 2 0 ≤ (74716023406274427869086543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (237177717773068835751325039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (550261992478463768654099117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_0_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_0_1
  · norm_num [gridPoint]

theorem exp_2_1_0 : expNegUpper (8945210373840369376813 / 116803099256538624000 : ℝ) ≤ (275129676990692546287159477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1819041 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_1_1 : expNegUpper (892826372088924794633 / 11680309925653862400 : ℝ) ≤ (6361771591620574979865279 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816981 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_1 : rowCell 2 1 ≤ (8651601647747461101539941 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (275129676990692546287159477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6361771591620574979865279 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_1_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_1_1
  · norm_num [gridPoint]

theorem exp_2_2_0 : expNegUpper (2709147266719886568779 / 35442140553369651200 : ℝ) ≤ (636174177569837263195787599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816981 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_2_1 : expNegUpper (27041217841351071055461 / 354421405533696512000 : ℝ) ≤ (733088463631499991560319397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1814969 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_2 : rowCell 2 2 ≤ (99847861993305716943255143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (636174177569837263195787599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (733088463631499991560319397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_2_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_2_1
  · norm_num [gridPoint]

theorem exp_2_3_0 : expNegUpper (27349072942672881132189 / 358456351603532288000 : ℝ) ≤ (146617020994483865551624247 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1814969 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_3_1 : expNegUpper (6824851645152551267167 / 89614087900883072000 : ℝ) ≤ (21050800330374772930176329 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (906503 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_3 : rowCell 2 3 ≤ (57429477701255913282126239 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (146617020994483865551624247 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21050800330374772930176329 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_3_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_3_1
  · norm_num [gridPoint]

theorem exp_2_4_0 : expNegUpper (92028139800939337309 / 1208380453263744000 : ℝ) ≤ (168405648309912940337706989 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (906503 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_4_1 : expNegUpper (367458231637117234769 / 4833521813054976000 : ℝ) ≤ (964091679183238183583381279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1811089 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_4 : rowCell 2 4 ≤ (8231492956606391860726273 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (168405648309912940337706989 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (964091679183238183583381279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_4_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_4_1
  · norm_num [gridPoint]

theorem exp_2_5_0 : expNegUpper (3981369950337753228341 / 52370679808638464000 : ℝ) ≤ (60255466040706667711271697 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1811089 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_5_1 : expNegUpper (1987222157872177171539 / 26185339904319232000 : ℝ) ≤ (550197567565683676425251259 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1809219 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_5 : rowCell 2 5 ≤ (30108785080274229093631597 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (60255466040706667711271697 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (550197567565683676425251259 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_5_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_5_1
  · norm_num [gridPoint]

theorem exp_2_6_0 : expNegUpper (14066263035629471039157 / 185349109823785216000 : ℝ) ≤ (220078084403924876902727751 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1809219 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_6_1 : expNegUpper (5616929017045783035869 / 74139643929514086400 : ℝ) ≤ (250421810834799553378762521 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (903697 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_6 : rowCell 2 6 ≤ (171546375377787069988033009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (220078084403924876902727751 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (250421810834799553378762521 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_6_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_6_1
  · norm_num [gridPoint]

theorem exp_2_7_0 : expNegUpper (1893150745953630424103 / 24988301262695116800 : ℝ) ≤ (1252103809004700396532797423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (903697 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_7_1 : expNegUpper (1181249249590739319589 / 15617688289184448000 : ℝ) ≤ (710216726632720901645730141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902807 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_7 : rowCell 2 7 ≤ (194883818272435340042067527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1252103809004700396532797423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (710216726632720901645730141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_7_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_7_1
  · norm_num [gridPoint]

theorem exp_2_8_0 : expNegUpper (3582975624854932772143 / 47371707067379776000 : ℝ) ≤ (177553454113352659168701607 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902807 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_8_1 : expNegUpper (28617130917395612602983 / 378973656539038208000 : ℝ) ≤ (321319036892237860345975731 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (901939 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_8 : rowCell 2 8 ≤ (220733223433287810206797569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (177553454113352659168701607 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (321319036892237860345975731 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_8_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_8_1
  · norm_num [gridPoint]

theorem exp_2_9_0 : expNegUpper (1157286699688104250167 / 15325825297736192000 : ℝ) ≤ (1606588744259838609859043437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (901939 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_9_1 : expNegUpper (577722037184423374139 / 7662912648868096000 : ℝ) ≤ (905920292584866974493142683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (225273 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_9 : rowCell 2 9 ≤ (124637468973552545186298607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1606588744259838609859043437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (905920292584866974493142683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_9_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_9_1
  · norm_num [gridPoint]

theorem exp_2_10_0 : expNegUpper (4867059776955422553617 / 64556741108921088000 : ℝ) ≤ (113239592444061731184822963 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (225273 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_10_1 : expNegUpper (9718968269331019570367 / 129113482217842176000 : ℝ) ≤ (407485462443524588276092277 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1800533 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_10 : rowCell 2 10 ≤ (28069155522348697180141707 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (113239592444061731184822963 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (407485462443524588276092277 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_10_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_10_1
  · norm_num [gridPoint]

theorem exp_2_11_0 : expNegUpper (29474388499767896108789 / 391558099169403392000 : ℝ) ≤ (127338718317354594157178487 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1800533 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_11_1 : expNegUpper (58859099512099858689 / 783116198338806784 : ℝ) ≤ (1142307698829377969095792541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1798923 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_11 : rowCell 2 11 ≤ (315166667310722581118822897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (127338718317354594157178487 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1142307698829377969095792541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_11_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_11_1
  · norm_num [gridPoint]

theorem exp_2_12_0 : expNegUpper (8499504856756381527 / 113085311426010112 : ℝ) ≤ (71393963038686584768084947 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1798923 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_12_1 : expNegUpper (4243435242247203905173 / 56542655713005056000 : ℝ) ≤ (2554657577479995072125155431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1797353 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_12 : rowCell 2 12 ≤ (5513804803741229600671737 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (71393963038686584768084947 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2554657577479995072125155431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_12_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_12_1
  · norm_num [gridPoint]

theorem exp_2_13_0 : expNegUpper (10008001383569833252633 / 133353973039474176000 : ℝ) ≤ (2554648186796616960536821849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1797353 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_13_1 : expNegUpper (4996734269895533235883 / 66676986519737088000 : ℝ) ≤ (142439447872864998476541233 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112239 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_13 : rowCell 2 13 ≤ (197011745604777456584512321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2554648186796616960536821849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (142439447872864998476541233 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_13_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_13_1
  · norm_num [gridPoint]

theorem exp_2_14_0 : expNegUpper (606032198965860721561 / 8086961731031296000 : ℝ) ≤ (2848778706990431763177510703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112239 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_14_1 : expNegUpper (1210345460772675692433 / 16173923462062592000 : ℝ) ≤ (1584108046581277492098134597 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1794333 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_14 : rowCell 2 14 ≤ (219382333360460778033763437 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2848778706990431763177510703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1584108046581277492098134597 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_14_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_14_1
  · norm_num [gridPoint]

theorem exp_2_15_0 : expNegUpper (30581094383736591034017 / 408657092290462208000 : ℝ) ≤ (158410246655352621497220083 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897167 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_15_1 : expNegUpper (1908671836743759546991 / 25541068268153888000 : ℝ) ≤ (351410557327316791999039761 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896441 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_15 : rowCell 2 15 ≤ (15227502680112226371764569 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (158410246655352621497220083 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (351410557327316791999039761 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_15_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_15_1
  · norm_num [gridPoint]

theorem exp_2_16_0 : expNegUpper (642968071862058569893 / 8603936173648224000 : ℝ) ≤ (3514093453810800632458772027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896441 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_16_1 : expNegUpper (2054716947830775164497 / 27532595755674316800 : ℝ) ≤ (1943786103330558472789615481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1791467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_16 : rowCell 2 16 ≤ (539736109895604060028980197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3514093453810800632458772027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1943786103330558472789615481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_16_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_16_1
  · norm_num [gridPoint]

theorem exp_2_17_0 : expNegUpper (6229147827511668753931 / 83468723737104486400 : ℝ) ≤ (3887559078246105235213628753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1791467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_17_1 : expNegUpper (15552330500169981593343 / 208671809342761216000 : ℝ) ≤ (4289666924011748857845816303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (179009 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_17 : rowCell 2 17 ≤ (596290666811129124006681467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3887559078246105235213628753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4289666924011748857845816303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_17_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_17_1
  · norm_num [gridPoint]

theorem exp_2_18_0 : expNegUpper (15715459720306917503727 / 210860569670842624000 : ℝ) ≤ (4289652737668552250610773229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (179009 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_18_1 : expNegUpper (31390479728873806638613 / 421721139341685248000 : ℝ) ≤ (4721364513736122131850946703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1431 / 800 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_18 : rowCell 2 18 ≤ (657091473808240664856249111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4289652737668552250610773229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4721364513736122131850946703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_18_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_18_1
  · norm_num [gridPoint]

theorem exp_2_19_0 : expNegUpper (1948879775783958943 / 26182580540928000 : ℝ) ≤ (944269844273429149745282031 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1431 / 800 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_19_1 : expNegUpper (486608608224298073 / 6545645135232000 : ℝ) ≤ (647943914937993317015516723 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (357489 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_19 : rowCell 2 19 ≤ (144454849274879947656655267 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (944269844273429149745282031 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (647943914937993317015516723 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_19_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_19_1
  · norm_num [gridPoint]

theorem exp_2_20_0 : expNegUpper (8001761465176820217083 / 107636173892819072000 : ℝ) ≤ (1295883718551162033232881427 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (357489 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_20_1 : expNegUpper (31967892992262603656811 / 430544695571276288000 : ℝ) ≤ (1135402606534068296494750077 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27909 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_20 : rowCell 2 20 ≤ (197990227723208581438458831 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1295883718551162033232881427 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1135402606534068296494750077 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_20_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_20_1
  · norm_num [gridPoint]

theorem exp_2_21_0 : expNegUpper (32298011962422528949539 / 434990731144704512000 : ℝ) ≤ (2838497694524533971939256507 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27909 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_21_1 : expNegUpper (3225950751179485068121 / 43499073114470451200 : ℝ) ≤ (775302839632345459473960837 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1784941 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_21 : rowCell 2 21 ≤ (866257841212087787961321761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2838497694524533971939256507 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (775302839632345459473960837 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_21_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_21_1
  · norm_num [gridPoint]

theorem exp_2_22_0 : expNegUpper (1086364221612277425667 / 14648653500796262400 : ℝ) ≤ (193825119736203867086410529 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1784941 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_22_1 : expNegUpper (10851024648779064118187 / 146486535007962624000 : ℝ) ≤ (845041150735569697120580261 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (89187 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_22 : rowCell 2 22 ≤ (37810165571832512715790091 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (193825119736203867086410529 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (845041150735569697120580261 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_22_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_22_1
  · norm_num [gridPoint]

theorem exp_2_23_0 : expNegUpper (32885799910883309058809 / 443951317208826368000 : ℝ) ≤ (1690077259275962425733850993 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (89187 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_23_1 : expNegUpper (4106075286028534425741 / 55493914651103296000 : ℝ) ≤ (3675573005490526564826068429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1782573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_23 : rowCell 2 23 ≤ (1029019980366745878332172131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1690077259275962425733850993 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3675573005490526564826068429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_23_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_23_1
  · norm_num [gridPoint]

theorem exp_2_24_0 : expNegUpper (6636528348461226909 / 89693173539904000 : ℝ) ≤ (7351124519990814997688113509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1782573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_24_1 : expNegUpper (53033764047690794503 / 717545388319232000 : ℝ) ≤ (7975140882879437941808235937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1781439 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_24 : rowCell 2 24 ≤ (1117605042868871735590949131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7351124519990814997688113509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7975140882879437941808235937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_24_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_24_1
  · norm_num [gridPoint]

theorem exp_2_25_0 : expNegUpper (11160487378325148652549 / 151001085498656256000 : ℝ) ≤ (1993779508383292153368182749 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1781439 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_25_1 : expNegUpper (5574264110568542093161 / 75500542749328128000 : ℝ) ≤ (863242615668624912234531479 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1780337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_25 : rowCell 2 25 ≤ (1211037043191283341553973923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1993779508383292153368182749 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (863242615668624912234531479 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_25_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_25_1
  · norm_num [gridPoint]

theorem exp_2_26_0 : expNegUpper (2413019362944992144701 / 32683105971298048000 : ℝ) ≤ (1726480383184075173446063533 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1780337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_26_1 : expNegUpper (964201676610869717679 / 13073242388519219200 : ℝ) ≤ (9322950013124959520748611127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1779267 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_26 : rowCell 2 26 ≤ (10474563155419876865279489 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1726480383184075173446063533 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9322950013124959520748611127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_26_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_26_1
  · norm_num [gridPoint]

theorem exp_2_27_0 : expNegUpper (6817015714681622695713 / 92429309801226342400 : ℝ) ≤ (9322924351246579341490695263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1779267 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_27_1 : expNegUpper (8512633644013238993209 / 115536637251532928000 : ℝ) ≤ (19622048391840092842840337 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444557 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_27 : rowCell 2 27 ≤ (706217503745646587506997011 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9322924351246579341490695263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19622048391840092842840337 / 1953125000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_27_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_27_1
  · norm_num [gridPoint]

theorem exp_2_28_0 : expNegUpper (2865824550320730253747 / 38896037726653824000 : ℝ) ≤ (5023230833790673538895028263 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444557 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_28_1 : expNegUpper (11452007446589148950081 / 155584150906615296000 : ℝ) ≤ (1350330045377333794416876039 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1777221 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_28 : rowCell 2 28 ≤ (760167625843229444213321151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5023230833790673538895028263 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1350330045377333794416876039 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_28_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_28_1
  · norm_num [gridPoint]

theorem exp_2_29_0 : expNegUpper (1387869166595619418163 / 18855247789572608000 : ℝ) ≤ (10802611784662896015895062477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1777221 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_29_1 : expNegUpper (693270639297251189601 / 9427623894786304000 : ℝ) ≤ (1448852372312394681375450273 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1776243 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_29 : rowCell 2 29 ≤ (816474545173864108606831147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10802611784662896015895062477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1448852372312394681375450273 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_29_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_29_1
  · norm_num [gridPoint]

theorem exp_2_30_0 : expNegUpper (17502796124435963717481 / 238016387532269824000 : ℝ) ≤ (724424307050428006489661109 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1776243 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_30_1 : expNegUpper (34973073443676940591321 / 476032775064539648000 : ℝ) ≤ (12410251158811590975928709501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (355059 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_30 : rowCell 2 30 ≤ (1750177405456855922387699631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (724424307050428006489661109 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12410251158811590975928709501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_30_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_30_1
  · norm_num [gridPoint]

theorem exp_2_31_0 : expNegUpper (11772164616043911905563 / 160235731231839744000 : ℝ) ≤ (12410219592103176417233137547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (355059 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_31_1 : expNegUpper (73509701601144243569 / 1001473320198998400 : ℝ) ≤ (2651994644795526566464019723 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1774377 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_31 : rowCell 2 31 ≤ (1871893523212470808079482127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12410219592103176417233137547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2651994644795526566464019723 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_31_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_31_1
  · norm_num [gridPoint]

theorem sum_2_0_2 : blockSum (rowCell 2) 0 2 ≤ (161232039883749038884485953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_0) (by simpa only [blockSum_one] using cell_2_1) (by norm_num)

theorem sum_2_2_2 : blockSum (rowCell 2) 2 2 ≤ (214706817395817543507507621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_2) (by simpa only [blockSum_one] using cell_2_3) (by norm_num)

theorem sum_2_0_4 : blockSum (rowCell 2) 0 4 ≤ (187969428639783291195996787 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_0_2 sum_2_2_2 (by norm_num)

theorem sum_2_4_2 : blockSum (rowCell 2) 4 2 ≤ (282247812707073415239778353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_4) (by simpa only [blockSum_one] using cell_2_5) (by norm_num)

theorem sum_2_6_2 : blockSum (rowCell 2) 6 2 ≤ (45803774206277801253762567 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_6) (by simpa only [blockSum_one] using cell_2_7) (by norm_num)

theorem sum_2_4_4 : blockSum (rowCell 2) 4 4 ≤ (648678006357295825269878889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_4_2 sum_2_6_2 (by norm_num)

theorem sum_2_0_8 : blockSum (rowCell 2) 0 8 ≤ (1024616863636862407661872463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_0_4 sum_2_4_4 (by norm_num)

theorem sum_2_8_2 : blockSum (rowCell 2) 8 2 ≤ (470008161380392900579394783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_8) (by simpa only [blockSum_one] using cell_2_9) (by norm_num)

theorem sum_2_10_2 : blockSum (rowCell 2) 10 2 ≤ (595858222534209552920239967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_10) (by simpa only [blockSum_one] using cell_2_11) (by norm_num)

theorem sum_2_8_4 : blockSum (rowCell 2) 8 4 ≤ (4263465535658409813998539 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_8_2 sum_2_10_2 (by norm_num)

theorem sum_2_12_2 : blockSum (rowCell 2) 12 2 ≤ (74690699864899360761201581 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_12) (by simpa only [blockSum_one] using cell_2_13) (by norm_num)

theorem sum_2_14_2 : blockSum (rowCell 2) 14 2 ≤ (463022376242256399981996541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_14) (by simpa only [blockSum_one] using cell_2_15) (by norm_num)

theorem sum_2_12_4 : blockSum (rowCell 2) 12 4 ≤ (418237937783376601894002223 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_12_2 sum_2_14_2 (by norm_num)

theorem sum_2_8_8 : blockSum (rowCell 2) 8 8 ≤ (1369409067524054430537821821 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_8_4 sum_2_12_4 (by norm_num)

theorem sum_2_0_16 : blockSum (rowCell 2) 0 16 ≤ (752686999736994253747503221 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_0_8 sum_2_8_8 (by norm_num)

theorem sum_2_16_2 : blockSum (rowCell 2) 16 2 ≤ (35500836772085412001114427 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_16) (by simpa only [blockSum_one] using cell_2_17) (by norm_num)

theorem sum_2_18_2 : blockSum (rowCell 2) 18 2 ≤ (689682860091320201569762723 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_18) (by simpa only [blockSum_one] using cell_2_19) (by norm_num)

theorem sum_2_16_4 : blockSum (rowCell 2) 16 4 ≤ (251539249688937358717518711 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_16_2 sum_2_18_2 (by norm_num)

theorem sum_2_20_2 : blockSum (rowCell 2) 20 2 ≤ (331643750420984422743031417 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_20) (by simpa only [blockSum_one] using cell_2_21) (by norm_num)

theorem sum_2_22_2 : blockSum (rowCell 2) 22 2 ≤ (987137059831279348113462203 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_22) (by simpa only [blockSum_one] using cell_2_23) (by norm_num)

theorem sum_2_20_4 : blockSum (rowCell 2) 20 4 ≤ (3632492871767480809942081491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_20_2 sum_2_22_2 (by norm_num)

theorem sum_2_16_8 : blockSum (rowCell 2) 16 8 ≤ (6147885368656854397117268601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_16_4 sum_2_20_4 (by norm_num)

theorem sum_2_24_2 : blockSum (rowCell 2) 24 2 ≤ (1164321043030077538572461527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_24) (by simpa only [blockSum_one] using cell_2_25) (by norm_num)

theorem sum_2_26_2 : blockSum (rowCell 2) 26 2 ≤ (2721755401918777783173930147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_26) (by simpa only [blockSum_one] using cell_2_27) (by norm_num)

theorem sum_2_24_4 : blockSum (rowCell 2) 24 4 ≤ (5050397487978932860318853201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_24_2 sum_2_26_2 (by norm_num)

theorem sum_2_28_2 : blockSum (rowCell 2) 28 2 ≤ (788321085508546776410076149 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_28) (by simpa only [blockSum_one] using cell_2_29) (by norm_num)

theorem sum_2_30_2 : blockSum (rowCell 2) 30 2 ≤ (1811035464334663365233590879 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_30) (by simpa only [blockSum_one] using cell_2_31) (by norm_num)

theorem sum_2_28_4 : blockSum (rowCell 2) 28 4 ≤ (3387677635351756918053743177 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_28_2 sum_2_30_2 (by norm_num)

theorem sum_2_24_8 : blockSum (rowCell 2) 24 8 ≤ (2365150551736489339285267911 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_24_4 sum_2_28_4 (by norm_num)

theorem sum_2_16_16 : blockSum (rowCell 2) 16 16 ≤ (4493409531834825273385902039 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_16_8 sum_2_24_8 (by norm_num)

theorem sum_2_0_32 : blockSum (rowCell 2) 0 32 ≤ (21737073126024272362281124261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_0_16 sum_2_16_16 (by norm_num)

#print axioms sum_2_0_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
