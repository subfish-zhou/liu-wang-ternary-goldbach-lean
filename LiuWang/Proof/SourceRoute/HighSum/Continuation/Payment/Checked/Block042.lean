import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_320_0 : expNegUpper (560731578170314205909 / 6224672724816056000 : ℝ) ≤ (755572277343333802843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2021351 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_320_1 : expNegUpper (35930357851389195642873 / 398379054388227584000 : ℝ) ≤ (84668947750396698959 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1011539 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_320 : rowCell 2 320 ≤ (26122523804019300209 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (755572277343333802843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (84668947750396698959 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_320_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_320_1
  · norm_num [gridPoint]

theorem exp_2_321_0 : expNegUpper (252531444779485532628039 / 2799950908017562112000 : ℝ) ≤ (677351531509619953567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1011539 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_321_1 : expNegUpper (25283785037059080973051 / 279995090801756211200 : ℝ) ≤ (607139085144232253229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (253101 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_321 : rowCell 2 321 ≤ (18733241960187460573 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (677351531509619953567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (607139085144232253229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_321_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_321_1
  · norm_num [gridPoint]

theorem exp_2_322_0 : expNegUpper (8462002960816495515577 / 93709042454109542400 : ℝ) ≤ (607139040248841002253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (253101 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_322_1 : expNegUpper (84722715132687121109687 / 937090424541095424000 : ℝ) ≤ (544124851559736369133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1013271 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_322 : rowCell 2 322 ≤ (83951197329334258691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (607139040248841002253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (544124851559736369133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_322_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_322_1
  · norm_num [gridPoint]

theorem exp_2_323_0 : expNegUpper (255193689147667409494109 / 2822614477534765568000 : ℝ) ≤ (136031202911761965871 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1013271 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_323_1 : expNegUpper (63875850008618669256207 / 705653619383691392000 : ℝ) ≤ (243789865091354129559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (50707 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_323 : rowCell 2 323 ≤ (9404102764034389579 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (136031202911761965871 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (243789865091354129559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_323_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_323_1
  · norm_num [gridPoint]

theorem exp_2_324_0 : expNegUpper (4104516091861468983 / 45343688316032000 : ℝ) ≤ (243789847352156898793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (50707 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_324_1 : expNegUpper (16437991953418841443 / 181374753264128000 : ℝ) ≤ (54605932594264063087 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1015011 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_324 : rowCell 2 324 ≤ (67410058716050928143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (243789847352156898793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (54605932594264063087 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_324_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_324_1
  · norm_num [gridPoint]

theorem exp_2_325_0 : expNegUpper (85958599532618906008849 / 948456466758329856000 : ℝ) ≤ (436847429221421202699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1015011 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_325_1 : expNegUpper (43031471350580695270711 / 474228233379164928000 : ℝ) ≤ (78267498555347935613 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2031767 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_325 : rowCell 2 325 ≤ (15097997146124187287 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (436847429221421202699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (78267498555347935613 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_325_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_325_1
  · norm_num [gridPoint]

theorem exp_2_326_0 : expNegUpper (129612163854775387995157 / 1428390559551867136000 : ℝ) ≤ (78267492950903453903 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2031767 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_326_1 : expNegUpper (51907804304151529197213 / 571356223820746854400 : ℝ) ≤ (350518500508175991383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2033517 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_326 : rowCell 2 326 ≤ (27048401749087191643 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (78267492950903453903 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (350518500508175991383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_326_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_326_1
  · norm_num [gridPoint]

theorem exp_2_327_0 : expNegUpper (7445081516250360915939 / 81949019321092403200 : ℝ) ≤ (350518475608774141719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2033517 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_327_1 : expNegUpper (4658825259220151202881 / 51218137075682752000 : ℝ) ≤ (31391252775317004783 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (203527 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_327 : rowCell 2 327 ≤ (48450905714882553299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (350518475608774141719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31391252775317004783 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_327_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_327_1
  · norm_num [gridPoint]

theorem exp_2_328_0 : expNegUpper (10914016027826288873261 / 119986377986603712000 : ℝ) ≤ (313912505631373239259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (203527 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_328_1 : expNegUpper (87418139027511760826381 / 959891023892829696000 : ℝ) ≤ (281089702389130121889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2037027 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_328 : rowCell 2 328 ≤ (10847023895287843379 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (313912505631373239259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (281089702389130121889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_328_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_328_1
  · norm_num [gridPoint]

theorem exp_2_329_0 : expNegUpper (339741848385928161833 / 3730520394096128000 : ℝ) ≤ (281089682737554777871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2037027 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_329_1 : expNegUpper (170077186588204347141 / 1865260197048064000 : ℝ) ≤ (125831733085155198123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2038787 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_329 : rowCell 2 329 ≤ (38848838263768750407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (281089682737554777871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (125831733085155198123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_329_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_329_1
  · norm_num [gridPoint]

theorem exp_2_330_0 : expNegUpper (132334253277445728086931 / 1451328188738132224000 : ℝ) ≤ (12583172435764886819 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2038787 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_330_1 : expNegUpper (264989890896211480858621 / 2902656377476264448000 : ℝ) ≤ (28160783807015266847 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2040551 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_330 : rowCell 2 330 ≤ (17389801015746627539 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12583172435764886819 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28160783807015266847 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_330_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_330_1
  · norm_num [gridPoint]

theorem exp_2_331_0 : expNegUpper (88680705609186990649063 / 971394095944594944000 : ℝ) ≤ (225286254954072372619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2040551 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_331_1 : expNegUpper (4439419702139302626307 / 48569704797229747200 : ℝ) ≤ (6301427910698297447 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2042319 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_331 : rowCell 2 331 ≤ (15566130613431455241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (225286254954072372619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6301427910698297447 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_331_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_331_1
  · norm_num [gridPoint]

theorem exp_2_332_0 : expNegUpper (13371038665472075973481 / 146286551824853017600 : ℝ) ≤ (201645679376446504459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2042319 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_332_1 : expNegUpper (267745522900495414957011 / 2925731036497060352000 : ℝ) ≤ (18046093628233603063 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2044091 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_332 : rowCell 2 332 ≤ (27863557712750928397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (201645679376446504459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18046093628233603063 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_332_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_332_1
  · norm_num [gridPoint]

theorem exp_2_333_0 : expNegUpper (268804485992871745470219 / 2937302623466091008000 : ℝ) ≤ (180460924059644365829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2044091 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_333_1 : expNegUpper (134565461602480949861729 / 1468651311733045504000 : ℝ) ≤ (161479667706558606313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2045867 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_333 : rowCell 2 333 ≤ (24934615163841935677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (180460924059644365829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (161479667706558606313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_333_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_333_1
  · norm_num [gridPoint]

theorem exp_2_334_0 : expNegUpper (257326918923990758741 / 2808473379753216000 : ℝ) ≤ (40369914213848915499 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2045867 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_334_1 : expNegUpper (515278843874469064013 / 5616946759506432000 : ℝ) ≤ (144475173417607605333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1023823 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_334 : rowCell 2 334 ≤ (2788812638100027707 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (40369914213848915499 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (144475173417607605333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_334_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_334_1
  · norm_num [gridPoint]

theorem exp_2_335_0 : expNegUpper (271587119933735819822177 / 2960514312321417728000 : ℝ) ≤ (144475163785236844281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1023823 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_335_1 : expNegUpper (16994808898764821146011 / 185032144520088608000 : ℝ) ≤ (129243790685939050093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2049429 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_335 : rowCell 2 335 ≤ (3991966415882260783 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (144475163785236844281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (129243790685939050093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_335_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_335_1
  · norm_num [gridPoint]

theorem exp_2_336_0 : expNegUpper (17061628823490435101979 / 185759650887982112000 : ℝ) ≤ (16155472767061822979 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2049429 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_336_1 : expNegUpper (10932703249428927425623 / 118886176568308551680 : ℝ) ≤ (28900648656938912189 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (128201 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_336 : rowCell 2 336 ≤ (4463604443203937773 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16155472767061822979 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28900648656938912189 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_336_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_336_1
  · norm_num [gridPoint]

theorem exp_2_337_0 : expNegUpper (3658534647851498251141 / 39784231391996866560 : ℝ) ≤ (7225161690024696481 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (128201 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_337_1 : expNegUpper (45787219932148841208181 / 497302892399960832000 : ℝ) ≤ (3230853551163190729 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1026503 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_337 : rowCell 2 337 ≤ (159689403061507397 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7225161690024696481 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3230853551163190729 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_337_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_337_1
  · norm_num [gridPoint]

theorem exp_2_338_0 : expNegUpper (137899621082560344081487 / 1497751566448785664000 : ℝ) ≤ (10338730690447999191 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1026503 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_338_1 : expNegUpper (276134167444085369890773 / 2995503132897571328000 : ℝ) ≤ (92450451394512566591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (5137 / 2500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_338 : rowCell 2 338 ≤ (7140332641574254559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10338730690447999191 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (92450451394512566591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_338_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_338_1
  · norm_num [gridPoint]

theorem exp_2_339_0 : expNegUpper (11088540075878422653717 / 120288469988045312000 : ℝ) ≤ (46225222710416033443 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (5137 / 2500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_339_1 : expNegUpper (2775501347816388002947 / 30072117497011328000 : ℝ) ≤ (41329797650525535777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1028299 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_339 : rowCell 2 339 ≤ (6384590747433464761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (46225222710416033443 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41329797650525535777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_339_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_339_1
  · norm_num [gridPoint]

theorem exp_2_340_0 : expNegUpper (23219407314726720842041 / 251578600400870784000 : ℝ) ≤ (82659590001475799599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1028299 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_340_1 : expNegUpper (92990410532630661729977 / 1006314401603483136000 : ℝ) ≤ (73895893123708832909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2573 / 1250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_340 : rowCell 2 340 ≤ (5708083242402666843 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (82659590001475799599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (73895893123708832909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_340_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_340_1
  · norm_num [gridPoint]

theorem exp_2_341_0 : expNegUpper (40008201399534226596677 / 432956785460788736000 : ℝ) ≤ (36947944211358416933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2573 / 1250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_341_1 : expNegUpper (4005678112645479590079 / 43295678546078873600 : ℝ) ≤ (33026340689453213847 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (412041 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_341 : rowCell 2 341 ≤ (10205175444977549379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36947944211358416933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33026340689453213847 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_341_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_341_1
  · norm_num [gridPoint]

theorem exp_2_342_0 : expNegUpper (28148707794935602128873 / 304247462994634803200 : ℝ) ≤ (8256584651171409933 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (412041 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_342_1 : expNegUpper (281828853635852205370561 / 3042474629946348032000 : ℝ) ≤ (59034250572149943887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1031007 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_342 : rowCell 2 342 ≤ (4560725578307603159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8256584651171409933 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (59034250572149943887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_342_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_342_1
  · norm_num [gridPoint]

theorem exp_2_343_0 : expNegUpper (94307300742302867389843 / 1018091533324310016000 : ℝ) ≤ (7379280859301902787 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1031007 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_343_1 : expNegUpper (11802724951759855588087 / 127261441665538752000 : ℝ) ≤ (52754733843642430877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1031913 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_343 : rowCell 2 343 ≤ (163035058187462559 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7379280859301902787 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (52754733843642430877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_343_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_343_1
  · norm_num [gridPoint]

theorem exp_2_344_0 : expNegUpper (1421809463108679877741 / 15330487041526336000 : ℝ) ≤ (52754730564697288787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1031913 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_344_1 : expNegUpper (11388284539867008170607 / 122643896332210688000 : ℝ) ≤ (23568553435017800339 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1032821 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_344 : rowCell 2 344 ≤ (227631329134794299 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (52754730564697288787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23568553435017800339 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_344_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_344_1
  · norm_num [gridPoint]

theorem exp_2_345_0 : expNegUpper (285807059126176788153807 / 3077943054943359488000 : ℝ) ≤ (11784275990695130593 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1032821 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_345_1 : expNegUpper (143077003795753431276443 / 1538971527471679744000 : ℝ) ≤ (8422457609733028369 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1033731 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_345 : rowCell 2 345 ≤ (3254072925237626559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11784275990695130593 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8422457609733028369 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_345_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_345_1
  · norm_num [gridPoint]

theorem exp_2_346_0 : expNegUpper (47876235288761614452569 / 514968589981201152000 : ℝ) ≤ (42112285471258104777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1033731 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_346_1 : expNegUpper (19173739407938010380419 / 205987435992480460800 : ℝ) ≤ (37618329055160338229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1034643 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_346 : rowCell 2 346 ≤ (1453507011060105361 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42112285471258104777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37618329055160338229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_346_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_346_1
  · norm_num [gridPoint]

theorem exp_2_347_0 : expNegUpper (57742592086650663592417 / 620340572627361894400 : ℝ) ≤ (3761832677043466111 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1034643 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_347_1 : expNegUpper (72265843517925932613609 / 775425715784202368000 : ℝ) ≤ (33599686828518240329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2071113 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_347 : rowCell 2 347 ≤ (5193281536569738383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3761832677043466111 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33599686828518240329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_347_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_347_1
  · norm_num [gridPoint]

theorem exp_2_348_0 : expNegUpper (10363346972163083165103 / 111200608024720256000 : ℝ) ≤ (33599684803464332551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2071113 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_348_1 : expNegUpper (41503695205963747646629 / 444802432098881024000 : ℝ) ≤ (30006568909027154297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (129559 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_348 : rowCell 2 348 ≤ (2319112583479224519 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33599684803464332551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (30006568909027154297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_348_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_348_1
  · norm_num [gridPoint]

theorem exp_2_349_0 : expNegUpper (155541165912985261561 / 1666962146428416000 : ℝ) ≤ (15003283557165609177 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (129559 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_349_1 : expNegUpper (77864954192409683107 / 833481073214208000 : ℝ) ≤ (26794344842398493877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1037389 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_349 : rowCell 2 349 ≤ (4141973531954066741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15003283557165609177 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26794344842398493877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_349_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_349_1
  · norm_num [gridPoint]

theorem exp_2_350_0 : expNegUpper (146555441512217537551561 / 1568756931360073984000 : ℝ) ≤ (13397171626015990129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1037389 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_350_1 : expNegUpper (293466519403412611558041 / 3137513862720147968000 : ℝ) ≤ (11961508537961297561 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (259577 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_350 : rowCell 2 350 ≤ (924588870373216821 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13397171626015990129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11961508537961297561 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_350_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_350_1
  · norm_num [gridPoint]

theorem exp_2_351_0 : expNegUpper (294587316025668104380689 / 3149496539192771072000 : ℝ) ≤ (23923015666776877343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (259577 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_351_1 : expNegUpper (1843404374873211124849 / 19684353369954819200 : ℝ) ≤ (533918635412309011 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1039229 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_351 : rowCell 2 351 ≤ (3301840859227341069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23923015666776877343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (533918635412309011 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_351_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_351_1
  · norm_num [gridPoint]

theorem sum_2_320_2 : blockSum (rowCell 2) 320 2 ≤ (198156305017014503701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_320) (by simpa only [blockSum_one] using cell_2_321) (by norm_num)

theorem sum_2_322_2 : blockSum (rowCell 2) 322 2 ≤ (159184019441609375323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_322) (by simpa only [blockSum_one] using cell_2_323) (by norm_num)

theorem sum_2_320_4 : blockSum (rowCell 2) 320 4 ≤ (22333770278663992439 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_320_2 sum_2_322_2 (by norm_num)

theorem sum_2_324_2 : blockSum (rowCell 2) 324 2 ≤ (127802047300547677291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_324) (by simpa only [blockSum_one] using cell_2_325) (by norm_num)

theorem sum_2_326_2 : blockSum (rowCell 2) 326 2 ≤ (20509541842611387317 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_326) (by simpa only [blockSum_one] using cell_2_327) (by norm_num)

theorem sum_2_324_4 : blockSum (rowCell 2) 324 4 ≤ (57587439128401153469 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_324_2 sum_2_326_2 (by norm_num)

theorem sum_2_320_8 : blockSum (rowCell 2) 320 8 ≤ (5876900809722284929 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_320_4 sum_2_324_4 (by norm_num)

theorem sum_2_328_2 : blockSum (rowCell 2) 328 2 ≤ (82236933844920123923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_328) (by simpa only [blockSum_one] using cell_2_329) (by norm_num)

theorem sum_2_330_2 : blockSum (rowCell 2) 330 2 ≤ (1647796581458904139 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_330) (by simpa only [blockSum_one] using cell_2_331) (by norm_num)

theorem sum_2_328_4 : blockSum (rowCell 2) 328 4 ≤ (148148797103276289483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_328_2 sum_2_330_2 (by norm_num)

theorem sum_2_332_2 : blockSum (rowCell 2) 332 2 ≤ (26399086438296432037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_332) (by simpa only [blockSum_one] using cell_2_333) (by norm_num)

theorem sum_2_334_2 : blockSum (rowCell 2) 334 2 ≤ (42270333184211525571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_334) (by simpa only [blockSum_one] using cell_2_335) (by norm_num)

theorem sum_2_332_4 : blockSum (rowCell 2) 332 4 ≤ (19013701212160877929 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_332_2 sum_2_334_2 (by norm_num)

theorem sum_2_328_8 : blockSum (rowCell 2) 328 8 ≤ (30402162895510084891 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_328_4 sum_2_332_4 (by norm_num)

theorem sum_2_320_16 : blockSum (rowCell 2) 320 16 ≤ (207726846034077293007 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_320_8 sum_2_328_8 (by norm_num)

theorem sum_2_336_2 : blockSum (rowCell 2) 336 2 ≤ (4227919759870811349 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_336) (by simpa only [blockSum_one] using cell_2_337) (by norm_num)

theorem sum_2_338_2 : blockSum (rowCell 2) 338 2 ≤ (338123084725192983 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_338) (by simpa only [blockSum_one] using cell_2_339) (by norm_num)

theorem sum_2_336_4 : blockSum (rowCell 2) 336 4 ≤ (7609150607122741179 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_336_2 sum_2_338_2 (by norm_num)

theorem sum_2_340_2 : blockSum (rowCell 2) 340 2 ≤ (4324268385956576613 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_340) (by simpa only [blockSum_one] using cell_2_341) (by norm_num)

theorem sum_2_342_2 : blockSum (rowCell 2) 342 2 ≤ (4318301016497083567 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_342) (by simpa only [blockSum_one] using cell_2_343) (by norm_num)

theorem sum_2_340_4 : blockSum (rowCell 2) 340 4 ≤ (38894545995771217333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_340_2 sum_2_342_2 (by norm_num)

theorem sum_2_336_8 : blockSum (rowCell 2) 336 8 ≤ (19953550170550629353 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_336_4 sum_2_340_4 (by norm_num)

theorem sum_2_344_2 : blockSum (rowCell 2) 344 2 ≤ (6896174191394335343 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_344) (by simpa only [blockSum_one] using cell_2_345) (by norm_num)

theorem sum_2_346_2 : blockSum (rowCell 2) 346 2 ≤ (11007309580810159827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_346) (by simpa only [blockSum_one] using cell_2_347) (by norm_num)

theorem sum_2_344_4 : blockSum (rowCell 2) 344 4 ≤ (24799657963598830513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_344_2 sum_2_346_2 (by norm_num)

theorem sum_2_348_2 : blockSum (rowCell 2) 348 2 ≤ (8780198698912515779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_348) (by simpa only [blockSum_one] using cell_2_349) (by norm_num)

theorem sum_2_350_2 : blockSum (rowCell 2) 350 2 ≤ (7000196340720208353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_350) (by simpa only [blockSum_one] using cell_2_351) (by norm_num)

theorem sum_2_348_4 : blockSum (rowCell 2) 348 4 ≤ (3945098759908181033 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_348_2 sum_2_350_2 (by norm_num)

theorem sum_2_344_8 : blockSum (rowCell 2) 344 8 ≤ (8116010600646310929 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_344_4 sum_2_348_4 (by norm_num)

theorem sum_2_336_16 : blockSum (rowCell 2) 336 16 ≤ (14034780385598470141 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_336_8 sum_2_344_8 (by norm_num)

theorem sum_2_320_32 : blockSum (rowCell 2) 320 32 ≤ (485627593996146936719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_320_16 sum_2_336_16 (by norm_num)

#print axioms sum_2_320_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
