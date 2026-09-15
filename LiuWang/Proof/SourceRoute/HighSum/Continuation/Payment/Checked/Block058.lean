import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_320_0 : expNegUpper (3981403675730567441363 / 43572709073712392000 : ℝ) ≤ (25954354694244316389 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2041853 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_320_1 : expNegUpper (255107311451859793500111 / 2788653380717593088000 : ℝ) ≤ (186626102860741573583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (408711 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_320 : rowCell 3 320 ≤ (28749861993853293783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25954354694244316389 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (186626102860741573583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_320_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_320_1
  · norm_num [gridPoint]

theorem exp_3_321_0 : expNegUpper (256140814740261212628039 / 2799950908017562112000 : ℝ) ≤ (93313043977434632567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (408711 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_321_1 : expNegUpper (25643993859704636173051 / 279995090801756211200 : ℝ) ≤ (83858267575327317579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2045261 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_321 : rowCell 3 321 ≤ (25838982431555249179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (93313043977434632567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (83858267575327317579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_321_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_321_1
  · norm_num [gridPoint]

theorem exp_3_322_0 : expNegUpper (2860852672439896371859 / 31236347484703180800 : ℝ) ≤ (167716521862867179199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2045261 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_322_1 : expNegUpper (28641946150981893703229 / 312363474847031808000 : ℝ) ≤ (150699272461901885127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2046971 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_322 : rowCell 3 322 ≤ (23219165798852373831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (167716521862867179199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (150699272461901885127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_322_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_322_1
  · norm_num [gridPoint]

theorem exp_3_323_0 : expNegUpper (258817622577083345494109 / 2822614477534765568000 : ℝ) ≤ (150699260618218228699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2046971 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_323_1 : expNegUpper (64780012932392621256207 / 705653619383691392000 : ℝ) ≤ (135387515990426603529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1024343 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_323 : rowCell 3 323 ≤ (1303856548836921281 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (150699260618218228699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (135387515990426603529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_323_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_323_1
  · norm_num [gridPoint]

theorem exp_3_324_0 : expNegUpper (4162615534481246007 / 45343688316032000 : ℝ) ≤ (27077501087075987557 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1024343 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_324_1 : expNegUpper (16669923692901461347 / 181374753264128000 : ℝ) ≤ (60806315347560689029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (512601 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_324 : rowCell 3 324 ≤ (18740680825195960699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27077501087075987557 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (60806315347560689029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_324_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_324_1
  · norm_num [gridPoint]

theorem exp_3_325_0 : expNegUpper (29057143943990323336283 / 316152155586109952000 : ℝ) ≤ (30403155322452766511 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (512601 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_325_1 : expNegUpper (14545557959290013090237 / 158076077793054976000 : ℝ) ≤ (13652801069715547877 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1026063 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_325 : rowCell 3 325 ≤ (16832697767329413591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30403155322452766511 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13652801069715547877 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_325_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_325_1
  · norm_num [gridPoint]

theorem exp_3_326_0 : expNegUpper (131435053170963547995157 / 1428390559551867136000 : ℝ) ≤ (54611200089035169799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1026063 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_326_1 : expNegUpper (52635503683762767597213 / 571356223820746854400 : ℝ) ≤ (98079494787646619003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (513463 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_326 : rowCell 3 326 ≤ (15116640428696338883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (54611200089035169799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (98079494787646619003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_326_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_326_1
  · norm_num [gridPoint]

theorem exp_3_327_0 : expNegUpper (52846182687091816011573 / 573643135247646822400 : ℝ) ≤ (98079487322825389289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (513463 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_327_1 : expNegUpper (33067499143588098420167 / 358526959529779264000 : ℝ) ≤ (17611992402062341997 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1027791 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_327 : rowCell 3 327 ≤ (10604262406276459 / 781250000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (98079487322825389289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17611992402062341997 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_327_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_327_1
  · norm_num [gridPoint]

theorem exp_3_328_0 : expNegUpper (3688843427345104291087 / 39995459328867904000 : ℝ) ≤ (8805995536135558789 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1027791 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_328_1 : expNegUpper (29545275272136858942127 / 319963674630943232000 : ℝ) ≤ (39526009408714428027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (411463 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_328 : rowCell 3 328 ≤ (2437191059356252581 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8805995536135558789 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39526009408714428027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_328_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_328_1
  · norm_num [gridPoint]

theorem exp_3_329_0 : expNegUpper (344474266237975521833 / 3730520394096128000 : ℝ) ≤ (79052012895971272009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (411463 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_329_1 : expNegUpper (172438697621118267141 / 1865260197048064000 : ℝ) ≤ (35477420140480090063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2059053 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_329 : rowCell 3 329 ≤ (34183232829512477 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (79052012895971272009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35477420140480090063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_329_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_329_1
  · norm_num [gridPoint]

theorem exp_3_330_0 : expNegUpper (134171706062274144086931 / 1451328188738132224000 : ℝ) ≤ (70954835008112286573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2059053 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_330_1 : expNegUpper (268657514731548184858621 / 2902656377476264448000 : ℝ) ≤ (15919377287289939841 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1030397 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_330 : rowCell 3 330 ≤ (9817511494694981389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (70954835008112286573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15919377287289939841 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_330_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_330_1
  · norm_num [gridPoint]

theorem exp_3_331_0 : expNegUpper (29969367125726436883021 / 323798031981531648000 : ℝ) ≤ (1989922014203271029 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1030397 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_331_1 : expNegUpper (1500222709433416608769 / 16189901599076582400 : ℝ) ≤ (14284514365485718581 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (103127 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_331 : rowCell 3 331 ≤ (4404989660089382227 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1989922014203271029 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14284514365485718581 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_331_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_331_1
  · norm_num [gridPoint]

theorem exp_3_332_0 : expNegUpper (13555512117386930373481 / 146286551824853017600 : ℝ) ≤ (14284513320658852741 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (103127 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_332_1 : expNegUpper (271427710204472374957011 / 2925731036497060352000 : ℝ) ≤ (5126259925225548811 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2064289 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_332 : rowCell 3 332 ≤ (7904672974055506177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14284513320658852741 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5126259925225548811 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_332_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_332_1
  · norm_num [gridPoint]

theorem exp_3_333_0 : expNegUpper (272501236765488961470219 / 2937302623466091008000 : ℝ) ≤ (12815648883054116787 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2064289 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_333_1 : expNegUpper (136410196121629493861729 / 1468651311733045504000 : ℝ) ≤ (4598454584765115293 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1033021 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_333 : rowCell 3 333 ≤ (7091348919898530331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12815648883054116787 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4598454584765115293 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_333_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_333_1
  · norm_num [gridPoint]

theorem exp_3_334_0 : expNegUpper (608660660838061423729 / 6553104552757504000 : ℝ) ≤ (1149613563421161527 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1033021 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_334_1 : expNegUpper (1218747305807615442697 / 13106209105515008000 : ℝ) ≤ (41243896058922606413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2067799 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_334 : rowCell 3 334 ≤ (795097013962972661 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1149613563421161527 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41243896058922606413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_334_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_334_1
  · norm_num [gridPoint]

theorem exp_3_335_0 : expNegUpper (275298434174993291822177 / 2960514312321417728000 : ℝ) ≤ (4124389311271821617 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2067799 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_335_1 : expNegUpper (17226310930448405146011 / 185032144520088608000 : ℝ) ≤ (36986594246784797793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (51739 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_335 : rowCell 3 335 ≤ (356539838966152927 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4124389311271821617 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36986594246784797793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_335_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_335_1
  · norm_num [gridPoint]

theorem exp_3_336_0 : expNegUpper (17294041071964035101979 / 185759650887982112000 : ℝ) ≤ (36986591625369836713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (51739 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_336_1 : expNegUpper (11081155819079226305623 / 118886176568308551680 : ℝ) ≤ (33163949899145117707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (517831 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_336 : rowCell 3 336 ≤ (159857516057649419 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36986591625369836713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33163949899145117707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_336_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_336_1
  · norm_num [gridPoint]

theorem exp_3_337_0 : expNegUpper (1236071005772267097047 / 13261410463998955520 : ℝ) ≤ (6632789513403179263 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (517831 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_337_1 : expNegUpper (15468995309359480402727 / 165767630799986944000 : ℝ) ≤ (5946422587164002201 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2073093 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_337 : rowCell 3 337 ≤ (4586437240046152379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6632789513403179263 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5946422587164002201 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_337_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_337_1
  · norm_num [gridPoint]

theorem exp_3_338_0 : expNegUpper (139766200804669272081487 / 1497751566448785664000 : ℝ) ≤ (14866055430659323111 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2073093 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_338_1 : expNegUpper (279860045153983097890773 / 2995503132897571328000 : ℝ) ≤ (26651599489612500193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (414973 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_338 : rowCell 3 338 ≤ (1027887704007416903 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14866055430659323111 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26651599489612500193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_338_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_338_1
  · norm_num [gridPoint]

theorem exp_3_339_0 : expNegUpper (11238157723019942013717 / 120288469988045312000 : ℝ) ≤ (26651597644514426559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (414973 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_339_1 : expNegUpper (2812832942258566562947 / 30072117497011328000 : ℝ) ≤ (23886863396988055151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2076641 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_339 : rowCell 3 339 ≤ (1842654992397476471 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26651597644514426559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23886863396988055151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_339_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_339_1
  · norm_num [gridPoint]

theorem exp_3_340_0 : expNegUpper (7843905852488298947347 / 83859533466956928000 : ℝ) ≤ (23886861756133304943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2076641 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_340_1 : expNegUpper (31412408086269996576659 / 335438133867827712000 : ℝ) ≤ (856236362893322573 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2078421 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_340 : rowCell 3 340 ≤ (51606086586493107 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23886861756133304943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (856236362893322573 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_340_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_340_1
  · norm_num [gridPoint]

theorem exp_3_341_0 : expNegUpper (283812414443917826176739 / 3030697498225521152000 : ℝ) ≤ (21405907613296726673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2078421 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_341_1 : expNegUpper (28414519079804168330553 / 303069749822552115200 : ℝ) ≤ (2397492730094779773 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (416041 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_341 : rowCell 3 341 ≤ (591911321207761383 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21405907613296726673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2397492730094779773 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_341_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_341_1
  · norm_num [gridPoint]

theorem exp_3_342_0 : expNegUpper (28524936433085438928873 / 304247462994634803200 : ℝ) ≤ (19179940543555982409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (416041 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_342_1 : expNegUpper (285583858283030445370561 / 3042474629946348032000 : ℝ) ≤ (17183052169104934807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (260249 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_342 : rowCell 3 342 ≤ (530324419696699873 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19179940543555982409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17183052169104934807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_342_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_342_1
  · norm_num [gridPoint]

theorem exp_3_343_0 : expNegUpper (31854607815858566463281 / 339363844441436672000 : ℝ) ≤ (687322040637196393 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (260249 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_343_1 : expNegUpper (3986495628107429196029 / 42420480555179584000 : ℝ) ≤ (15391930566416830893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2083783 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_343 : rowCell 3 343 ≤ (2375396923569739723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (687322040637196393 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15391930566416830893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_343_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_343_1
  · norm_num [gridPoint]

theorem exp_3_344_0 : expNegUpper (1440693712359372997741 / 15330487041526336000 : ℝ) ≤ (3847982385351158899 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2083783 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_344_1 : expNegUpper (11539067264499748010607 / 122643896332210688000 : ℝ) ≤ (2757122045314507323 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1042789 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_344 : rowCell 3 344 ≤ (212765241407678069 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3847982385351158899 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2757122045314507323 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_344_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_344_1
  · norm_num [gridPoint]

theorem exp_3_345_0 : expNegUpper (289591190710635540153807 / 3077943054943359488000 : ℝ) ≤ (3446402328897824977 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1042789 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_345_1 : expNegUpper (144965428720822743276443 / 1538971527471679744000 : ℝ) ≤ (61726173798537493 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2087377 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_345 : rowCell 3 345 ≤ (1905484626901012289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3446402328897824977 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (61726173798537493 / 5000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_345_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_345_1
  · norm_num [gridPoint]

theorem exp_3_346_0 : expNegUpper (16169379169519364817523 / 171656196660400384000 : ℝ) ≤ (6172616975085208173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2087377 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_346_1 : expNegUpper (6475338282300642393473 / 68662478664160153600 : ℝ) ≤ (88430788863423421 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (104459 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_346 : rowCell 3 346 ≤ (853141061374883517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6172616975085208173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (88430788863423421 / 8000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_346_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_346_1
  · norm_num [gridPoint]

theorem exp_3_347_0 : expNegUpper (58502331097270465192417 / 620340572627361894400 : ℝ) ≤ (5526923944312940271 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (104459 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_347_1 : expNegUpper (73213696847620652613609 / 775425715784202368000 : ℝ) ≤ (4948103983433827217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1045493 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_347 : rowCell 3 347 ≤ (1527696895298396241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5526923944312940271 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4948103983433827217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_347_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_347_1
  · norm_num [gridPoint]

theorem exp_3_348_0 : expNegUpper (73494923001996366155721 / 778404256173041792000 : ℝ) ≤ (15833931724511647 / 1600000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1045493 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_348_1 : expNegUpper (294324561494845241526403 / 3113617024692167168000 : ℝ) ≤ (177172204798005581 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (523199 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_348 : rowCell 3 348 ≤ (1367618147069555159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15833931724511647 / 1600000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (177172204798005581 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_348_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_348_1
  · norm_num [gridPoint]

theorem exp_3_349_0 : expNegUpper (52524967930415400787 / 555654048809472000 : ℝ) ≤ (8858609672220588769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (523199 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_349_1 : expNegUpper (26293293778573817569 / 277827024404736000 : ℝ) ≤ (495546264884789329 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (209461 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_349 : rowCell 3 349 ≤ (306037159462347961 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8858609672220588769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (495546264884789329 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_349_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_349_1
  · norm_num [gridPoint]

theorem exp_3_350_0 : expNegUpper (148465711640247233551561 / 1568756931360073984000 : ℝ) ≤ (1982184933483743877 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (209461 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_350_1 : expNegUpper (297279777925151875558041 / 3137513862720147968000 : ℝ) ≤ (1773882877153092117 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (524107 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_350 : rowCell 3 350 ≤ (1095583357375246799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1982184933483743877 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1773882877153092117 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_350_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_350_1
  · norm_num [gridPoint]

theorem exp_3_351_0 : expNegUpper (298415138016047624380689 / 3149496539192771072000 : ℝ) ≤ (221735345650256947 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (524107 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_351_1 : expNegUpper (1867282751473582324849 / 19684353369954819200 : ℝ) ≤ (3174520662977610977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (8393 / 4000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_351 : rowCell 3 351 ≤ (980390297550794089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (221735345650256947 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3174520662977610977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_351_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_351_1
  · norm_num [gridPoint]

theorem sum_3_320_2 : blockSum (rowCell 3) 320 2 ≤ (27294422212704271481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_320) (by simpa only [blockSum_one] using cell_3_321) (by norm_num)

theorem sum_3_322_2 : blockSum (rowCell 3) 322 2 ≤ (44080870580243114327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_322) (by simpa only [blockSum_one] using cell_3_323) (by norm_num)

theorem sum_3_320_4 : blockSum (rowCell 3) 320 4 ≤ (98669715005651657289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_320_2 sum_3_322_2 (by norm_num)

theorem sum_3_324_2 : blockSum (rowCell 3) 324 2 ≤ (3557337859252537429 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_324) (by simpa only [blockSum_one] using cell_3_325) (by norm_num)

theorem sum_3_326_2 : blockSum (rowCell 3) 326 2 ≤ (28690096308730206403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_326) (by simpa only [blockSum_one] using cell_3_327) (by norm_num)

theorem sum_3_324_4 : blockSum (rowCell 3) 324 4 ≤ (64263474901255580693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_324_2 sum_3_326_2 (by norm_num)

theorem sum_3_320_8 : blockSum (rowCell 3) 320 8 ≤ (81466594953453618991 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_320_4 sum_3_324_4 (by norm_num)

theorem sum_3_328_2 : blockSum (rowCell 3) 328 2 ≤ (4624917960445051109 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_328) (by simpa only [blockSum_one] using cell_3_329) (by norm_num)

theorem sum_3_330_2 : blockSum (rowCell 3) 330 2 ≤ (18627490814873745843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_330) (by simpa only [blockSum_one] using cell_3_331) (by norm_num)

theorem sum_3_328_4 : blockSum (rowCell 3) 328 4 ≤ (10438020154274750347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_328_2 sum_3_330_2 (by norm_num)

theorem sum_3_332_2 : blockSum (rowCell 3) 332 2 ≤ (3749005473488509127 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_332) (by simpa only [blockSum_one] using cell_3_333) (by norm_num)

theorem sum_3_334_2 : blockSum (rowCell 3) 334 2 ≤ (301635338379055703 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_334) (by simpa only [blockSum_one] using cell_3_335) (by norm_num)

theorem sum_3_332_4 : blockSum (rowCell 3) 332 4 ≤ (6765358857279066157 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_332_2 sum_3_334_2 (by norm_num)

theorem sum_3_328_8 : blockSum (rowCell 3) 328 8 ≤ (2150422376444227063 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_328_4 sum_3_332_4 (by norm_num)

theorem sum_3_320_16 : blockSum (rowCell 3) 320 16 ≤ (115873352976561251999 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_320_8 sum_3_328_8 (by norm_num)

theorem sum_3_336_2 : blockSum (rowCell 3) 336 2 ≤ (9701877753890933787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_336) (by simpa only [blockSum_one] using cell_3_337) (by norm_num)

theorem sum_3_338_2 : blockSum (rowCell 3) 338 2 ≤ (3898430400412310277 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_338) (by simpa only [blockSum_one] using cell_3_339) (by norm_num)

theorem sum_3_336_4 : blockSum (rowCell 3) 336 4 ≤ (17498738554715554341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_336_2 sum_3_338_2 (by norm_num)

theorem sum_3_340_2 : blockSum (rowCell 3) 340 2 ≤ (6262346147574365763 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_340) (by simpa only [blockSum_one] using cell_3_341) (by norm_num)

theorem sum_3_342_2 : blockSum (rowCell 3) 342 2 ≤ (314188688878327443 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_342) (by simpa only [blockSum_one] using cell_3_343) (by norm_num)

theorem sum_3_340_4 : blockSum (rowCell 3) 340 4 ≤ (11289365169627604851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_340_2 sum_3_342_2 (by norm_num)

theorem sum_3_336_8 : blockSum (rowCell 3) 336 8 ≤ (3598512965542894899 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_336_4 sum_3_340_4 (by norm_num)

theorem sum_3_344_2 : blockSum (rowCell 3) 344 2 ≤ (4033137040977792979 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_344) (by simpa only [blockSum_one] using cell_3_345) (by norm_num)

theorem sum_3_346_2 : blockSum (rowCell 3) 346 2 ≤ (129359160721926531 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_346) (by simpa only [blockSum_one] using cell_3_347) (by norm_num)

theorem sum_3_344_4 : blockSum (rowCell 3) 344 4 ≤ (3633558029512978127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_344_2 sum_3_346_2 (by norm_num)

theorem sum_3_348_2 : blockSum (rowCell 3) 348 2 ≤ (2591766784918947003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_348) (by simpa only [blockSum_one] using cell_3_349) (by norm_num)

theorem sum_3_350_2 : blockSum (rowCell 3) 350 2 ≤ (259496706865755111 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_350) (by simpa only [blockSum_one] using cell_3_351) (by norm_num)

theorem sum_3_348_4 : blockSum (rowCell 3) 348 4 ≤ (4667740439844987891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_348_2 sum_3_350_2 (by norm_num)

theorem sum_3_344_8 : blockSum (rowCell 3) 344 8 ≤ (2386971299774188829 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_344_4 sum_3_348_4 (by norm_num)

theorem sum_3_336_16 : blockSum (rowCell 3) 336 16 ≤ (40722960223214103337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_336_8 sum_3_344_8 (by norm_num)

theorem sum_3_320_32 : blockSum (rowCell 3) 320 32 ≤ (54493933235267321467 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_320_16 sum_3_336_16 (by norm_num)

#print axioms sum_3_320_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
