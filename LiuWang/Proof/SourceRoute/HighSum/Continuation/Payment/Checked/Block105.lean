import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_288_0 : expNegUpper (6799309275698453731607 / 76224722892415504000 : ℝ) ≤ (455975693825479167583 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1003741 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_288_1 : expNegUpper (217818338713308881792623 / 2439191132557296128000 : ℝ) ≤ (826344907003089939107 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2009029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_288 : rowCell 6 288 ≤ (253516255113500856813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (455975693825479167583 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (826344907003089939107 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_288_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_288_1
  · norm_num [gridPoint]

theorem exp_6_289_0 : expNegUpper (8750477569448330642687 / 97990313362924032000 : ℝ) ≤ (413172407984566659161 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2009029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_289_1 : expNegUpper (4380078443878054703759 / 48995156681462016000 : ℝ) ≤ (14972434582966732481 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (100529 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_289 : rowCell 6 289 ≤ (4593919019158851487 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (413172407984566659161 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14972434582966732481 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_289_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_289_1
  · norm_num [gridPoint]

theorem exp_6_290_0 : expNegUpper (109975304090526940925671 / 1230173686947330304000 : ℝ) ≤ (187155411846471659437 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (100529 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_290_1 : expNegUpper (220194135536264006621381 / 2460347373894660608000 : ℝ) ≤ (1356143121706932321063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (402427 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_290 : rowCell 6 290 ≤ (208071501078985767189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (187155411846471659437 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1356143121706932321063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_290_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_290_1
  · norm_num [gridPoint]

theorem exp_6_291_0 : expNegUpper (221143913649226013492989 / 2470959752021975552000 : ℝ) ≤ (339035743715879210031 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (402427 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_291_1 : expNegUpper (11069449436636567141099 / 123547987601098777600 : ℝ) ≤ (614046450802652220019 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (402739 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_291 : rowCell 6 291 ≤ (188444801886526712707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (339035743715879210031 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (614046450802652220019 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_291_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_291_1
  · norm_num [gridPoint]

theorem exp_6_292_0 : expNegUpper (11117093281653165386059 / 124079748422752281600 : ℝ) ≤ (307023192441439352921 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (402739 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_292_1 : expNegUpper (222588491775643390518811 / 2481594968455045632000 : ℝ) ≤ (222382223629004119679 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2015259 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_292 : rowCell 6 292 ≤ (34127037170739395467 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (307023192441439352921 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (222382223629004119679 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_292_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_292_1
  · norm_num [gridPoint]

theorem exp_6_293_0 : expNegUpper (223544474124904411264979 / 2492253023193870848000 : ℝ) ≤ (69494437487361968851 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2015259 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_293_1 : expNegUpper (111896327328669398220469 / 1246126511596935424000 : ℝ) ≤ (1006520530155521861689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2016827 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_293 : rowCell 6 293 ≤ (154477930442523302883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (69494437487361968851 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1006520530155521861689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_293_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_293_1
  · norm_num [gridPoint]

theorem exp_6_294_0 : expNegUpper (4495034982341759417069 / 50058678324769024000 : ℝ) ≤ (503260211969487799329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2016827 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_294_1 : expNegUpper (9000059494806248292697 / 100117356649538048000 : ℝ) ≤ (910939361107949146079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2523 / 1250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_294 : rowCell 6 294 ≤ (139822890243397380483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (503260211969487799329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (910939361107949146079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_294_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_294_1
  · norm_num [gridPoint]

theorem exp_6_295_0 : expNegUpper (225963700601952633215657 / 2513637647588786688000 : ℝ) ≤ (910939265795755406753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2523 / 1250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_295_1 : expNegUpper (28276874988304283734667 / 314204705948598336000 : ℝ) ≤ (412136535409638121889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2019977 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_295 : rowCell 6 295 ≤ (5061329702632071421 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (910939265795755406753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (412136535409638121889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_295_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_295_1
  · norm_num [gridPoint]

theorem exp_6_296_0 : expNegUpper (1494607490604191086057 / 16607659323979456000 : ℝ) ≤ (824272985307194918457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2019977 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_296_1 : expNegUpper (2394033707984332956313 / 26572254918367129600 : ℝ) ≤ (745706813405020531707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2021559 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_296 : rowCell 6 296 ≤ (114484337450820156133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (824272985307194918457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (745706813405020531707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_296_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_296_1
  · norm_num [gridPoint]

theorem exp_6_297_0 : expNegUpper (45680334603815970635507 / 507022725041344614400 : ℝ) ≤ (745706736698952766821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2021559 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_297_1 : expNegUpper (114328052209363468481843 / 1267556812603361536000 : ℝ) ≤ (674498526496261398471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (252893 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_297 : rowCell 6 297 ≤ (25890660939465292221 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (745706736698952766821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (674498526496261398471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_297_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_297_1
  · norm_num [gridPoint]

theorem exp_6_298_0 : expNegUpper (3703672805419672648957 / 41062675346360064000 : ℝ) ≤ (337249228850723877473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (252893 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_298_1 : expNegUpper (7415603754174801127363 / 82125350692720128000 : ℝ) ≤ (24398904036969158919 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1012367 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_298 : rowCell 6 298 ≤ (93664783611951081007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (337249228850723877473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24398904036969158919 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_298_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_298_1
  · norm_num [gridPoint]

theorem exp_6_299_0 : expNegUpper (369373554103992391973 / 4090689529676288000 : ℝ) ≤ (304986269617743482311 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1012367 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_299_1 : expNegUpper (92446419253170388613 / 1022672382419072000 : ℝ) ≤ (551514083965276290537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2026329 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_299 : rowCell 6 299 ≤ (42348324043468844251 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (304986269617743482311 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (551514083965276290537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_299_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_299_1
  · norm_num [gridPoint]

theorem exp_6_300_0 : expNegUpper (58023488787086280537493 / 641874719731697792000 : ℝ) ≤ (275757014329089720291 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2026329 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_300_1 : expNegUpper (232353109671586993445491 / 2567498878926791168000 : ℝ) ≤ (124640843212454357209 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2027927 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_300 : rowCell 6 300 ≤ (76572587546878549059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (275757014329089720291 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (124640843212454357209 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_300_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_300_1
  · norm_num [gridPoint]

theorem exp_6_301_0 : expNegUpper (233334175428407982464939 / 2578339640111657472000 : ℝ) ≤ (498563323272726967753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2027927 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_301_1 : expNegUpper (23359491098774054741629 / 257833964011165747200 : ℝ) ≤ (225305679294479627633 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (202953 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_301 : rowCell 6 301 ≤ (17303667643870598623 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (498563323272726967753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (225305679294479627633 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_301_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_301_1
  · norm_num [gridPoint]

theorem exp_6_302_0 : expNegUpper (23457914214752247265709 / 258920323960227891200 : ℝ) ≤ (225305657077913883639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (202953 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_302_1 : expNegUpper (234841462073725280173961 / 2589203239602278912000 : ℝ) ≤ (407194983279225583341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2031137 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_302 : rowCell 6 302 ≤ (62552005894309442133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (225305657077913883639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (407194983279225583341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_302_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_302_1
  · norm_num [gridPoint]

theorem exp_6_303_0 : expNegUpper (235828865298027239455489 / 2600089677398655488000 : ℝ) ≤ (81438988692619872259 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2031137 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_303_1 : expNegUpper (14755798307617489902973 / 162505604837415968000 : ℝ) ≤ (367893176925151789187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (508187 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_303 : rowCell 6 303 ≤ (56520122106944435213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (81438988692619872259 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (367893176925151789187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_303_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_303_1
  · norm_num [gridPoint]

theorem exp_6_304_0 : expNegUpper (592708387180652323973 / 6527497383751968000 : ℝ) ≤ (367893141252305441071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (508187 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_304_1 : expNegUpper (9493954140981714758647 / 104439958140031488000 : ℝ) ≤ (332323142486867788651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (508591 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_304 : rowCell 6 304 ≤ (2042416020433117353 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (367893141252305441071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (332323142486867788651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_304_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_304_1
  · norm_num [gridPoint]

theorem exp_6_305_0 : expNegUpper (238342620862562189787287 / 2621931067908674048000 : ℝ) ≤ (332323110531510811807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (508591 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_305_1 : expNegUpper (119304856937026509229423 / 1310965533954337024000 : ℝ) ≤ (300136960329449588723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2035983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_305 : rowCell 6 305 ≤ (46119556593026146551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (332323110531510811807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (300136960329449588723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_305_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_305_1
  · norm_num [gridPoint]

theorem exp_6_306_0 : expNegUpper (119803336630634833389407 / 1316443010311158016000 : ℝ) ≤ (300136931708950243 / 1000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2035983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_306_1 : expNegUpper (47975072792549786730929 / 526577204124463206400 : ℝ) ≤ (271018485536314494487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2037607 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_306 : rowCell 6 306 ≤ (41649166172969885951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (300136931708950243 / 1000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (271018485536314494487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_306_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_306_1
  · norm_num [gridPoint]

theorem exp_6_307_0 : expNegUpper (48175104412144401458569 / 528772762328342630400 : ℝ) ≤ (13550922995344570591 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2037607 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_307_1 : expNegUpper (60286453445742315320659 / 660965952910428288000 : ℝ) ≤ (47789162824796749 / 195312500000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (407847 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_307 : rowCell 6 307 ≤ (37605232476010084571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13550922995344570591 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47789162824796749 / 195312500000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_307_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_307_1
  · norm_num [gridPoint]

theorem exp_6_308_0 : expNegUpper (60537294313314464514611 / 663716110241716352000 : ℝ) ≤ (244680490715795964777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (407847 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_308_1 : expNegUpper (242421073327052648071883 / 2654864440966865408000 : ℝ) ≤ (44172438492363345113 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (510217 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_308 : rowCell 6 308 ≤ (33947790718315934767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (244680490715795964777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44172438492363345113 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_308_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_308_1
  · norm_num [gridPoint]

theorem exp_6_309_0 : expNegUpper (9737105953248634632187 / 106635516343910912000 : ℝ) ≤ (110431085959778897297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (510217 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_309_1 : expNegUpper (4874023051746754815029 / 53317758171955456000 : ℝ) ≤ (99663329457557300483 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (255313 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_309 : rowCell 6 309 ≤ (30640547057867014111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (110431085959778897297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (99663329457557300483 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_309_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_309_1
  · norm_num [gridPoint]

theorem exp_6_310_0 : expNegUpper (122355473393467338630301 / 1338467107267217664000 : ℝ) ≤ (19932664052870801691 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (255313 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_310_1 : expNegUpper (244986061556163186050401 / 2676934214534435328000 : ℝ) ≤ (179858882580854505603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (408829 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_310 : rowCell 6 310 ≤ (2765054901964271789 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19932664052870801691 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (179858882580854505603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_310_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_310_1
  · norm_num [gridPoint]

theorem exp_6_311_0 : expNegUpper (245999081112752939155289 / 2688003358776852992000 : ℝ) ≤ (179858866126704917859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (408829 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_311_1 : expNegUpper (1231379051129338153489 / 13440016793884264960 : ℝ) ≤ (32452739559437621167 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2045789 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_311 : rowCell 6 311 ≤ (24947884737071304661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (179858866126704917859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32452739559437621167 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_311_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_311_1
  · norm_num [gridPoint]

theorem exp_6_312_0 : expNegUpper (1236460309005046491089 / 13495476706625128960 : ℝ) ≤ (32452736614918438811 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2045789 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_312_1 : expNegUpper (247570408588789721422711 / 2699095341325025792000 : ℝ) ≤ (146364008711761557787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1023719 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_312 : rowCell 6 312 ≤ (22505408567752754887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32452736614918438811 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (146364008711761557787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_312_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_312_1
  · norm_num [gridPoint]

theorem exp_6_313_0 : expNegUpper (248589898844042401177199 / 2710210162178953728000 : ℝ) ≤ (7318199777029878469 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1023719 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_313_1 : expNegUpper (124434933318634052477099 / 1355105081089476864000 : ℝ) ≤ (32999788103400080361 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2049091 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_313 : rowCell 6 313 ≤ (20298490840710850299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7318199777029878469 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32999788103400080361 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_313_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_313_1
  · norm_num [gridPoint]

theorem exp_6_314_0 : expNegUpper (4997852044683817895251 / 54426956426772736000 : ℝ) ≤ (65999570316123560787 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2049091 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_314_1 : expNegUpper (10006967774545657120853 / 108853912853545472000 : ℝ) ≤ (59511703326925935923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2050749 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_314 : rowCell 6 314 ≤ (3660957935234433191 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (65999570316123560787 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (59511703326925935923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_314_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_314_1
  · norm_num [gridPoint]

theorem exp_6_315_0 : expNegUpper (13221062208620706615943 / 143816227305477632000 : ℝ) ≤ (14877924514664388847 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2050749 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_315_1 : expNegUpper (3308992128424320228331 / 35954056826369408000 : ℝ) ≤ (13413078719460471527 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (205241 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_315 : rowCell 6 315 ≤ (16504042988244823821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14877924514664388847 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13413078719460471527 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_315_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_315_1
  · norm_num [gridPoint]

theorem exp_6_316_0 : expNegUpper (63128162006297160181841 / 685922913643817088000 : ℝ) ≤ (107304620333908916191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (205241 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_316_1 : expNegUpper (50559499763885495935751 / 548738330915053670400 : ℝ) ≤ (12090377667480223059 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (82163 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_316 : rowCell 6 316 ≤ (14877878936934217353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (107304620333908916191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12090377667480223059 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_316_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_316_1
  · norm_num [gridPoint]

theorem exp_6_317_0 : expNegUpper (50766002082143037312991 / 550979565730443366400 : ℝ) ≤ (2418075322904892441 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (82163 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_317_1 : expNegUpper (127058247766758750863593 / 1377448914326108416000 : ℝ) ≤ (21792498359331422519 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (411149 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_317 : rowCell 6 317 ≤ (2681928647934335067 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2418075322904892441 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21792498359331422519 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_317_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_317_1
  · norm_num [gridPoint]

theorem exp_6_318_0 : expNegUpper (127576139556355854972377 / 1383063420517460224000 : ℝ) ≤ (43584992953615107209 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (411149 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_318_1 : expNegUpper (255440401894857050227513 / 2766126841034920448000 : ℝ) ≤ (9818392803801563437 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1028709 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_318 : rowCell 6 318 ≤ (12084241884863398133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43584992953615107209 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9818392803801563437 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_318_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_318_1
  · norm_num [gridPoint]

theorem exp_6_319_0 : expNegUpper (10259178564940674303833 / 111095147668935168000 : ℝ) ≤ (15709427140023016399 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1028709 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_319_1 : expNegUpper (160480767434865482443 / 1735861682327112000 : ℝ) ≤ (1105708016617223487 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (257387 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_319 : rowCell 6 319 ≤ (10887997911746165789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15709427140023016399 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1105708016617223487 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_319_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_319_1
  · norm_num [gridPoint]

theorem sum_6_288_2 : blockSum (rowCell 6) 288 2 ≤ (483212206071443431163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_288) (by simpa only [blockSum_one] using cell_6_289) (by norm_num)

theorem sum_6_290_2 : blockSum (rowCell 6) 290 2 ≤ (49564537870689059987 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_290) (by simpa only [blockSum_one] using cell_6_291) (by norm_num)

theorem sum_6_288_4 : blockSum (rowCell 6) 288 4 ≤ (879728509036955911059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_288_2 sum_6_290_2 (by norm_num)

theorem sum_6_292_2 : blockSum (rowCell 6) 292 2 ≤ (162556558148110140109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_292) (by simpa only [blockSum_one] using cell_6_293) (by norm_num)

theorem sum_6_294_2 : blockSum (rowCell 6) 294 2 ≤ (33294516601149895751 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_294) (by simpa only [blockSum_one] using cell_6_295) (by norm_num)

theorem sum_6_292_4 : blockSum (rowCell 6) 292 4 ≤ (295734624552709723113 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_292_2 sum_6_294_2 (by norm_num)

theorem sum_6_288_8 : blockSum (rowCell 6) 288 8 ≤ (294239551628475071457 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_288_4 sum_6_292_4 (by norm_num)

theorem sum_6_296_2 : blockSum (rowCell 6) 296 2 ≤ (218046981208681325017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_296) (by simpa only [blockSum_one] using cell_6_297) (by norm_num)

theorem sum_6_298_2 : blockSum (rowCell 6) 298 2 ≤ (178361431698888769509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_298) (by simpa only [blockSum_one] using cell_6_299) (by norm_num)

theorem sum_6_296_4 : blockSum (rowCell 6) 296 4 ≤ (198204206453785047263 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_296_2 sum_6_298_2 (by norm_num)

theorem sum_6_300_2 : blockSum (rowCell 6) 300 2 ≤ (145787258122360943551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_300) (by simpa only [blockSum_one] using cell_6_301) (by norm_num)

theorem sum_6_302_2 : blockSum (rowCell 6) 302 2 ≤ (59536064000626938673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_302) (by simpa only [blockSum_one] using cell_6_303) (by norm_num)

theorem sum_6_300_4 : blockSum (rowCell 6) 300 4 ≤ (264859386123614820897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_300_2 sum_6_302_2 (by norm_num)

theorem sum_6_296_8 : blockSum (rowCell 6) 296 8 ≤ (661267799031184915423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_296_4 sum_6_300_4 (by norm_num)

theorem sum_6_288_16 : blockSum (rowCell 6) 288 16 ≤ (533116389293390068177 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_288_8 sum_6_296_8 (by norm_num)

theorem sum_6_304_2 : blockSum (rowCell 6) 304 2 ≤ (12147494637981760047 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_304) (by simpa only [blockSum_one] using cell_6_305) (by norm_num)

theorem sum_6_306_2 : blockSum (rowCell 6) 306 2 ≤ (39627199324489985261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_306) (by simpa only [blockSum_one] using cell_6_307) (by norm_num)

theorem sum_6_304_4 : blockSum (rowCell 6) 304 4 ≤ (88217177876417025449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_304_2 sum_6_306_2 (by norm_num)

theorem sum_6_308_2 : blockSum (rowCell 6) 308 2 ≤ (32294168888091474439 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_308) (by simpa only [blockSum_one] using cell_6_309) (by norm_num)

theorem sum_6_310_2 : blockSum (rowCell 6) 310 2 ≤ (52598433756714022551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_310) (by simpa only [blockSum_one] using cell_6_311) (by norm_num)

theorem sum_6_308_4 : blockSum (rowCell 6) 308 4 ≤ (117186771532896971429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_308_2 sum_6_310_2 (by norm_num)

theorem sum_6_304_8 : blockSum (rowCell 6) 304 8 ≤ (293621127285731022327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_304_4 sum_6_308_4 (by norm_num)

theorem sum_6_312_2 : blockSum (rowCell 6) 312 2 ≤ (21401949704231802593 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_312) (by simpa only [blockSum_one] using cell_6_313) (by norm_num)

theorem sum_6_314_2 : blockSum (rowCell 6) 314 2 ≤ (2175552041526061861 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_314) (by simpa only [blockSum_one] using cell_6_315) (by norm_num)

theorem sum_6_312_4 : blockSum (rowCell 6) 312 4 ≤ (38806366036440297481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_312_2 sum_6_314_2 (by norm_num)

theorem sum_6_316_2 : blockSum (rowCell 6) 316 2 ≤ (1767970136037868293 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_316) (by simpa only [blockSum_one] using cell_6_317) (by norm_num)

theorem sum_6_318_2 : blockSum (rowCell 6) 318 2 ≤ (11486119898304781961 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_318) (by simpa only [blockSum_one] using cell_6_319) (by norm_num)

theorem sum_6_316_4 : blockSum (rowCell 6) 316 4 ≤ (5125976197321545661 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_316_2 sum_6_318_2 (by norm_num)

theorem sum_6_312_8 : blockSum (rowCell 6) 312 8 ≤ (32218123511524012893 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_312_4 sum_6_316_4 (by norm_num)

theorem sum_6_304_16 : blockSum (rowCell 6) 304 16 ≤ (422493621331827073899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_304_8 sum_6_312_8 (by norm_num)

theorem sum_6_288_32 : blockSum (rowCell 6) 288 32 ≤ (2554959178505387346607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_288_16 sum_6_304_16 (by norm_num)

#print axioms sum_6_288_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
