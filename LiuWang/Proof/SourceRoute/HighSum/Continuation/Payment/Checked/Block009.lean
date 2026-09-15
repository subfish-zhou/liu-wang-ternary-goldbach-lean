import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_288_0 : expNegUpper (6395722438464789731607 / 76224722892415504000 : ℝ) ≤ (363462425571454291319997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1926137 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_288_1 : expNegUpper (204931473236725457792623 / 2439191132557296128000 : ℝ) ≤ (325596150121152986132263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1927793 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_288 : rowCell 0 288 ≤ (5024677041556902149867 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (363462425571454291319997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (325596150121152986132263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_288_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_288_1
  · norm_num [gridPoint]

theorem exp_0_289_0 : expNegUpper (914752209465943084743 / 10887812595880448000 : ℝ) ≤ (325596122936097595855239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1927793 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_289_1 : expNegUpper (457975874227612193751 / 5443906297940224000 : ℝ) ≤ (291629771764274202927981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1929453 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_289 : rowCell 0 289 ≤ (45008666780440881432561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (325596122936097595855239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (291629771764274202927981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_289_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_289_1
  · norm_num [gridPoint]

theorem exp_0_290_0 : expNegUpper (103490001379894492925671 / 1230173686947330304000 : ℝ) ≤ (18226859226534657171233 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1929453 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_290_1 : expNegUpper (207251443429892934621381 / 2460347373894660608000 : ℝ) ≤ (261166687611547059526553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1931117 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_290 : rowCell 0 290 ≤ (20155206355231904615253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18226859226534657171233 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (261166687611547059526553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_290_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_290_1
  · norm_num [gridPoint]

theorem exp_0_291_0 : expNegUpper (208145394913067293492989 / 2470959752021975552000 : ℝ) ≤ (130583333089454510410587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1931117 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_291_1 : expNegUpper (10420919165573322341099 / 123547987601098777600 : ℝ) ≤ (1826953483627393699933 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (386557 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_291 : rowCell 0 291 ≤ (564016615416958285669 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (130583333089454510410587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1826953483627393699933 / 7812500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_291_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_291_1
  · norm_num [gridPoint]

theorem exp_0_292_0 : expNegUpper (1162863519900059798451 / 13786638713639142400 : ℝ) ≤ (233850026877721756244239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (386557 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_292_1 : expNegUpper (23287774782164963390979 / 275732774272782848000 : ℝ) ≤ (26169855977520561441013 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (241807 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_292 : rowCell 0 292 ≤ (6463837867688645313947 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (233850026877721756244239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26169855977520561441013 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_292_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_292_1
  · norm_num [gridPoint]

theorem exp_0_293_0 : expNegUpper (210490128758958043264979 / 2492253023193870848000 : ℝ) ≤ (209358830931774954718319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (241807 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_293_1 : expNegUpper (105383111303143126220469 / 1246126511596935424000 : ℝ) ≤ (187404399991300590735679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1936131 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_293 : rowCell 0 293 ≤ (28932331265875951225191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (209358830931774954718319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (187404399991300590735679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_293_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_293_1
  · norm_num [gridPoint]

theorem exp_0_294_0 : expNegUpper (4233389808724955577069 / 50058678324769024000 : ℝ) ≤ (187404385002799008745481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1936131 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_294_1 : expNegUpper (8477885680168393572697 / 100117356649538048000 : ℝ) ≤ (83863556029169280326121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1937809 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_294 : rowCell 0 294 ≤ (25896507829152542426267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (187404385002799008745481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (83863556029169280326121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_294_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_294_1
  · norm_num [gridPoint]

theorem exp_0_295_0 : expNegUpper (23650392067357624135073 / 279293071954309632000 : ℝ) ≤ (167727098757740683806969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1937809 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_295_1 : expNegUpper (2960176961466584414963 / 34911633994288704000 : ℝ) ≤ (37523401586985719439047 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (484873 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_295 : rowCell 0 295 ≤ (23175771358346188696761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (167727098757740683806969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37523401586985719439047 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_295_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_295_1
  · norm_num [gridPoint]

theorem exp_0_296_0 : expNegUpper (26755281657651150635083 / 315545527155609664000 : ℝ) ≤ (30018718909341596509677 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (484873 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_296_1 : expNegUpper (42864606052555522969947 / 504872843448975462400 : ℝ) ≤ (67147054916045803391251 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (970589 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_296 : rowCell 0 296 ≤ (4147561381576043776353 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30018718909341596509677 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (67147054916045803391251 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_296_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_296_1
  · norm_num [gridPoint]

theorem exp_0_297_0 : expNegUpper (43047134878711637835507 / 507022725041344614400 : ℝ) ≤ (67147049681277376659297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (970589 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_297_1 : expNegUpper (107759009554049548481843 / 1267556812603361536000 : ℝ) ≤ (120140101317888142009457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (485717 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_297 : rowCell 0 297 ≤ (1159598156677816860171 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (67147049681277376659297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (120140101317888142009457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_297_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_297_1
  · norm_num [gridPoint]

theorem exp_0_298_0 : expNegUpper (387874197124738738773 / 4562519482928896000 : ℝ) ≤ (60070046015485362343269 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (485717 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_298_1 : expNegUpper (776766013454828569707 / 9125038965857792000 : ℝ) ≤ (429848757413243423577 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1944561 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_298 : rowCell 0 298 ≤ (8298481422483247023217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (60070046015485362343269 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (429848757413243423577 / 4000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_298_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_298_1
  · norm_num [gridPoint]

theorem exp_0_299_0 : expNegUpper (348218633695497492773 / 4090689529676288000 : ℝ) ≤ (13432772639559954122191 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1944561 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_299_1 : expNegUpper (87168854477004193413 / 1022672382419072000 : ℝ) ≤ (96108198638951110432299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (973129 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_299 : rowCell 0 299 ≤ (7422267493514535664627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13432772639559954122191 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (96108198638951110432299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_299_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_299_1
  · norm_num [gridPoint]

theorem exp_0_300_0 : expNegUpper (54711054144535496537493 / 641874719731697792000 : ℝ) ≤ (4805409566719952582457 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (973129 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_300_1 : expNegUpper (219131284416277681445491 / 2567498878926791168000 : ℝ) ≤ (85941444829122166266427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1947959 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_300 : rowCell 0 300 ≤ (6637611514631978936999 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4805409566719952582457 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (85941444829122166266427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_300_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_300_1
  · norm_num [gridPoint]

theorem exp_0_301_0 : expNegUpper (24450724838145669162771 / 286482182234628608000 : ℝ) ≤ (42970719176073641084413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1947959 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_301_1 : expNegUpper (2448279693528193460181 / 28648218223462860800 : ℝ) ≤ (1920979487663588740137 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (60927 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_301 : rowCell 0 301 ≤ (11870108902467092870527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42970719176073641084413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1920979487663588740137 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_301_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_301_1
  · norm_num [gridPoint]

theorem exp_0_302_0 : expNegUpper (22127357694753168865709 / 258920323960227891200 : ℝ) ≤ (76839173764104396017619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (60927 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_302_1 : expNegUpper (221563810188628320173961 / 2589203239602278912000 : ℝ) ≤ (68691188840312161402127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (487843 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_302 : rowCell 0 302 ≤ (10612204791049207772549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (76839173764104396017619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (68691188840312161402127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_302_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_302_1
  · norm_num [gridPoint]

theorem exp_0_303_0 : expNegUpper (222495386783142631455489 / 2600089677398655488000 : ℝ) ≤ (429319898435881106891 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (487843 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_303_1 : expNegUpper (13924200482618065902973 / 162505604837415968000 : ℝ) ≤ (61398531002775482437281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1953083 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_303 : rowCell 0 303 ≤ (2371564719307899548413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (429319898435881106891 / 6250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (61398531002775482437281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_303_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_303_1
  · norm_num [gridPoint]

theorem exp_0_304_0 : expNegUpper (62144989734022915997 / 725277487083552000 : ℝ) ≤ (3837407905664496600121 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1953083 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_304_1 : expNegUpper (995623888931814493183 / 11604439793336832000 : ℝ) ≤ (10974479768315259932049 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1954799 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_304 : rowCell 0 304 ≤ (2119645084346025850091 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3837407905664496600121 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10974479768315259932049 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_304_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_304_1
  · norm_num [gridPoint]

theorem exp_0_305_0 : expNegUpper (224953315717889933787287 / 2621931067908674048000 : ℝ) ≤ (2743619742131335151373 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1954799 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_305_1 : expNegUpper (112624161022137293229423 / 1310965533954337024000 : ℝ) ≤ (49033095591647769976013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (978259 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_305 : rowCell 0 305 ≤ (3788440857528178307443 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2743619742131335151373 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (49033095591647769976013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_305_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_305_1
  · norm_num [gridPoint]

theorem exp_0_306_0 : expNegUpper (113094727400851793389407 / 1316443010311158016000 : ℝ) ≤ (39226473638364830573 / 800000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (978259 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_306_1 : expNegUpper (45297211763615335530929 / 526577204124463206400 : ℝ) ≤ (43809112580264169231847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1958241 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_306 : rowCell 0 306 ≤ (1692534243602009548427 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (39226473638364830573 / 800000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43809112580264169231847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_306_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_306_1
  · norm_num [gridPoint]

theorem exp_0_307_0 : expNegUpper (5054008673028046739841 / 58752529147593625600 : ℝ) ≤ (43809109440382594400603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1958241 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_307_1 : expNegUpper (6325794314538977257851 / 73440661434492032000 : ℝ) ≤ (39136298937310350324929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1959967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_307 : rowCell 0 307 ≤ (6048453700166708862891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43809109440382594400603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39136298937310350324929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_307_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_307_1
  · norm_num [gridPoint]

theorem exp_0_308_0 : expNegUpper (57169033040976032514611 / 663716110241716352000 : ℝ) ≤ (39136296155559220319423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1959967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_308_1 : expNegUpper (228975941552592744071883 / 2654864440966865408000 : ℝ) ≤ (4369639285334505329987 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1961697 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_308 : rowCell 0 308 ≤ (1350739514363638994247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (39136296155559220319423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4369639285334505329987 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_308_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_308_1
  · norm_num [gridPoint]

theorem exp_0_309_0 : expNegUpper (9197067617078732552187 / 106635516343910912000 : ℝ) ≤ (1747855590925124961257 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1961697 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_309_1 : expNegUpper (4604562149959680255029 / 53317758171955456000 : ℝ) ≤ (31219956232185316671587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (196343 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_309 : rowCell 0 309 ≤ (150802851819241635157 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1747855590925124961257 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31219956232185316671587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_309_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_309_1
  · norm_num [gridPoint]

theorem exp_0_310_0 : expNegUpper (12843448614877405625589 / 148718567474135296000 : ℝ) ≤ (31219954049592818213173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (196343 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_310_1 : expNegUpper (25720567016879514894489 / 297437134948270592000 : ℝ) ≤ (13939277675504202801683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (122823 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_310 : rowCell 0 310 ≤ (861903280361776168673 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31219954049592818213173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13939277675504202801683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_310_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_310_1
  · norm_num [gridPoint]

theorem exp_0_311_0 : expNegUpper (232442296078717739155289 / 2688003358776852992000 : ℝ) ≤ (13939276709024548998607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (122823 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_311_1 : expNegUpper (1163734692533631273489 / 13440016793884264960 : ℝ) ≤ (6222857724152178765253 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (491727 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_311 : rowCell 0 311 ≤ (769606933351526085717 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13939276709024548998607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6222857724152178765253 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_311_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_311_1
  · norm_num [gridPoint]

theorem exp_0_312_0 : expNegUpper (1168536817260401371089 / 13495476706625128960 : ℝ) ≤ (24891429184931844017909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (491727 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_312_1 : expNegUpper (234013623554754521422711 / 2699095341325025792000 : ℝ) ≤ (22221401338815856946551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1968653 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_312 : rowCell 0 312 ≤ (214719370607834752119 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24891429184931844017909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22221401338815856946551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_312_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_312_1
  · norm_num [gridPoint]

theorem exp_0_313_0 : expNegUpper (26108587464468839241911 / 301134462464328192000 : ℝ) ≤ (22221399823266096116989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1968653 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_313_1 : expNegUpper (13071398238241060053011 / 150567231232164096000 : ℝ) ≤ (9917572114417429419817 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1970401 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_313 : rowCell 0 313 ≤ (3066800977455498444889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22221399823266096116989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9917572114417429419817 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_313_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_313_1
  · norm_num [gridPoint]

theorem exp_0_314_0 : expNegUpper (4725041545109484455251 / 54426956426772736000 : ℝ) ≤ (4958785721773772632527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1970401 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_314_1 : expNegUpper (9462463307992743200853 / 108853912853545472000 : ℝ) ≤ (3540560103517945744581 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (246519 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_314 : rowCell 0 314 ≤ (171081284910352791653 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4958785721773772632527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3540560103517945744581 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_314_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_314_1
  · norm_num [gridPoint]

theorem exp_0_315_0 : expNegUpper (237531743670182929702917 / 2732508318804075008000 : ℝ) ≤ (3540559865972681095339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (246519 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_315_1 : expNegUpper (59460719195382916338289 / 683127079701018752000 : ℝ) ≤ (15797618901930874375797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1973907 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_315 : rowCell 0 315 ≤ (1221440297747222007259 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3540559865972681095339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15797618901930874375797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_315_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_315_1
  · norm_num [gridPoint]

theorem exp_0_316_0 : expNegUpper (6633786011574564464649 / 76213657071535232000 : ℝ) ≤ (15797617850659617925757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1973907 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_316_1 : expNegUpper (5313979122795932970639 / 60970925657228185600 : ℝ) ≤ (14095636209616920728879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (987833 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_316 : rowCell 0 316 ≤ (2179842943295809978399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15797617850659617925757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14095636209616920728879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_316_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_316_1
  · norm_num [gridPoint]

theorem exp_0_317_0 : expNegUpper (48021149097463408512991 / 550979565730443366400 : ℝ) ≤ (14095635279229486459029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (987833 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_317_1 : expNegUpper (120210071962506590863593 / 1377448914326108416000 : ℝ) ≤ (3143847556222868690621 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (494357 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_317 : rowCell 0 317 ≤ (1944875142009976850949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14095635279229486459029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3143847556222868690621 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_317_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_317_1
  · norm_num [gridPoint]

theorem exp_0_318_0 : expNegUpper (120700050437209870972377 / 1383063420517460224000 : ℝ) ≤ (12575389401580630826291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (494357 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_318_1 : expNegUpper (241716136971458906227513 / 2766126841034920448000 : ℝ) ≤ (11217661709803916077131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (989597 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_318 : rowCell 0 318 ≤ (108438166475719940297 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12575389401580630826291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11217661709803916077131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_318_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_318_1
  · norm_num [gridPoint]

theorem exp_0_319_0 : expNegUpper (1078663878090360291537 / 12343905296548352000 : ℝ) ≤ (5608830490664081038107 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (989597 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_319_1 : expNegUpper (16876184003992555827 / 192873520258568000 : ℝ) ≤ (5002621347852289762997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (495241 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_319 : rowCell 0 319 ≤ (1547593203581749851737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5608830490664081038107 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5002621347852289762997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_319_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_319_1
  · norm_num [gridPoint]

theorem sum_0_288_2 : blockSum (rowCell 0) 288 2 ≤ (95255437196009902931231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_288) (by simpa only [blockSum_one] using cell_0_289) (by norm_num)

theorem sum_0_290_2 : blockSum (rowCell 0) 290 2 ≤ (38203738048574569756661 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_290) (by simpa only [blockSum_one] using cell_0_291) (by norm_num)

theorem sum_0_288_4 : blockSum (rowCell 0) 288 4 ≤ (171662913293159042444553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_288_2 sum_0_290_2 (by norm_num)

theorem sum_0_292_2 : blockSum (rowCell 0) 292 2 ≤ (30625760302159588897463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_292) (by simpa only [blockSum_one] using cell_0_293) (by norm_num)

theorem sum_0_294_2 : blockSum (rowCell 0) 294 2 ≤ (12268069796874682780757 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_294) (by simpa only [blockSum_one] using cell_0_295) (by norm_num)

theorem sum_0_292_4 : blockSum (rowCell 0) 292 4 ≤ (55161899895908954458977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_292_2 sum_0_294_2 (by norm_num)

theorem sum_0_288_8 : blockSum (rowCell 0) 288 8 ≤ (281986713084976951362507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_288_4 sum_0_292_4 (by norm_num)

theorem sum_0_296_2 : blockSum (rowCell 0) 296 2 ≤ (39291377414725288644501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_296) (by simpa only [blockSum_one] using cell_0_297) (by norm_num)

theorem sum_0_298_2 : blockSum (rowCell 0) 298 2 ≤ (3930187228999445671961 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_298) (by simpa only [blockSum_one] using cell_0_299) (by norm_num)

theorem sum_0_296_4 : blockSum (rowCell 0) 296 4 ≤ (70732875246720854020189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_296_2 sum_0_298_2 (by norm_num)

theorem sum_0_300_2 : blockSum (rowCell 0) 300 2 ≤ (1005813277269242029781 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_300) (by simpa only [blockSum_one] using cell_0_301) (by norm_num)

theorem sum_0_302_2 : blockSum (rowCell 0) 302 2 ≤ (20098463668280805966201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_302) (by simpa only [blockSum_one] using cell_0_303) (by norm_num)

theorem sum_0_300_4 : blockSum (rowCell 0) 300 4 ≤ (22621897800005928355363 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_300_2 sum_0_302_2 (by norm_num)

theorem sum_0_296_8 : blockSum (rowCell 0) 296 8 ≤ (23195334169346542146183 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_296_4 sum_0_300_4 (by norm_num)

theorem sum_0_288_16 : blockSum (rowCell 0) 288 16 ≤ (198981691965854831046711 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_288_8 sum_0_296_8 (by norm_num)

theorem sum_0_304_2 : blockSum (rowCell 0) 304 2 ≤ (64221848209761840061 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_304) (by simpa only [blockSum_one] using cell_0_305) (by norm_num)

theorem sum_0_306_2 : blockSum (rowCell 0) 306 2 ≤ (12818590674574747056599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_306) (by simpa only [blockSum_one] using cell_0_307) (by norm_num)

theorem sum_0_304_4 : blockSum (rowCell 0) 304 4 ≤ (28874052727015207071849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_304_2 sum_0_306_2 (by norm_num)

theorem sum_0_308_2 : blockSum (rowCell 0) 308 2 ≤ (2557162328917572075503 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_308) (by simpa only [blockSum_one] using cell_0_309) (by norm_num)

theorem sum_0_310_2 : blockSum (rowCell 0) 310 2 ≤ (163151021371330225439 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_310) (by simpa only [blockSum_one] using cell_0_311) (by norm_num)

theorem sum_0_308_4 : blockSum (rowCell 0) 308 4 ≤ (9193100192118399786981 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_308_2 sum_0_310_2 (by norm_num)

theorem sum_0_304_8 : blockSum (rowCell 0) 304 8 ≤ (47260253111252006645811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_304_4 sum_0_308_4 (by norm_num)

theorem sum_0_312_2 : blockSum (rowCell 0) 312 2 ≤ (6502310907180854478793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_312) (by simpa only [blockSum_one] using cell_0_313) (by norm_num)

theorem sum_0_314_2 : blockSum (rowCell 0) 314 2 ≤ (2590090577030044340483 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_314) (by simpa only [blockSum_one] using cell_0_315) (by norm_num)

theorem sum_0_312_4 : blockSum (rowCell 0) 312 4 ≤ (11682492061240943159759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_312_2 sum_0_314_2 (by norm_num)

theorem sum_0_316_2 : blockSum (rowCell 0) 316 2 ≤ (1031179521326446707337 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_316) (by simpa only [blockSum_one] using cell_0_317) (by norm_num)

theorem sum_0_318_2 : blockSum (rowCell 0) 318 2 ≤ (3282603867193268896489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_318) (by simpa only [blockSum_one] using cell_0_319) (by norm_num)

theorem sum_0_316_4 : blockSum (rowCell 0) 316 4 ≤ (7407321952499055725837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_316_2 sum_0_318_2 (by norm_num)

theorem sum_0_312_8 : blockSum (rowCell 0) 312 8 ≤ (4772453503434999721399 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_312_4 sum_0_316_4 (by norm_num)

theorem sum_0_304_16 : blockSum (rowCell 0) 304 16 ≤ (66350067124992005531407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_304_8 sum_0_312_8 (by norm_num)

theorem sum_0_288_32 : blockSum (rowCell 0) 288 32 ≤ (464313451056701667624829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_288_16 sum_0_304_16 (by norm_num)

#print axioms sum_0_288_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
