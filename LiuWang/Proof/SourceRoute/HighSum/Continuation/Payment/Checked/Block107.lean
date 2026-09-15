import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_352_0 : expNegUpper (1894375116113548674929 / 19759387837319683200 : ℝ) ≤ (2310392119512771551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1057443 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_352_1 : expNegUpper (303445803591807583633711 / 3161502053971149312000 : ℝ) ≤ (414204982092385857 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1058347 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_352 : rowCell 6 352 ≤ (319496866255118053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2310392119512771551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (414204982092385857 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_352_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_352_1
  · norm_num [gridPoint]

theorem exp_6_353_0 : expNegUpper (16031594922629524455581 / 167027916160804352000 : ℝ) ≤ (1035512387290227213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1058347 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_353_1 : expNegUpper (8024943231058631506861 / 83513958080402176000 : ℝ) ≤ (928100266828849389 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1059253 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_353 : rowCell 6 353 ≤ (143188398921607001 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1035512387290227213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (928100266828849389 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_353_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_353_1
  · norm_num [gridPoint]

theorem exp_6_354_0 : expNegUpper (6122117090448308022239 / 63711631968903424000 : ℝ) ≤ (371240082558317077 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1059253 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_354_1 : expNegUpper (12258206053603568783437 / 127423263937806848000 : ℝ) ≤ (831715470733943777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2120321 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_354 : rowCell 6 354 ≤ (25665468052139561 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (371240082558317077 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (831715470733943777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_354_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_354_1
  · norm_num [gridPoint]

theorem exp_6_355_0 : expNegUpper (307616681547869744085437 / 3197655628140814848000 : ℝ) ≤ (1663430833971118109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2120321 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_355_1 : expNegUpper (76991934815932474334599 / 799413907035203712000 : ℝ) ≤ (1490477099648381249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2122141 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_355 : rowCell 6 355 ≤ (45997160021738601 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1663430833971118109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1490477099648381249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_355_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_355_1
  · norm_num [gridPoint]

theorem exp_6_356_0 : expNegUpper (77283198649665660076391 / 802438124035553408000 : ℝ) ≤ (372619251013457777 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2122141 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_356_1 : expNegUpper (61897123308697735449439 / 641950499228442726400 : ℝ) ≤ (41728891389948461 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (530991 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_356 : rowCell 6 356 ≤ (51514996566656873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (372619251013457777 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41728891389948461 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_356_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_356_1
  · norm_num [gridPoint]

theorem exp_6_357_0 : expNegUpper (62130840733426547300279 / 644374440489873510400 : ℝ) ≤ (1335324439478525643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (530991 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_357_1 : expNegUpper (155504396585852103020693 / 1610936101224683776000 : ℝ) ≤ (1196161062798158693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2125791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_357 : rowCell 6 357 ≤ (92299098603760887 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1335324439478525643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1196161062798158693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_357_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_357_1
  · norm_num [gridPoint]

theorem exp_6_358_0 : expNegUpper (156090459372809339700997 / 1617007373531138304000 : ℝ) ≤ (1196160987227985507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2125791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_358_1 : expNegUpper (312537279140715130450033 / 3234014747062276608000 : ℝ) ≤ (1071356838412348651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1063811 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_358 : rowCell 6 358 ≤ (165349437068739641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1196160987227985507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1071356838412348651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_358_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_358_1
  · norm_num [gridPoint]

theorem exp_6_359_0 : expNegUpper (12548517993058364629457 / 129847205199237632000 : ℝ) ≤ (1071356771233803059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1063811 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_359_1 : expNegUpper (1570355422214300486011 / 16230900649904704000 : ℝ) ≤ (29982692409697899 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (133091 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_359 : rowCell 6 359 ≤ (148087974084360319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1071356771233803059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29982692409697899 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_359_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_359_1
  · norm_num [gridPoint]

theorem exp_6_360_0 : expNegUpper (1271170592346744726749 / 13138582061311936000 : ℝ) ≤ (959446097398709713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (133091 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_360_1 : expNegUpper (10180974808725088807321 / 105108656490495488000 : ℝ) ≤ (26847224440990827 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (426259 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_360 : rowCell 6 360 ≤ (66305415340977679 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (959446097398709713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26847224440990827 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_360_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_360_1
  · norm_num [gridPoint]

theorem exp_6_361_0 : expNegUpper (316792999964558055623039 / 3270579410735534592000 : ℝ) ≤ (429555564521679927 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (426259 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_361_1 : expNegUpper (6343093860318134893067 / 65411588214710691840 : ℝ) ≤ (769167209495625543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2133137 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_361 : rowCell 6 361 ≤ (118735519352582597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (429555564521679927 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (769167209495625543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_361_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_361_1
  · norm_num [gridPoint]

theorem exp_6_362_0 : expNegUpper (6366820780129877052667 / 65656266171429283840 : ℝ) ≤ (384583581168510791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2133137 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_362_1 : expNegUpper (318704516271485718810461 / 3282813308571464192000 : ℝ) ≤ (172137347321589969 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2134983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_362 : rowCell 6 362 ≤ (53149000305795663 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (384583581168510791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (172137347321589969 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_362_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_362_1
  · norm_num [gridPoint]

theorem exp_6_363_0 : expNegUpper (319894434020138729993749 / 3295070044713148928000 : ℝ) ≤ (86068668423038097 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2134983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_363_1 : expNegUpper (80064924707388330556837 / 823767511178287232000 : ℝ) ≤ (616300752487825177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2136833 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_363 : rowCell 6 363 ≤ (95150841608937321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (86068668423038097 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (616300752487825177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_363_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_363_1
  · norm_num [gridPoint]

theorem exp_6_364_0 : expNegUpper (3214531949978313344333 / 33073496191605888000 : ℝ) ≤ (154075178815185639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2136833 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_364_1 : expNegUpper (12872810027297928065323 / 132293984766423552000 : ℝ) ≤ (275780708811737717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1069343 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_364 : rowCell 6 364 ≤ (85161555981052189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (154075178815185639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (275780708811737717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_364_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_364_1
  · norm_num [gridPoint]

theorem exp_6_365_0 : expNegUpper (323017331931910312681067 / 3319652031913783808000 : ℝ) ≤ (551561384553621829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1069343 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_365_1 : expNegUpper (161693090911254501878353 / 1659826015956891904000 : ℝ) ≤ (246779431183721857 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (33446 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_365 : rowCell 6 365 ≤ (76211107380705943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (551561384553621829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (246779431183721857 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_365_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_365_1
  · norm_num [gridPoint]

theorem exp_6_366_0 : expNegUpper (162293427407357155733057 / 1665988641486366976000 : ℝ) ≤ (493558832993962341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (33446 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_366_1 : expNegUpper (64991500448414875065461 / 666395456594546790400 : ℝ) ≤ (441599156760430393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (428481 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_366 : rowCell 6 366 ≤ (68192560793896739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (493558832993962341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (441599156760430393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_366_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_366_1
  · norm_num [gridPoint]

theorem exp_6_367_0 : expNegUpper (65232354727716395503501 / 668865074467487846400 : ℝ) ≤ (220799565336576899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (428481 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_367_1 : expNegUpper (20408388870842685192121 / 209020335771089952000 : ℝ) ≤ (19752953219590719 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2144269 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_367 : rowCell 6 367 ≤ (61009867269234609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (220799565336576899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19752953219590719 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_367_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_367_1
  · norm_num [gridPoint]

theorem exp_6_368_0 : expNegUpper (20483881149740747347769 / 209793518750493728000 : ℝ) ≤ (79011808245147211 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2144269 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_368_1 : expNegUpper (328116350889073413725663 / 3356696300007899648000 : ℝ) ≤ (353378926890990269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1073069 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_368 : rowCell 6 368 ≤ (6822096132476083 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (79011808245147211 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (353378926890990269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_368_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_368_1
  · norm_num [gridPoint]

theorem exp_6_369_0 : expNegUpper (13173113563154515933423 / 134763602639364608000 : ℝ) ≤ (88344726580333437 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1073069 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_369_1 : expNegUpper (6594077982023687480231 / 67381801319682304000 : ℝ) ≤ (316056255190903541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (214801 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_369 : rowCell 6 369 ≤ (9763162684625053 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (88344726580333437 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (316056255190903541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_369_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_369_1
  · norm_num [gridPoint]

theorem exp_6_370_0 : expNegUpper (165459502839976723280191 / 1690753335133042944000 : ℝ) ≤ (79014059232181257 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (214801 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_370_1 : expNegUpper (331296876562154490660661 / 3381506670266085888000 : ℝ) ≤ (282639958382479567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1074943 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_370 : rowCell 6 370 ≤ (21828732226603007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (79014059232181257 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (282639958382479567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_370_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_370_1
  · norm_num [gridPoint]

theorem exp_6_371_0 : expNegUpper (332515608191462248967789 / 3393946112853811712000 : ℝ) ≤ (17664996385671683 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1074943 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_371_1 : expNegUpper (16644764663216120520103 / 169697305642690585600 : ℝ) ≤ (252725147640509597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1075883 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_371 : rowCell 6 371 ≤ (4879912917638713 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17664996385671683 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (252725147640509597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_371_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_371_1
  · norm_num [gridPoint]

theorem exp_6_372_0 : expNegUpper (879256991067705137597 / 8964232615124454400 : ℝ) ≤ (2021801066004853 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1075883 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_372_1 : expNegUpper (17605218905264567366569 / 179284652302489088000 : ℝ) ≤ (225948458733635887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (43073 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_372 : rowCell 6 372 ≤ (34905308385796263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2021801066004853 / 8000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (225948458733635887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_372_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_372_1
  · norm_num [gridPoint]

theorem exp_6_373_0 : expNegUpper (335725160915089203246659 / 3418893512946528768000 : ℝ) ≤ (225948445962246147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (43073 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_373_1 : expNegUpper (168054242180803123038989 / 1709446756473264384000 : ℝ) ≤ (100991921045832849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2155537 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_373 : rowCell 6 373 ≤ (31205206915306301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (225948445962246147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (100991921045832849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_373_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_373_1
  · norm_num [gridPoint]

theorem exp_6_374_0 : expNegUpper (269870504889507718861 / 2745121176361216000 : ℝ) ≤ (201983830757995119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2155537 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_374_1 : expNegUpper (540357245986239128753 / 5490242352722432000 : ℝ) ≤ (90269387172785521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (539357 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_374 : rowCell 6 374 ≤ (6973473009201267 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (201983830757995119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (90269387172785521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_374_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_374_1
  · norm_num [gridPoint]

theorem exp_6_375_0 : expNegUpper (338956577188452935004697 / 3443932266262266368000 : ℝ) ≤ (180538764288872799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (539357 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_375_1 : expNegUpper (42417944041468131858977 / 430491533282783296000 : ℝ) ≤ (3227016994548499 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2159323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_375 : rowCell 6 375 ≤ (997235912820741 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (180538764288872799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3227016994548499 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_375_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_375_1
  · norm_num [gridPoint]

theorem exp_6_376_0 : expNegUpper (42572563642141588657633 / 432060737547345984000 : ℝ) ≤ (161350840804794017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2159323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_376_1 : expNegUpper (68193863024996338202123 / 691297180075753574400 : ℝ) ≤ (144184713763031717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2161221 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_376 : rowCell 6 376 ≤ (1113996357184283 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (161350840804794017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (144184713763031717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_376_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_376_1
  · norm_num [gridPoint]

theorem exp_6_377_0 : expNegUpper (68441987390052523614883 / 693812474560204902400 : ℝ) ≤ (1802308823093 / 12500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2161221 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_377_1 : expNegUpper (171300288556724005308043 / 1734531186400512256000 : ℝ) ≤ (128829305348980357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2163123 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_377 : rowCell 6 377 ≤ (19908426982468657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1802308823093 / 12500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (128829305348980357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_377_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_377_1
  · norm_num [gridPoint]

theorem exp_6_378_0 : expNegUpper (171922435310090654086907 / 1740830841764518144000 : ℝ) ≤ (25765859665505279 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2163123 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_378_1 : expNegUpper (344237348289482660417293 / 3481661683529036288000 : ℝ) ≤ (115095376614499367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2165029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_378 : rowCell 6 378 ≤ (8893603223923831 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25765859665505279 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (115095376614499367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_378_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_378_1
  · norm_num [gridPoint]

theorem exp_6_379_0 : expNegUpper (13819412805569097051533 / 139771353302512128000 : ℝ) ≤ (14386921298356173 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2165029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_379_1 : expNegUpper (3458796386454242871433 / 34942838325628032000 : ℝ) ≤ (102813262959712771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2166939 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_379 : rowCell 6 379 ≤ (3178018664183817 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14386921298356173 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (102813262959712771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_379_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_379_1
  · norm_num [gridPoint]

theorem exp_6_380_0 : expNegUpper (86782823874934904786753 / 876732204975581312000 : ℝ) ≤ (51406628718356173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2166939 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_380_1 : expNegUpper (347527458173611537523171 / 3506928819902325248000 : ℝ) ≤ (4591543918278357 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (542213 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_380 : rowCell 6 380 ≤ (709681262914649 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (51406628718356173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4591543918278357 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_380_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_380_1
  · norm_num [gridPoint]

theorem exp_6_381_0 : expNegUpper (348782806694056533478939 / 3519596645547602432000 : ℝ) ≤ (18366174693600997 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (542213 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_381_1 : expNegUpper (34918081686638305828597 / 351959664554760243200 : ℝ) ≤ (8201191351394163 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2170769 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_381 : rowCell 6 381 ≤ (12676772213602477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18366174693600997 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8201191351394163 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_381_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_381_1
  · norm_num [gridPoint]

theorem exp_6_382_0 : expNegUpper (35043986371451681601317 / 353228730949863475200 : ℝ) ≤ (10251488646431121 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2170769 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_382_1 : expNegUpper (350839724716077496160761 / 3532287309498634752000 : ℝ) ≤ (73234216463888869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (217269 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_382 : rowCell 6 382 ≤ (2830171740067459 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10251488646431121 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (73234216463888869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_382_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_382_1
  · norm_num [gridPoint]

theorem exp_6_383_0 : expNegUpper (352102476553459113478769 / 3545000811755422208000 : ℝ) ≤ (73234212613959661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (217269 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_383_1 : expNegUpper (2753938997773699202161 / 27695318841839236000 : ℝ) ≤ (65388337623926267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1087307 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_383 : rowCell 6 383 ≤ (5054240453522061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (73234212613959661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (65388337623926267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_383_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_383_1
  · norm_num [gridPoint]

theorem sum_6_352_2 : blockSum (rowCell 6) 352 2 ≤ (121174732819666411 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_352) (by simpa only [blockSum_one] using cell_6_353) (by norm_num)

theorem sum_6_354_2 : blockSum (rowCell 6) 354 2 ≤ (97328096126017723 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_354) (by simpa only [blockSum_one] using cell_6_355) (by norm_num)

theorem sum_6_352_4 : blockSum (rowCell 6) 352 4 ≤ (109251414472842067 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_352_2 sum_6_354_2 (by norm_num)

theorem sum_6_356_2 : blockSum (rowCell 6) 356 2 ≤ (195329091737074633 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_356) (by simpa only [blockSum_one] using cell_6_357) (by norm_num)

theorem sum_6_358_2 : blockSum (rowCell 6) 358 2 ≤ (7835935278827499 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_358) (by simpa only [blockSum_one] using cell_6_359) (by norm_num)

theorem sum_6_356_4 : blockSum (rowCell 6) 356 4 ≤ (352047797313624613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_356_2 sum_6_358_2 (by norm_num)

theorem sum_6_352_8 : blockSum (rowCell 6) 352 8 ≤ (224576217419458737 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_352_4 sum_6_356_4 (by norm_num)

theorem sum_6_360_2 : blockSum (rowCell 6) 360 2 ≤ (50269270006907591 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_360) (by simpa only [blockSum_one] using cell_6_361) (by norm_num)

theorem sum_6_362_2 : blockSum (rowCell 6) 362 2 ≤ (201448842220528647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_362) (by simpa only [blockSum_one] using cell_6_363) (by norm_num)

theorem sum_6_360_4 : blockSum (rowCell 6) 360 4 ≤ (226397596127533301 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_360_2 sum_6_362_2 (by norm_num)

theorem sum_6_364_2 : blockSum (rowCell 6) 364 2 ≤ (40343165840439533 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_364) (by simpa only [blockSum_one] using cell_6_365) (by norm_num)

theorem sum_6_366_2 : blockSum (rowCell 6) 366 2 ≤ (32300607015782837 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_366) (by simpa only [blockSum_one] using cell_6_367) (by norm_num)

theorem sum_6_364_4 : blockSum (rowCell 6) 364 4 ≤ (7264377285622237 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_364_2 sum_6_366_2 (by norm_num)

theorem sum_6_360_8 : blockSum (rowCell 6) 360 8 ≤ (371685141839978041 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_360_4 sum_6_364_4 (by norm_num)

theorem sum_6_352_16 : blockSum (rowCell 6) 352 16 ≤ (1269990011517812989 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_352_8 sum_6_360_8 (by norm_num)

theorem sum_6_368_2 : blockSum (rowCell 6) 368 2 ≤ (103392582482933929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_368) (by simpa only [blockSum_one] using cell_6_369) (by norm_num)

theorem sum_6_370_2 : blockSum (rowCell 6) 370 2 ≤ (41348383897157859 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_370) (by simpa only [blockSum_one] using cell_6_371) (by norm_num)

theorem sum_6_368_4 : blockSum (rowCell 6) 368 4 ≤ (186089350277249647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_368_2 sum_6_370_2 (by norm_num)

theorem sum_6_372_2 : blockSum (rowCell 6) 372 2 ≤ (16527628825275641 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_372) (by simpa only [blockSum_one] using cell_6_373) (by norm_num)

theorem sum_6_374_2 : blockSum (rowCell 6) 374 2 ≤ (52824789857323593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_374) (by simpa only [blockSum_one] using cell_6_375) (by norm_num)

theorem sum_6_372_4 : blockSum (rowCell 6) 372 4 ≤ (118935305158426157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_372_2 sum_6_374_2 (by norm_num)

theorem sum_6_368_8 : blockSum (rowCell 6) 368 8 ≤ (76256163858918951 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_368_4 sum_6_372_4 (by norm_num)

theorem sum_6_376_2 : blockSum (rowCell 6) 376 2 ≤ (42188354126154317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_376) (by simpa only [blockSum_one] using cell_6_377) (by norm_num)

theorem sum_6_378_2 : blockSum (rowCell 6) 378 2 ≤ (33677299768766747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_378) (by simpa only [blockSum_one] using cell_6_379) (by norm_num)

theorem sum_6_376_4 : blockSum (rowCell 6) 376 4 ≤ (9483206736865133 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_376_2 sum_6_378_2 (by norm_num)

theorem sum_6_380_2 : blockSum (rowCell 6) 380 2 ≤ (26870397471895457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_380) (by simpa only [blockSum_one] using cell_6_381) (by norm_num)

theorem sum_6_382_2 : blockSum (rowCell 6) 382 2 ≤ (10714583933656979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_382) (by simpa only [blockSum_one] using cell_6_383) (by norm_num)

theorem sum_6_380_4 : blockSum (rowCell 6) 380 4 ≤ (9659913067841883 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_380_2 sum_6_382_2 (by norm_num)

theorem sum_6_376_8 : blockSum (rowCell 6) 376 8 ≤ (124165219234130479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_376_4 sum_6_380_4 (by norm_num)

theorem sum_6_368_16 : blockSum (rowCell 6) 368 16 ≤ (429189874669806283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_368_8 sum_6_376_8 (by norm_num)

theorem sum_6_352_32 : blockSum (rowCell 6) 352 32 ≤ (2969169897705432261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_352_16 sum_6_368_16 (by norm_num)

#print axioms sum_6_352_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
