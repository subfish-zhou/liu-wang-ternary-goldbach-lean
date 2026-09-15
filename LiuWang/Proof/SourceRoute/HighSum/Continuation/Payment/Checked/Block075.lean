import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_352_0 : expNegUpper (1882390416973862274929 / 19759387837319683200 : ℝ) ≤ (4237396990924752709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (263111 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_352_1 : expNegUpper (301531892596617823633711 / 3161502053971149312000 : ℝ) ≤ (1897005725081578813 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2106707 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_352 : rowCell 4 352 ≤ (9150898738166433 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4237396990924752709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1897005725081578813 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_352_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_352_1
  · norm_num [gridPoint]

theorem exp_4_353_0 : expNegUpper (302679110800451076656039 / 3173530407055282688000 : ℝ) ≤ (189700560454807163 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2106707 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_353_1 : expNegUpper (151515145458939086630359 / 1586765203527641344000 : ℝ) ≤ (339656523097418633 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2108529 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_353 : rowCell 4 353 ≤ (52434329429344881 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (189700560454807163 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (339656523097418633 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_353_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_353_1
  · norm_num [gridPoint]

theorem exp_4_354_0 : expNegUpper (6083620418514908982239 / 63711631968903424000 : ℝ) ≤ (3396565016791754147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2108529 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_354_1 : expNegUpper (12181358344423173263437 / 127423263937806848000 : ℝ) ≤ (3040349278642137957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422071 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_354 : rowCell 4 354 ≤ (469385573588226717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3396565016791754147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3040349278642137957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_354_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_354_1
  · norm_num [gridPoint]

theorem exp_4_355_0 : expNegUpper (13290791612349553395019 / 139028505571339776000 : ℝ) ≤ (190021818023039009 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422071 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_355_1 : expNegUpper (3326553322468042884113 / 34757126392834944000 : ℝ) ≤ (1360565725154051193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (264023 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_355 : rowCell 4 355 ≤ (210066168605239183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (190021818023039009 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1360565725154051193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_355_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_355_1
  · norm_num [gridPoint]

theorem exp_4_356_0 : expNegUpper (76800169816918140076391 / 802438124035553408000 : ℝ) ≤ (108845251251781371 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (264023 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_356_1 : expNegUpper (61511428415931732249439 / 641950499228442726400 : ℝ) ≤ (304388630732397487 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1057009 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_356 : rowCell 4 356 ≤ (75199535443143553 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (108845251251781371 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (304388630732397487 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_356_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_356_1
  · norm_num [gridPoint]

theorem exp_4_357_0 : expNegUpper (61743689493796518500279 / 644374440489873510400 : ℝ) ≤ (1217554447873860923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1057009 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_357_1 : expNegUpper (154538338920357063020693 / 1610936101224683776000 : ℝ) ≤ (2178865777241812003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (423171 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_357 : rowCell 4 357 ≤ (336455178522267073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1217554447873860923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2178865777241812003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_357_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_357_1
  · norm_num [gridPoint]

theorem exp_4_358_0 : expNegUpper (155120760840154235700997 / 1617007373531138304000 : ℝ) ≤ (2178865643934044199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (423171 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_358_1 : expNegUpper (310601522942564986450033 / 3234014747062276608000 : ℝ) ≤ (97466649502727107 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (33089 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_358 : rowCell 4 358 ≤ (15051597665945397 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2178865643934044199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (97466649502727107 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_358_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_358_1
  · norm_num [gridPoint]

theorem exp_4_359_0 : expNegUpper (12470796475759553749457 / 129847205199237632000 : ℝ) ≤ (30458326120049427 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (33089 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_359_1 : expNegUpper (1560658436887749446011 / 16230900649904704000 : ℝ) ≤ (348750944728128191 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (105977 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_359 : rowCell 4 359 ≤ (269303265459398233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30458326120049427 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (348750944728128191 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_359_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_359_1
  · norm_num [gridPoint]

theorem exp_4_360_0 : expNegUpper (1263321081057912726749 / 13138582061311936000 : ℝ) ≤ (1743754618544229303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (105977 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_360_1 : expNegUpper (10118296165742176807321 / 105108656490495488000 : ℝ) ≤ (1559656235474974753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2121389 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_360 : rowCell 4 360 ≤ (120443843691634759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1743754618544229303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1559656235474974753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_360_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_360_1
  · norm_num [gridPoint]

theorem exp_4_361_0 : expNegUpper (314842680297767655623039 / 3270579410735534592000 : ℝ) ≤ (311931228435095929 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2121389 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_361_1 : expNegUpper (6304160284325528173067 / 65411588214710691840 : ℝ) ≤ (278963130300408387 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2123241 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_361 : rowCell 4 361 ≤ (107721368801608503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (311931228435095929 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (278963130300408387 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_361_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_361_1
  · norm_num [gridPoint]

theorem exp_4_362_0 : expNegUpper (6327741569450867772667 / 65656266171429283840 : ℝ) ≤ (278963113736942833 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2123241 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_362_1 : expNegUpper (316754196604695318810461 / 3282813308571464192000 : ℝ) ≤ (311809609143390707 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2125097 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_362 : rowCell 4 362 ≤ (48165237945957227 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (278963113736942833 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (311809609143390707 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_362_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_362_1
  · norm_num [gridPoint]

theorem exp_4_363_0 : expNegUpper (317936832619028201993749 / 3295070044713148928000 : ℝ) ≤ (1247238363069061623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2125097 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_363_1 : expNegUpper (79576434573900714556837 / 823767511178287232000 : ℝ) ≤ (1115134408564302829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (531739 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_363 : rowCell 4 363 ≤ (172266344951791951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1247238363069061623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1115134408564302829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_363_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_363_1
  · norm_num [gridPoint]

theorem exp_4_364_0 : expNegUpper (3194919527295607424333 / 33073496191605888000 : ℝ) ≤ (557567171666372953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (531739 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_364_1 : expNegUpper (12794505971253506945323 / 132293984766423552000 : ℝ) ≤ (199379409279218979 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2128819 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_364 : rowCell 4 364 ≤ (154011226467228781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (557567171666372953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (199379409279218979 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_364_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_364_1
  · norm_num [gridPoint]

theorem exp_4_365_0 : expNegUpper (321052448796479656681067 / 3319652031913783808000 : ℝ) ≤ (498448494256421297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2128819 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_365_1 : expNegUpper (160712469777119205878353 / 1659826015956891904000 : ℝ) ≤ (44554243316455579 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1065343 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_365 : rowCell 4 365 ≤ (8604583318048313 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (498448494256421297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44554243316455579 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_365_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_365_1
  · norm_num [gridPoint]

theorem exp_4_366_0 : expNegUpper (161309165406061795733057 / 1665988641486366976000 : ℝ) ≤ (445542407486049181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1065343 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_366_1 : expNegUpper (64598523821328743865461 / 666395456594546790400 : ℝ) ≤ (398202331359991801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2132557 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_366 : rowCell 4 366 ≤ (123053248817134231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (445542407486049181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (398202331359991801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_366_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_366_1
  · norm_num [gridPoint]

theorem exp_4_367_0 : expNegUpper (64837921753766238703501 / 668865074467487846400 : ℝ) ≤ (796404617158430071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2132557 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_367_1 : expNegUpper (20285356120680765192121 / 209020335771089952000 : ℝ) ≤ (355848214605458943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (66701 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_367 : rowCell 4 367 ≤ (109972083235786701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (796404617158430071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (355848214605458943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_367_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_367_1
  · norm_num [gridPoint]

theorem exp_4_368_0 : expNegUpper (20360393291183819347769 / 209793518750493728000 : ℝ) ≤ (177924097198818579 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (66701 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_368_1 : expNegUpper (326144186019322629725663 / 3356696300007899648000 : ℝ) ≤ (635919794195815261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (213631 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_368 : rowCell 4 368 ≤ (98269382812624659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (177924097198818579 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (635919794195815261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_368_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_368_1
  · norm_num [gridPoint]

theorem exp_4_369_0 : expNegUpper (13093935698991679453423 / 134763602639364608000 : ℝ) ≤ (158979939587200881 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (213631 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_369_1 : expNegUpper (6554561867285470520231 / 67381801319682304000 : ℝ) ≤ (35508863786515003 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2138191 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_369 : rowCell 4 369 ≤ (2195031302746809 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (158979939587200881 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35508863786515003 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_369_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_369_1
  · norm_num [gridPoint]

theorem exp_4_370_0 : expNegUpper (164467959104361235280191 / 1690753335133042944000 : ℝ) ≤ (284070894396437543 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2138191 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_370_1 : expNegUpper (329317429958083578660661 / 3381506670266085888000 : ℝ) ≤ (20301041380465931 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2140077 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_370 : rowCell 4 370 ≤ (19609666023918961 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (284070894396437543 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20301041380465931 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_370_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_370_1
  · norm_num [gridPoint]

theorem exp_4_371_0 : expNegUpper (330528879853071208967789 / 3393946112853811712000 : ℝ) ≤ (20301040252805319 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2140077 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_371_1 : expNegUpper (16545610289654571720103 / 169697305642690585600 : ℝ) ≤ (45332256086963917 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1070983 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_371 : rowCell 4 371 ≤ (7006594078186277 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20301040252805319 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45332256086963917 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_371_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_371_1
  · norm_num [gridPoint]

theorem exp_4_372_0 : expNegUpper (16606364370008842414343 / 170320419687364633600 : ℝ) ≤ (453322535873037907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1070983 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_372_1 : expNegUpper (332512430861635739964811 / 3406408393747292672000 : ℝ) ≤ (80971851096991737 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2143859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_372 : rowCell 4 372 ≤ (12515877449705657 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (453322535873037907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (80971851096991737 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_372_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_372_1
  · norm_num [gridPoint]

theorem exp_4_373_0 : expNegUpper (333731150842378035246659 / 3418893512946528768000 : ℝ) ≤ (101214808330891239 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2143859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_373_1 : expNegUpper (167059057578027571038989 / 1709446756473264384000 : ℝ) ≤ (180766867290122187 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (536439 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_373 : rowCell 4 373 ≤ (27943031887863939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (101214808330891239 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (180766867290122187 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_373_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_373_1
  · norm_num [gridPoint]

theorem exp_4_374_0 : expNegUpper (268272384137610733261 / 2745121176361216000 : ℝ) ≤ (180766857467283533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (536439 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_374_1 : expNegUpper (537166829869901259953 / 5490242352722432000 : ℝ) ≤ (32280621191172059 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (268457 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_374 : rowCell 4 374 ≤ (24951341151142161 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (180766857467283533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32280621191172059 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_374_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_374_1
  · norm_num [gridPoint]

theorem exp_4_375_0 : expNegUpper (336955285381421639004697 / 3443932266262266368000 : ℝ) ≤ (322806194498021513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (268457 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_375_1 : expNegUpper (42168237673984227858977 / 430491533282783296000 : ℝ) ≤ (18012066424865967 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (53739 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_375 : rowCell 4 375 ≤ (44554614786660577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (322806194498021513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18012066424865967 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_375_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_375_1
  · norm_num [gridPoint]

theorem exp_4_376_0 : expNegUpper (42321947057867668657633 / 432060737547345984000 : ℝ) ≤ (288193047364178089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (53739 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_376_1 : expNegUpper (67793604663590079002123 / 691297180075753574400 : ℝ) ≤ (64315260554466609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2151467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_376 : rowCell 4 376 ≤ (1242968820897853 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (288193047364178089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64315260554466609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_376_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_376_1
  · norm_num [gridPoint]

theorem exp_4_377_0 : expNegUpper (68040272681782238814883 / 693812474560204902400 : ℝ) ≤ (257261028540502189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2151467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_377_1 : expNegUpper (170297822219628325308043 / 1734531186400512256000 : ℝ) ≤ (229622091351088857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1076689 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_377 : rowCell 4 377 ≤ (35503954536547847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (257261028540502189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (229622091351088857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_377_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_377_1
  · norm_num [gridPoint]

theorem exp_4_378_0 : expNegUpper (7431144700253691742909 / 75688297468022528000 : ℝ) ≤ (114811039615716639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1076689 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_378_1 : expNegUpper (14879511945570923322491 / 151376594936045056000 : ℝ) ≤ (40985734684245331 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2155293 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_378 : rowCell 4 378 ≤ (31687831300123799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (114811039615716639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40985734684245331 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_378_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_378_1
  · norm_num [gridPoint]

theorem exp_4_379_0 : expNegUpper (13738778594542234971533 / 139771353302512128000 : ℝ) ≤ (204928662682982647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2155293 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_379_1 : expNegUpper (3438674242369127991433 / 34942838325628032000 : ℝ) ≤ (91434792785068191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (539303 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_379 : rowCell 4 379 ≤ (5655719335021221 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (204928662682982647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (91434792785068191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_379_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_379_1
  · norm_num [gridPoint]

theorem exp_4_380_0 : expNegUpper (86277949839227000786753 / 876732204975581312000 : ℝ) ≤ (36573915211365327 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (539303 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_380_1 : expNegUpper (345511602897939985523171 / 3506928819902325248000 : ℝ) ≤ (40791549693641577 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1079567 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_380 : rowCell 4 380 ≤ (3154154949027703 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36573915211365327 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40791549693641577 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_380_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_380_1
  · norm_num [gridPoint]

theorem exp_4_381_0 : expNegUpper (346759669684064853478939 / 3519596645547602432000 : ℝ) ≤ (163166190347320989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1079567 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_381_1 : expNegUpper (34716132072355144228597 / 351959664554760243200 : ℝ) ≤ (36392270647753311 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108053 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_381 : rowCell 4 381 ≤ (22513253482010113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (163166190347320989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36392270647753311 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_381_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_381_1
  · norm_num [gridPoint]

theorem exp_4_382_0 : expNegUpper (34841308583736507201317 / 353228730949863475200 : ℝ) ≤ (9098067195412671 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108053 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_382_1 : expNegUpper (348816587706085816160761 / 3532287309498634752000 : ℝ) ≤ (129854975818252121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2162989 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_382 : rowCell 4 382 ≤ (20084169246194587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9098067195412671 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (129854975818252121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_382_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_382_1
  · norm_num [gridPoint]

theorem exp_4_383_0 : expNegUpper (350072057809147305478769 / 3545000811755422208000 : ℝ) ≤ (129854969207337893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2162989 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_383_1 : expNegUpper (2738104795608451202161 / 27695318841839236000 : ℝ) ≤ (115824068049135757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2164923 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_383 : rowCell 4 383 ≤ (8957568062001047 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (129854969207337893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (115824068049135757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_383_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_383_1
  · norm_num [gridPoint]

theorem sum_4_352_2 : blockSum (rowCell 4) 352 2 ≤ (555000406768050261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_352) (by simpa only [blockSum_one] using cell_4_353) (by norm_num)

theorem sum_4_354_2 : blockSum (rowCell 4) 354 2 ≤ (889517910798705083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_354) (by simpa only [blockSum_one] using cell_4_355) (by norm_num)

theorem sum_4_352_4 : blockSum (rowCell 4) 352 4 ≤ (399903744866961121 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_352_2 sum_4_354_2 (by norm_num)

theorem sum_4_356_2 : blockSum (rowCell 4) 356 2 ≤ (356226427868992419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_356) (by simpa only [blockSum_one] using cell_4_357) (by norm_num)

theorem sum_4_358_2 : blockSum (rowCell 4) 358 2 ≤ (570335218778306173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_358) (by simpa only [blockSum_one] using cell_4_359) (by norm_num)

theorem sum_4_356_4 : blockSum (rowCell 4) 356 4 ≤ (1282788074516291011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_356_2 sum_4_358_2 (by norm_num)

theorem sum_4_352_8 : blockSum (rowCell 4) 352 8 ≤ (410288349856387077 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_352_4 sum_4_356_4 (by norm_num)

theorem sum_4_360_2 : blockSum (rowCell 4) 360 2 ≤ (114082606246621631 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_360) (by simpa only [blockSum_one] using cell_4_361) (by norm_num)

theorem sum_4_362_2 : blockSum (rowCell 4) 362 2 ≤ (364927296735620859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_362) (by simpa only [blockSum_one] using cell_4_363) (by norm_num)

theorem sum_4_360_4 : blockSum (rowCell 4) 360 4 ≤ (821257721722107383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_360_2 sum_4_362_2 (by norm_num)

theorem sum_4_364_2 : blockSum (rowCell 4) 364 2 ≤ (291684559556001789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_364) (by simpa only [blockSum_one] using cell_4_365) (by norm_num)

theorem sum_4_366_2 : blockSum (rowCell 4) 366 2 ≤ (58256333013230233 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_366) (by simpa only [blockSum_one] using cell_4_367) (by norm_num)

theorem sum_4_364_4 : blockSum (rowCell 4) 364 4 ≤ (524709891608922721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_364_2 sum_4_366_2 (by norm_num)

theorem sum_4_360_8 : blockSum (rowCell 4) 360 8 ≤ (168245951666378763 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_360_4 sum_4_364_4 (by norm_num)

theorem sum_4_352_16 : blockSum (rowCell 4) 352 16 ≤ (7231678769034573 / 1562500000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_352_8 sum_4_360_8 (by norm_num)

theorem sum_4_368_2 : blockSum (rowCell 4) 368 2 ≤ (186070634922497019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_368) (by simpa only [blockSum_one] using cell_4_369) (by norm_num)

theorem sum_4_370_2 : blockSum (rowCell 4) 370 2 ≤ (74252302438769307 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_370) (by simpa only [blockSum_one] using cell_4_371) (by norm_num)

theorem sum_4_368_4 : blockSum (rowCell 4) 368 4 ≤ (334575239800035633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_368_2 sum_4_370_2 (by norm_num)

theorem sum_4_372_2 : blockSum (rowCell 4) 372 2 ≤ (118465451024256163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_372) (by simpa only [blockSum_one] using cell_4_373) (by norm_num)

theorem sum_4_374_2 : blockSum (rowCell 4) 374 2 ≤ (94457297088944899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_374) (by simpa only [blockSum_one] using cell_4_375) (by norm_num)

theorem sum_4_372_4 : blockSum (rowCell 4) 372 4 ≤ (106461374056600531 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_372_2 sum_4_374_2 (by norm_num)

theorem sum_4_368_8 : blockSum (rowCell 4) 368 8 ≤ (109499597582647339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_368_4 sum_4_372_4 (by norm_num)

theorem sum_4_376_2 : blockSum (rowCell 4) 376 2 ≤ (75278956805279143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_376) (by simpa only [blockSum_one] using cell_4_377) (by norm_num)

theorem sum_4_378_2 : blockSum (rowCell 4) 378 2 ≤ (3747901748451869 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_378) (by simpa only [blockSum_one] using cell_4_379) (by norm_num)

theorem sum_4_376_4 : blockSum (rowCell 4) 376 4 ≤ (135245384780509047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_376_2 sum_4_378_2 (by norm_num)

theorem sum_4_380_2 : blockSum (rowCell 4) 380 2 ≤ (47746493074231737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_380) (by simpa only [blockSum_one] using cell_4_381) (by norm_num)

theorem sum_4_382_2 : blockSum (rowCell 4) 382 2 ≤ (37999305370196681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_382) (by simpa only [blockSum_one] using cell_4_383) (by norm_num)

theorem sum_4_380_4 : blockSum (rowCell 4) 380 4 ≤ (42872899222214209 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_380_2 sum_4_382_2 (by norm_num)

theorem sum_4_376_8 : blockSum (rowCell 4) 376 8 ≤ (44198236644987493 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_376_4 sum_4_380_4 (by norm_num)

theorem sum_4_368_16 : blockSum (rowCell 4) 368 16 ≤ (9606114639227177 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_368_8 sum_4_376_8 (by norm_num)

theorem sum_4_352_32 : blockSum (rowCell 4) 352 32 ≤ (67459544791503761 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_352_16 sum_4_368_16 (by norm_num)

#print axioms sum_4_352_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
