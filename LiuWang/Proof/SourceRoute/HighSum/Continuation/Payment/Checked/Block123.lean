import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_352_0 : (1933867297683900059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (948924494685428004369 / 9879684997446656000 : ℝ) := by
  apply lower_of_taylor (t := (423559 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_352 : (28203868161202051 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 352 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1933867297683900059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_352_0
  · norm_num [gridPoint]

theorem exp_7_353_0 : (2709044647756769 / 1562500000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (76289432031632081432893 / 793381888066765824000 : ℝ) := by
  apply lower_of_taylor (t := (2119603 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_353 : (126429420557903561 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 353 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2709044647756769 / 1562500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_353_0
  · norm_num [gridPoint]

theorem exp_7_354_0 : (1554194497549806469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (15333244282988536215421 / 159278937182847590400 : ℝ) := by
  apply lower_of_taylor (t := (424283 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_354 : (5666662955397539 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 354 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1554194497549806469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_354_0
  · norm_num [gridPoint]

theorem exp_7_355_0 : (1393011500864918469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (38522165111425350482211 / 399706596669074432000 : ℝ) := by
  apply lower_of_taylor (t := (212323 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_355 : (101579650176840163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 355 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1393011500864918469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_355_0
  · norm_num [gridPoint]

theorem exp_7_356_0 : (1997397321541339 / 1600000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7742376095344080277711 / 80243741033849856000 : ℝ) := by
  apply lower_of_taylor (t := (2125049 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_356 : (9103250451465657 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 356 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1997397321541339 / 1600000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_356_0
  · norm_num [gridPoint]

theorem exp_7_357_0 : (559300288320137547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (15560903220959529639487 / 161093467383057408000 : ℝ) := by
  apply lower_of_taylor (t := (265859 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_357 : (16313871808262887 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 357 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (559300288320137547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_357_0
  · norm_num [gridPoint]

theorem exp_7_358_0 : (501091130105819601 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (78186598175005898907663 / 808502973068514304000 : ℝ) := by
  apply lower_of_taylor (t := (2128699 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_358 : (146160061625514279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 358 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (501091130105819601 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_358_0
  · norm_num [gridPoint]

theorem exp_7_359_0 : (448879562528310159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3928500483107510829503 / 40577215939909017600 : ℝ) := by
  apply lower_of_taylor (t := (213053 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_359 : (130930803959185343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 359 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (448879562528310159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_359_0
  · norm_num [gridPoint]

theorem exp_7_360_0 : (100513577824815167 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (19738688266078815731723 / 203647843526071296000 : ℝ) := by
  apply lower_of_taylor (t := (533091 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_360 : (117272646402449583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 360 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (100513577824815167 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_360_0
  · norm_num [gridPoint]

theorem exp_7_361_0 : (720131337946463867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3173633235183427984017 / 32705765559473152000 : ℝ) := by
  apply lower_of_taylor (t := (2134203 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_361 : (52512624156055081 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 361 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (720131337946463867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_361_0
  · norm_num [gridPoint]

theorem exp_7_362_0 : (644838748084052507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3189129824241847531717 / 32828104537832448000 : ℝ) := by
  apply lower_of_taylor (t := (427209 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_362 : (94044441715203681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 362 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (644838748084052507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_362_0
  · norm_num [gridPoint]

theorem exp_7_363_0 : (288671089901588829 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (40058499870890695343329 / 411883398740616192000 : ℝ) := by
  apply lower_of_taylor (t := (2137891 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_363 : (84200620914224763 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 363 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (288671089901588829 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_363_0
  · norm_num [gridPoint]

theorem exp_7_364_0 : (129210712915856579 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8050709578487596846389 / 82683669109309235200 : ℝ) := by
  apply lower_of_taylor (t := (106987 / 50000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_364 : (9422161273574147 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 364 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (129210712915856579 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_364_0
  · norm_num [gridPoint]

theorem exp_7_365_0 : (57827861902617523 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (80898536233414583306887 / 829912294281391104000 : ℝ) := by
  apply lower_of_taylor (t := (1070797 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_365 : (33734877157268383 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 365 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (57827861902617523 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_365_0
  · norm_num [gridPoint]

theorem exp_7_366_0 : (207018630358095673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (16258264717096379379583 / 166598721409225728000 : ℝ) := by
  apply lower_of_taylor (t := (2143451 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_366 : (12076787615210439 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 366 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (207018630358095673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_366_0
  · norm_num [gridPoint]

theorem exp_7_367_0 : (185253210715160459 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2042136508479064272981 / 20902015734682624000 : ℝ) := by
  apply lower_of_taylor (t := (67041 / 31250 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_367 : (5403532225512401 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 367 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (185253210715160459 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_367_0
  · norm_num [gridPoint]

theorem exp_7_368_0 : (82877449774637311 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (10260118624067658381641 / 104896670163115008000 : ℝ) := by
  apply lower_of_taylor (t := (2147177 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_368 : (12086996195550669 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 368 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (82877449774637311 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_368_0
  · norm_num [gridPoint]

theorem exp_7_369_0 : (59315968036683087 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (16495558408740529396369 / 168454360559794790400 : ℝ) := by
  apply lower_of_taylor (t := (429809 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_369 : (10813434202312409 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 369 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (59315968036683087 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_369_0
  · norm_num [gridPoint]

theorem exp_7_370_0 : (265296679530130217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (82875991990731372387657 / 845375953869466624000 : ℝ) := by
  apply lower_of_taylor (t := (1075459 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_370 : (38691344447645221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 370 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (265296679530130217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_370_0
  · norm_num [gridPoint]

theorem exp_7_371_0 : (29660416751849619 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8327555133171210495283 / 84848581451639808000 : ℝ) := by
  apply lower_of_taylor (t := (1076397 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_371 : (6921165560241759 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 371 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (29660416751849619 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_371_0
  · norm_num [gridPoint]

theorem exp_7_372_0 : (53050343577913461 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8367647256472950635963 / 85160138473976832000 : ℝ) := by
  apply lower_of_taylor (t := (1077337 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_372 : (15473914864478031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 372 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (53050343577913461 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_372_0
  · norm_num [gridPoint]

theorem exp_7_373_0 : (37949405580120943 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (84078758187868238290323 / 854722664539577344000 : ℝ) := by
  apply lower_of_taylor (t := (2156557 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_373 : (553460950014299 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 373 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (37949405580120943 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_373_0
  · norm_num [gridPoint]

theorem exp_7_374_0 : (42411917739795753 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3379296427968518497087 / 34313986156633006080 : ℝ) := by
  apply lower_of_taylor (t := (539611 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_374 : (4948344233669201 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 374 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (42411917739795753 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_374_0
  · norm_num [gridPoint]

theorem exp_7_375_0 : (37914667719363047 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (684576069329422100423 / 6943406071520256000 : ℝ) := by
  apply lower_of_taylor (t := (432067 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_375 : (1105908653622093 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 375 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (37914667719363047 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_375_0
  · norm_num [gridPoint]

theorem exp_7_376_0 : (135560544839953299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (137570687707837151691 / 1393743163544576000 : ℝ) := by
  apply lower_of_taylor (t := (216223 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_376 : (9885196722406399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 376 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (135560544839953299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_376_0
  · norm_num [gridPoint]

theorem exp_7_377_0 : (121156403271832689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (17140318908665940979469 / 173452975900640256000 : ℝ) := by
  apply lower_of_taylor (t := (2164129 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_377 : (1104354222254763 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 377 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (121156403271832689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_377_0
  · norm_num [gridPoint]

theorem exp_7_378_0 : (108269649979597897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (86110739588345014681493 / 870414707185204224000 : ℝ) := by
  apply lower_of_taylor (t := (2166031 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_378 : (1973780037506483 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 378 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (108269649979597897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_378_0
  · norm_num [gridPoint]

theorem exp_7_379_0 : (24185478390110561 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8652126401198962508313 / 87357024444364595200 : ℝ) := by
  apply lower_of_taylor (t := (2167937 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_379 : (564360580271233 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 379 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (24185478390110561 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_379_0
  · norm_num [gridPoint]

theorem exp_7_380_0 : (540194919593133 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (43466585156174098892261 / 438365745639263232000 : ℝ) := by
  apply lower_of_taylor (t := (1084923 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_380 : (2521055927558677 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 380 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (540194919593133 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_380_0
  · norm_num [gridPoint]

theorem exp_7_381_0 : (19302538925106011 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (17469292197501078893587 / 175979689537969152000 : ℝ) := by
  apply lower_of_taylor (t := (27147 / 12500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_381 : (5630233922174183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 381 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (19302538925106011 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_381_0
  · norm_num [gridPoint]

theorem exp_7_382_0 : (13792938486131957 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (17552227707109175363127 / 176614222735520768000 : ℝ) := by
  apply lower_of_taylor (t := (2173677 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_382 : (5028967332509567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 382 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (13792938486131957 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_382_0
  · norm_num [gridPoint]

theorem exp_7_383_0 : (61592507077215003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1377768835227411039217 / 13847648269403136000 : ℝ) := by
  apply lower_of_taylor (t := (2175597 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_383 : (898276190617719 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 383 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (61592507077215003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_383_0
  · norm_num [gridPoint]

theorem sum_7_352_2 : (33431095170489227 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 352 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_352) (by simpa only [blockSum_one] using cell_7_353) (by norm_num)

theorem sum_7_354_2 : (214912909284790943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 354 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_354) (by simpa only [blockSum_one] using cell_7_355) (by norm_num)

theorem sum_7_352_4 : (482361670648704759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 352 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_352_2 sum_7_354_2 (by norm_num)

theorem sum_7_356_2 : (34520372711194201 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 356 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_356) (by simpa only [blockSum_one] using cell_7_357) (by norm_num)

theorem sum_7_358_2 : (138545432792349811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 358 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_358) (by simpa only [blockSum_one] using cell_7_359) (by norm_num)

theorem sum_7_356_4 : (19446706021770051 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 356 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_356_2 sum_7_358_2 (by norm_num)

theorem sum_7_352_8 : (31740358679881023 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 352 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_352_4 sum_7_356_4 (by norm_num)

theorem sum_7_360_2 : (44459578942911949 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 360 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_360) (by simpa only [blockSum_one] using cell_7_361) (by norm_num)

theorem sum_7_362_2 : (44561265657357111 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 362 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_362) (by simpa only [blockSum_one] using cell_7_363) (by norm_num)

theorem sum_7_360_4 : (400542957343988189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 360 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_360_2 sum_7_362_2 (by norm_num)

theorem sum_7_364_2 : (71423522251564971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 364 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_364) (by simpa only [blockSum_one] using cell_7_365) (by norm_num)

theorem sum_7_366_2 : (22883852066235241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 366 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_366) (by simpa only [blockSum_one] using cell_7_367) (by norm_num)

theorem sum_7_364_4 : (257266304834306147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 364 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_364_2 sum_7_366_2 (by norm_num)

theorem sum_7_360_8 : (10278269721535849 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 360 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_360_4 sum_7_364_4 (by norm_num)

theorem sum_7_352_16 : (1122413598086172743 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 352 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_352_8 sum_7_360_8 (by norm_num)

theorem sum_7_368_2 : (11450215198931539 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 368 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_368) (by simpa only [blockSum_one] using cell_7_369) (by norm_num)

theorem sum_7_370_2 : (143158539548543 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 370 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_370) (by simpa only [blockSum_one] using cell_7_371) (by norm_num)

theorem sum_7_368_4 : (20612361730038291 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 368 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_368_2 sum_7_370_2 (by norm_num)

theorem sum_7_372_2 : (14655219307417753 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 372 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_372) (by simpa only [blockSum_one] using cell_7_373) (by norm_num)

theorem sum_7_374_2 : (9371978848157573 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 374 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_374) (by simpa only [blockSum_one] using cell_7_375) (by norm_num)

theorem sum_7_372_4 : (105480771470458877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 372 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_372_2 sum_7_374_2 (by norm_num)

theorem sum_7_368_8 : (54075933062153041 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 368 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_368_4 sum_7_372_4 (by norm_num)

theorem sum_7_376_2 : (18720030500444503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 376 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_376) (by simpa only [blockSum_one] using cell_7_377) (by norm_num)

theorem sum_7_378_2 : (29899254806832689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 378 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_378) (by simpa only [blockSum_one] using cell_7_379) (by norm_num)

theorem sum_7_376_4 : (13467863161544339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 376 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_376_2 sum_7_378_2 (by norm_num)

theorem sum_7_380_2 : (23865747482141751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 380 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_380) (by simpa only [blockSum_one] using cell_7_381) (by norm_num)

theorem sum_7_382_2 : (4760174142799081 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 382 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_382) (by simpa only [blockSum_one] using cell_7_383) (by norm_num)

theorem sum_7_380_4 : (1716257762133523 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 380 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_380_2 sum_7_382_2 (by norm_num)

theorem sum_7_376_8 : (11024575986105977 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 376 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_376_4 sum_7_380_4 (by norm_num)

theorem sum_7_368_16 : (15225017006872999 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 368 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_368_8 sum_7_376_8 (by norm_num)

theorem sum_7_352_32 : (2625452621344170461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 352 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_352_16 sum_7_368_16 (by norm_num)

#print axioms sum_7_352_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
