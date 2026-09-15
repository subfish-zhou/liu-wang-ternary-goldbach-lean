import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_352_0 : expNegUpper (608820606996219691643 / 6586462612439894400 : ℝ) ≤ (35919639407775367757 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1029427 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_352_1 : expNegUpper (97533435984132981211237 / 1053834017990383104000 : ℝ) ≤ (15994381376119920609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2060719 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_352 : rowCell 1 352 ≤ (1980776678785349871 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35919639407775367757 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15994381376119920609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_352_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_352_1
  · norm_num [gridPoint]

theorem exp_1_353_0 : expNegUpper (293713544729404932656039 / 3173530407055282688000 : ℝ) ≤ (31988761029009342923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2060719 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_353_1 : expNegUpper (147040857780122830630359 / 1586765203527641344000 : ℝ) ≤ (3560603548343622001 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2062587 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_353 : rowCell 1 353 ≤ (4409788471937587337 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31988761029009342923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3560603548343622001 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_353_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_353_1
  · norm_num [gridPoint]

theorem exp_1_354_0 : expNegUpper (5903969282825713462239 / 63711631968903424000 : ℝ) ≤ (2848482686387392747 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2062587 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_354_1 : expNegUpper (11822735701581327503437 / 127423263937806848000 : ℝ) ≤ (50723680711392294839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2064459 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_354 : rowCell 1 354 ≤ (7853094703032259887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2848482686387392747 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (50723680711392294839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_354_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_354_1
  · norm_num [gridPoint]

theorem exp_1_355_0 : expNegUpper (98896219862055440028479 / 1065885209380271616000 : ℝ) ≤ (25361839010014276423 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2064459 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_355_1 : expNegUpper (24755029073550014111533 / 266471302345067904000 : ℝ) ≤ (22578713459002274917 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (413267 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_355 : rowCell 1 355 ≤ (1747934078815397903 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25361839010014276423 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22578713459002274917 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_355_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_355_1
  · norm_num [gridPoint]

theorem exp_1_356_0 : expNegUpper (5734310404930490775107 / 61726009541196416000 : ℝ) ≤ (22578712270012778559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (413267 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_356_1 : expNegUpper (4593193762796696203803 / 49380807632957132800 : ℝ) ≤ (40197510861607653103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1034107 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_356 : rowCell 1 356 ≤ (1244831715112373719 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22578712270012778559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40197510861607653103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_356_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_356_1
  · norm_num [gridPoint]

theorem exp_1_357_0 : expNegUpper (59936983708856384100279 / 644374440489873510400 : ℝ) ≤ (4019750876072706649 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1034107 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_357_1 : expNegUpper (150030069814713543020693 / 1610936101224683776000 : ℝ) ≤ (35778403202117347861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2070097 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_357 : rowCell 1 357 ≤ (5540231759939018813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4019750876072706649 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35778403202117347861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_357_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_357_1
  · norm_num [gridPoint]

theorem exp_1_358_0 : expNegUpper (50198500340365694566999 / 539002457843712768000 : ℝ) ≤ (3577840134622530331 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2070097 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_358_1 : expNegUpper (100522664672621438150011 / 1078004915687425536000 : ℝ) ≤ (31841596705475098387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2071983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_358 : rowCell 1 358 ≤ (4930911010271992867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3577840134622530331 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31841596705475098387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_358_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_358_1
  · norm_num [gridPoint]

theorem exp_1_359_0 : expNegUpper (12108096061698436309457 / 129847205199237632000 : ℝ) ≤ (31841595066160567779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2071983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_359_1 : expNegUpper (1515405838697177926011 / 16230900649904704000 : ℝ) ≤ (28334860628347269689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (129617 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_359 : rowCell 1 359 ≤ (4388121214027924543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31841595066160567779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28334860628347269689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_359_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_359_1
  · norm_num [gridPoint]

theorem exp_1_360_0 : expNegUpper (1226690028376696726749 / 13138582061311936000 : ℝ) ≤ (28334859180474671029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (129617 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_360_1 : expNegUpper (9825795831821920807321 / 105108656490495488000 : ℝ) ≤ (504231469784227537 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (415153 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_360 : rowCell 1 360 ≤ (3904653978396608283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28334859180474671029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (504231469784227537 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_360_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_360_1
  · norm_num [gridPoint]

theorem exp_1_361_0 : expNegUpper (101913729506470818541013 / 1090193136911844864000 : ℝ) ≤ (1008462888421812823 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (415153 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_361_1 : expNegUpper (2040823421008898937689 / 21803862738236897280 : ℝ) ≤ (22430126074006200789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1038831 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_361 : rowCell 1 361 ≤ (694815088399559893 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1008462888421812823 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22430126074006200789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_361_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_361_1
  · norm_num [gridPoint]

theorem exp_1_362_0 : expNegUpper (6145371919615491132667 / 65656266171429283840 : ℝ) ≤ (11215062472439469591 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1038831 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_362_1 : expNegUpper (307652704826340118810461 / 3282813308571464192000 : ℝ) ≤ (9976693681123571907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1039781 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_362 : rowCell 1 362 ≤ (1545321898186236203 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11215062472439469591 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9976693681123571907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_362_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_362_1
  · norm_num [gridPoint]

theorem exp_1_363_0 : expNegUpper (308801359413845737993749 / 3295070044713148928000 : ℝ) ≤ (9976693182631949467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1039781 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_363_1 : expNegUpper (77296813950958506556837 / 823767511178287232000 : ℝ) ≤ (8874113406133802023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1040733 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_363 : rowCell 1 363 ≤ (1374617752724343193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9976693182631949467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8874113406133802023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_363_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_363_1
  · norm_num [gridPoint]

theorem exp_1_364_0 : expNegUpper (1034464962703215488111 / 11024498730535296000 : ℝ) ≤ (8874112966022745231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1040733 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_364_1 : expNegUpper (4143029014348736128441 / 44097994922141184000 : ℝ) ≤ (15785087120533710953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2083373 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_364 : rowCell 1 364 ≤ (611319828845005261 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8874112966022745231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15785087120533710953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_364_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_364_1
  · norm_num [gridPoint]

theorem exp_1_365_0 : expNegUpper (311882994164469928681067 / 3319652031913783808000 : ℝ) ≤ (3946271585867612573 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2083373 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_365_1 : expNegUpper (156136237817821157878353 / 1659826015956891904000 : ℝ) ≤ (3509400544362711601 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2085283 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_365 : rowCell 1 365 ≤ (2174697240767298971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3946271585867612573 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3509400544362711601 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_365_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_365_1
  · norm_num [gridPoint]

theorem exp_1_366_0 : expNegUpper (156715942733350115733057 / 1665988641486366976000 : ℝ) ≤ (2807520298303979589 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2085283 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_366_1 : expNegUpper (62764632894926798265461 / 666395456594546790400 : ℝ) ≤ (6241127743819471881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2087197 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_366 : rowCell 1 366 ≤ (1933851797354267451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2807520298303979589 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6241127743819471881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_366_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_366_1
  · norm_num [gridPoint]

theorem exp_1_367_0 : expNegUpper (20999078180666280101167 / 222955024822495948800 : ℝ) ≤ (6241127441104027483 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2087197 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_367_1 : expNegUpper (6570401095530601730707 / 69673445257029984000 : ℝ) ≤ (11098074812521147111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (417823 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_367 : rowCell 1 367 ≤ (429874706698028381 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6241127441104027483 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11098074812521147111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_367_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_367_1
  · norm_num [gridPoint]

theorem exp_1_368_0 : expNegUpper (19784116617918155347769 / 209793518750493728000 : ℝ) ≤ (2219614855638333043 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (417823 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_368_1 : expNegUpper (316940749960485637725663 / 3356696300007899648000 : ℝ) ≤ (9866359232853182877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (522759 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_368 : rowCell 1 368 ≤ (1528745326858622903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2219614855638333043 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9866359232853182877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_368_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_368_1
  · norm_num [gridPoint]

theorem exp_1_369_0 : expNegUpper (978802999966546862571 / 10366430972258816000 : ℝ) ≤ (4933179380658884183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (522759 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_369_1 : expNegUpper (490011794756958310787 / 5183215486129408000 : ℝ) ≤ (8770435223569314353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (13081 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_369 : rowCell 1 369 ≤ (1359011761372561869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4933179380658884183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8770435223569314353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_369_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_369_1
  · norm_num [gridPoint]

theorem exp_1_370_0 : expNegUpper (53280251668274097093397 / 563584445044347648000 : ℝ) ≤ (4385217403742981593 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (13081 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_370_1 : expNegUpper (106693337490806440886887 / 1127168890088695296000 : ℝ) ≤ (243607458987002703 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (261861 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_370 : rowCell 1 370 ≤ (966398702929981 / 800000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4385217403742981593 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (243607458987002703 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_370_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_370_1
  · norm_num [gridPoint]

theorem exp_1_371_0 : expNegUpper (321257480940579688967789 / 3393946112853811712000 : ℝ) ≤ (3897719160232302177 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (261861 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_371_1 : expNegUpper (16082889879700677320103 / 169697305642690585600 : ℝ) ≤ (6928120213063731913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2096819 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_371 : rowCell 1 371 ≤ (134206889557750781 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3897719160232302177 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6928120213063731913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_371_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_371_1
  · norm_num [gridPoint]

theorem exp_1_372_0 : expNegUpper (16141944888713584814343 / 170320419687364633600 : ℝ) ≤ (6928119889175013571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2096819 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_372_1 : expNegUpper (323241031949144219964811 / 3406408393747292672000 : ℝ) ≤ (6156671103855298259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1049377 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_372 : rowCell 1 372 ≤ (47707735753933907 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6928119889175013571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6156671103855298259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_372_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_372_1
  · norm_num [gridPoint]

theorem exp_1_373_0 : expNegUpper (108141923501019750415553 / 1139631170982176256000 : ℝ) ≤ (1539167704532987889 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1049377 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_373_1 : expNegUpper (54138287588358331679663 / 569815585491088128000 : ℝ) ≤ (547056798855517379 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (525173 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_373 : rowCell 1 373 ≤ (211967175032747641 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1539167704532987889 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (547056798855517379 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_373_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_373_1
  · norm_num [gridPoint]

theorem exp_1_374_0 : expNegUpper (260814487295424800461 / 2745121176361216000 : ℝ) ≤ (2735283868261096513 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (525173 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_374_1 : expNegUpper (522278221326991205553 / 5490242352722432000 : ℝ) ≤ (4860434043099500613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1051317 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_374 : rowCell 1 374 ≤ (1177103018014727 / 1562500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2735283868261096513 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4860434043099500613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_374_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_374_1
  · norm_num [gridPoint]

theorem exp_1_375_0 : expNegUpper (327615923615275591004697 / 3443932266262266368000 : ℝ) ≤ (2430216910401920531 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1051317 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_375_1 : expNegUpper (41002941292392675858977 / 430491533282783296000 : ℝ) ≤ (67467422928988959 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2104579 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_375 : rowCell 1 375 ≤ (669293447104685379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2430216910401920531 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (67467422928988959 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_375_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_375_1
  · norm_num [gridPoint]

theorem exp_1_376_0 : expNegUpper (13717467665974236219211 / 144020245849115328000 : ℝ) ≤ (1079478717851332227 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2104579 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_376_1 : expNegUpper (21975244103453623134041 / 230432393358584524800 : ℝ) ≤ (767113768280263829 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2106527 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_376 : rowCell 1 376 ≤ (594559357733384001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1079478717851332227 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (767113768280263829 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_376_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_376_1
  · norm_num [gridPoint]

theorem exp_1_377_0 : expNegUpper (66165604043187576414883 / 693812474560204902400 : ℝ) ≤ (3835568668513280549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2106527 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_377_1 : expNegUpper (165619645979848485308043 / 1734531186400512256000 : ℝ) ≤ (851691587421770147 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2108479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_377 : rowCell 1 377 ≤ (528117576312538249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3835568668513280549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (851691587421770147 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_377_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_377_1
  · norm_num [gridPoint]

theorem exp_1_378_0 : expNegUpper (166221161152641438086907 / 1740830841764518144000 : ℝ) ≤ (851691549309418701 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2108479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_378_1 : expNegUpper (332855431555157924417293 / 3481661683529036288000 : ℝ) ≤ (3025603615002543459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422087 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_378 : rowCell 1 378 ≤ (469054185790809901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (851691549309418701 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3025603615002543459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_378_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_378_1
  · norm_num [gridPoint]

theorem exp_1_379_0 : expNegUpper (4454161869916737310511 / 46590451100837376000 : ℝ) ≤ (47275054384172577 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422087 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_379_1 : expNegUpper (1114923634435086183811 / 11647612775209344000 : ℝ) ≤ (107472920397563619 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1056197 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_379 : rowCell 1 379 ≤ (104138817986835219 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47275054384172577 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (107472920397563619 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_379_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_379_1
  · norm_num [gridPoint]

theorem exp_1_380_0 : expNegUpper (83921871005923448786753 / 876732204975581312000 : ℝ) ≤ (2686822891434276563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1056197 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_380_1 : expNegUpper (336104278278139409523171 / 3506928819902325248000 : ℝ) ≤ (2385743038054284459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (528589 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_380 : rowCell 1 380 ≤ (73979212992351629 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2686822891434276563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2385743038054284459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_380_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_380_1
  · norm_num [gridPoint]

theorem exp_1_381_0 : expNegUpper (337318363637437013478939 / 3519596645547602432000 : ℝ) ≤ (596435733396414623 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (528589 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_381_1 : expNegUpper (33773700539033723428597 / 351959664554760243200 : ℝ) ≤ (33096807510781171 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1058161 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_381 : rowCell 1 381 ≤ (82107812565082353 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (596435733396414623 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33096807510781171 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_381_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_381_1
  · norm_num [gridPoint]

theorem exp_1_382_0 : expNegUpper (869114843788009230803 / 9057146947432396800 : ℝ) ≤ (2118195588602803911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1058161 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_382_1 : expNegUpper (8701930298960460927199 / 90571469474323968000 : ℝ) ≤ (376094100322352339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2118291 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_382 : rowCell 1 382 ≤ (9112072620312861 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2118195588602803911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (376094100322352339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_382_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_382_1
  · norm_num [gridPoint]

theorem exp_1_383_0 : expNegUpper (340596770335692201478769 / 3545000811755422208000 : ℝ) ≤ (1880470420445371973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2118291 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_383_1 : expNegUpper (2664211852170627202161 / 27695318841839236000 : ℝ) ≤ (1669264786983686319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2120263 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_383 : rowCell 1 383 ≤ (64712470135238089 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1880470420445371973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1669264786983686319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_383_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_383_1
  · norm_num [gridPoint]

theorem sum_1_352_2 : blockSum (rowCell 1) 352 2 ≤ (18723460337801924029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_352) (by simpa only [blockSum_one] using cell_1_353) (by norm_num)

theorem sum_1_354_2 : blockSum (rowCell 1) 354 2 ≤ (14844831018293851499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_354) (by simpa only [blockSum_one] using cell_1_355) (by norm_num)

theorem sum_1_352_4 : blockSum (rowCell 1) 352 4 ≤ (4196036419511971941 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_352_2 sum_1_354_2 (by norm_num)

theorem sum_1_356_2 : blockSum (rowCell 1) 356 2 ≤ (735274395968805463 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_356) (by simpa only [blockSum_one] using cell_1_357) (by norm_num)

theorem sum_1_358_2 : blockSum (rowCell 1) 358 2 ≤ (931903222429991741 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_358) (by simpa only [blockSum_one] using cell_1_359) (by norm_num)

theorem sum_1_356_4 : blockSum (rowCell 1) 356 4 ≤ (10541711279900402409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_356_2 sum_1_358_2 (by norm_num)

theorem sum_1_352_8 : blockSum (rowCell 1) 352 8 ≤ (27325856957948290173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_352_4 sum_1_356_4 (by norm_num)

theorem sum_1_360_2 : blockSum (rowCell 1) 360 2 ≤ (1844682355098601937 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_360) (by simpa only [blockSum_one] using cell_1_361) (by norm_num)

theorem sum_1_362_2 : blockSum (rowCell 1) 362 2 ≤ (729984912727644849 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_362) (by simpa only [blockSum_one] using cell_1_363) (by norm_num)

theorem sum_1_360_4 : blockSum (rowCell 1) 360 4 ≤ (660930436110778327 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_360_2 sum_1_362_2 (by norm_num)

theorem sum_1_364_2 : blockSum (rowCell 1) 364 2 ≤ (923995311229464003 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_364) (by simpa only [blockSum_one] using cell_1_365) (by norm_num)

theorem sum_1_366_2 : blockSum (rowCell 1) 366 2 ≤ (146134024965855239 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_366) (by simpa only [blockSum_one] using cell_1_367) (by norm_num)

theorem sum_1_364_4 : blockSum (rowCell 1) 364 4 ≤ (827332718029370099 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_364_2 sum_1_366_2 (by norm_num)

theorem sum_1_360_8 : blockSum (rowCell 1) 360 8 ≤ (2149193590250926753 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_360_4 sum_1_364_4 (by norm_num)

theorem sum_1_352_16 : blockSum (rowCell 1) 352 16 ≤ (19035912454601461969 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_352_8 sum_1_360_8 (by norm_num)

theorem sum_1_368_2 : blockSum (rowCell 1) 368 2 ≤ (721939272057796193 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_368) (by simpa only [blockSum_one] using cell_1_369) (by norm_num)

theorem sum_1_370_2 : blockSum (rowCell 1) 370 2 ≤ (1140826747562241249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_370) (by simpa only [blockSum_one] using cell_1_371) (by norm_num)

theorem sum_1_368_4 : blockSum (rowCell 1) 368 4 ≤ (516941058335566727 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_368_2 sum_1_370_2 (by norm_num)

theorem sum_1_372_2 : blockSum (rowCell 1) 372 2 ≤ (56313231725302147 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_372) (by simpa only [blockSum_one] using cell_1_373) (by norm_num)

theorem sum_1_374_2 : blockSum (rowCell 1) 374 2 ≤ (1422639378634110659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_374) (by simpa only [blockSum_one] using cell_1_375) (by norm_num)

theorem sum_1_372_4 : blockSum (rowCell 1) 372 4 ≤ (3224662793843779363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_372_2 sum_1_374_2 (by norm_num)

theorem sum_1_368_8 : blockSum (rowCell 1) 368 8 ≤ (8394073377199446633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_368_4 sum_1_372_4 (by norm_num)

theorem sum_1_376_2 : blockSum (rowCell 1) 376 2 ≤ (4490707736183689 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_376) (by simpa only [blockSum_one] using cell_1_377) (by norm_num)

theorem sum_1_378_2 : blockSum (rowCell 1) 378 2 ≤ (885609457738150777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_378) (by simpa only [blockSum_one] using cell_1_379) (by norm_num)

theorem sum_1_376_4 : blockSum (rowCell 1) 376 4 ≤ (2008286391784073027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_376_2 sum_1_378_2 (by norm_num)

theorem sum_1_380_2 : blockSum (rowCell 1) 380 2 ≤ (698327315222087557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_380) (by simpa only [blockSum_one] using cell_1_381) (by norm_num)

theorem sum_1_382_2 : blockSum (rowCell 1) 382 2 ≤ (137609051097740977 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_382) (by simpa only [blockSum_one] using cell_1_383) (by norm_num)

theorem sum_1_380_4 : blockSum (rowCell 1) 380 4 ≤ (249752703922610293 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_380_2 sum_1_382_2 (by norm_num)

theorem sum_1_376_8 : blockSum (rowCell 1) 376 8 ≤ (814262477849281123 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_376_4 sum_1_380_4 (by norm_num)

theorem sum_1_368_16 : blockSum (rowCell 1) 368 16 ≤ (93208986308772569 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_368_8 sum_1_376_8 (by norm_num)

theorem sum_1_352_32 : blockSum (rowCell 1) 352 32 ≤ (87794773107002419001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_352_16 sum_1_368_16 (by norm_num)

#print axioms sum_1_352_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
