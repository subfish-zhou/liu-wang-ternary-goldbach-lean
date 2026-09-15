import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_416_0 : expNegUpper (12794814327391984627027 / 124292458617438736000 : ℝ) ≤ (983129563840097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (223497 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_416_1 : expNegUpper (81980008621656751811171 / 795471735151607910400 : ℝ) ≤ (874438177707427 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2237017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_416 : rowCell 5 416 ≤ (270911017244327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (983129563840097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (874438177707427 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_416_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_416_1
  · norm_num [gridPoint]

theorem exp_5_417_0 : expNegUpper (82258060192596485798011 / 798169736082100326400 : ℝ) ≤ (1748876283649571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2237017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_417_1 : expNegUpper (205879126500620523580343 / 1995424340205250816000 : ℝ) ≤ (388843949077923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2239067 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_417 : rowCell 5 417 ≤ (120474515167377 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1748876283649571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (388843949077923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_417_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_417_1
  · norm_num [gridPoint]

theorem exp_5_418_0 : expNegUpper (206576224499878000181927 / 2002180761684359424000 : ℝ) ≤ (311075146583423 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2239067 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_418_1 : expNegUpper (413622371775312534623813 / 4004361523368718848000 : ℝ) ≤ (1383151250288909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2241121 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_418 : rowCell 5 418 ≤ (10714001384911 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (311075146583423 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1383151250288909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_418_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_418_1
  · norm_num [gridPoint]

theorem exp_5_419_0 : expNegUpper (16600820503168114756613 / 160715888185307648000 : ℝ) ≤ (1383151194293439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2241121 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_419_1 : expNegUpper (4154924094228368681743 / 40178972046326912000 : ℝ) ≤ (614939419786689 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1121589 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_419 : rowCell 5 419 ≤ (9527224885687 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1383151194293439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (614939419786689 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_419_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_419_1
  · norm_num [gridPoint]

theorem exp_5_420_0 : expNegUpper (104223625423415420343383 / 1007863931050604672000 : ℝ) ≤ (307469697529403 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1121589 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_420_1 : expNegUpper (417368375936152694541211 / 4031455724202418688000 : ℝ) ≤ (218697344482931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2245239 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_420 : rowCell 5 420 ≤ (42355475143139 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (307469697529403 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (218697344482931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_420_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_420_1
  · norm_num [gridPoint]

theorem exp_5_421_0 : expNegUpper (418774426335471084467539 / 4045037082077901312000 : ℝ) ≤ (546743339369249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2245239 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_421_1 : expNegUpper (41925028130759866045361 / 404503708207790131200 : ℝ) ≤ (486063982238217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2247303 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_421 : rowCell 5 421 ≤ (150626475608889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (546743339369249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (486063982238217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_421_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_421_1
  · norm_num [gridPoint]

theorem exp_5_422_0 : expNegUpper (1356968698377321693311 / 13092391220190771200 : ℝ) ≤ (972127925907683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2247303 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_422_1 : expNegUpper (13585101146113335891631 / 130923912201907712000 : ℝ) ≤ (864156306712643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2249371 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_422 : rowCell 5 422 ≤ (13390349602929 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (972127925907683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (864156306712643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_422_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_422_1
  · norm_num [gridPoint]

theorem exp_5_423_0 : expNegUpper (422552122170496249479209 / 4072268312746131968000 : ℝ) ≤ (216039068164221 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2249371 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_423_1 : expNegUpper (52878993574279449728891 / 509033539093266496000 : ℝ) ≤ (76810452316079 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2251443 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_423 : rowCell 5 423 ≤ (59512961857667 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (216039068164221 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (76810452316079 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_423_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_423_1
  · norm_num [gridPoint]

theorem exp_5_424_0 : expNegUpper (84889982669677860971 / 817183637107776000 : ℝ) ≤ (768104493092441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2251443 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_424_1 : expNegUpper (679890768790566180407 / 6537469096862208000 : ℝ) ≤ (341332547114083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1126759 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_424 : rowCell 5 424 ≤ (5289571086661 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (768104493092441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (341332547114083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_424_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_424_1
  · norm_num [gridPoint]

theorem exp_5_425_0 : expNegUpper (426353680022987537782847 / 4099590896637383168000 : ℝ) ≤ (170666266920637 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1126759 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_425_1 : expNegUpper (213418745610728427069683 / 2049795448318691584000 : ℝ) ≤ (75834118731713 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2255597 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_425 : rowCell 5 425 ≤ (94019686628369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (170666266920637 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (75834118731713 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_425_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_425_1
  · norm_num [gridPoint]

theorem exp_5_426_0 : expNegUpper (214131716093314797495907 / 2056643223020820736000 : ℝ) ≤ (303336463210013 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2255597 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_426_1 : expNegUpper (85749848153726643743033 / 822657289208328294400 : ℝ) ≤ (26954503137103 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2257679 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_426 : rowCell 5 426 ≤ (16710013313227 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (303336463210013 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26954503137103 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_426_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_426_1
  · norm_num [gridPoint]

theorem exp_5_427_0 : expNegUpper (86035835966330824642193 / 825400966750330982400 : ℝ) ≤ (269545021028597 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2257679 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_427_1 : expNegUpper (107666747281992900802709 / 1031751208437913728000 : ℝ) ≤ (239495847497139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451953 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_427 : rowCell 5 427 ≤ (18559858737151 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (269545021028597 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (239495847497139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_427_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_427_1
  · norm_num [gridPoint]

theorem exp_5_428_0 : expNegUpper (108025233237599942292341 / 1035186514941855872000 : ℝ) ≤ (95798335347453 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451953 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_428_1 : expNegUpper (432590746291810654355443 / 4140746059767423488000 : ℝ) ≤ (106388530544499 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1130927 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_428 : rowCell 5 428 ≤ (4122518270923 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (95798335347453 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (106388530544499 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_428_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_428_1
  · norm_num [gridPoint]

theorem exp_5_429_0 : expNegUpper (17361148061408207183843 / 166180404963557888000 : ℝ) ≤ (106388526516293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1130927 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_429_1 : expNegUpper (8690410445049780377561 / 83090202481778944000 : ℝ) ≤ (378043677437391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2263947 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_429 : rowCell 5 429 ≤ (58599072355391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (106388526516293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (378043677437391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_429_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_429_1
  · norm_num [gridPoint]

theorem exp_5_430_0 : expNegUpper (217981247789204500610081 / 2084148513358113024000 : ℝ) ≤ (47255457902259 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2263947 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_430_1 : expNegUpper (436456327002345343507721 / 4168297026716226048000 : ℝ) ≤ (167903487431179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2266043 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_430 : rowCell 5 430 ≤ (1626707183719 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47255457902259 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (167903487431179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_430_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_430_1
  · norm_num [gridPoint]

theorem exp_5_431_0 : expNegUpper (437902325072349880770689 / 4182106767649260032000 : ℝ) ≤ (33580696231503 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2266043 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_431_1 : expNegUpper (5479977131671478437169 / 52276334595615750400 : ℝ) ≤ (149131093108897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2268143 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_431 : rowCell 5 431 ≤ (9247378396503 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33580696231503 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (149131093108897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_431_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_431_1
  · norm_num [gridPoint]

theorem exp_5_432_0 : expNegUpper (116980904257810230047 / 1115941315661715200 : ℝ) ≤ (149131087573367 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2268143 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_432_1 : expNegUpper (9369065166786094893713 / 89275305252937216000 : ℝ) ≤ (264891258457257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2270247 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_432 : rowCell 5 432 ≤ (41065654336567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (149131087573367 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (264891258457257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_432_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_432_1
  · norm_num [gridPoint]

theorem exp_5_433_0 : expNegUpper (441800130381797400567319 / 4209794764432593408000 : ℝ) ≤ (52978249737909 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2270247 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_433_1 : expNegUpper (221150006955184272664879 / 2104897382216296704000 : ℝ) ≤ (235232971372011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1136177 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_433 : rowCell 5 433 ≤ (36469507457243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (52978249737909 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (235232971372011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_433_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_433_1
  · norm_num [gridPoint]

theorem exp_5_434_0 : expNegUpper (8875162523639626685431 / 84473460405657856000 : ℝ) ≤ (29404120344361 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1136177 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_434_1 : expNegUpper (17770401349612927107133 / 168946920811315712000 : ℝ) ≤ (13054796587599 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (71077 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_434 : rowCell 5 434 ≤ (16192439461793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29404120344361 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13054796587599 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_434_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_434_1
  · norm_num [gridPoint]

theorem exp_5_435_0 : expNegUpper (445722197402256912818477 / 4237574114438947328000 : ℝ) ≤ (20887673780011 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (71077 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_435_1 : expNegUpper (111556533080287250944819 / 1059393528609736832000 : ℝ) ≤ (185457119185301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2276579 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_435 : rowCell 5 435 ≤ (28755179135701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20887673780011 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (185457119185301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_435_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_435_1
  · norm_num [gridPoint]

theorem exp_5_436_0 : expNegUpper (111923088508740695734291 / 1062874511725189248000 : ℝ) ≤ (18545711248029 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2276579 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_436_1 : expNegUpper (17927932785807386814467 / 170059921876030279680 : ℝ) ≤ (4116220624567 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (284837 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_436 : rowCell 5 436 ≤ (25530039508103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18545711248029 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4116220624567 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_436_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_436_1
  · norm_num [gridPoint]

theorem exp_5_437_0 : expNegUpper (17986744242897503654267 / 170617792706732871680 : ℝ) ≤ (82324409534433 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (284837 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_437_1 : expNegUpper (225088302852384412077293 / 2132722408834160896000 : ℝ) ≤ (146162397738531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2280817 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_437 : rowCell 5 437 ≤ (708269786689 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (82324409534433 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (146162397738531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_437_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_437_1
  · norm_num [gridPoint]

theorem exp_5_438_0 : expNegUpper (225825481753509992403037 / 2139707213370820864000 : ℝ) ≤ (29232478504591 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2280817 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_438_1 : expNegUpper (452161000492240111887073 / 4279414426741641728000 : ℝ) ≤ (129740260410271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1141471 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_438 : rowCell 5 438 ≤ (20119069333181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29232478504591 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (129740260410271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_438_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_438_1
  · norm_num [gridPoint]

theorem exp_5_439_0 : expNegUpper (18145577453241944400577 / 171736274964828672000 : ℝ) ≤ (32435063952711 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1141471 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_439_1 : expNegUpper (2270757569999685901441 / 21467034370603584000 : ℝ) ≤ (115153234294151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228507 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_439 : rowCell 5 439 ≤ (1116115832497 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32435063952711 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (115153234294151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_439_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_439_1
  · norm_num [gridPoint]

theorem exp_5_440_0 : expNegUpper (56954254317107764213849 / 538427769975693376000 : ℝ) ≤ (115153230238393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228507 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_440_1 : expNegUpper (456148156220198676087031 / 4307422159805547008000 : ℝ) ≤ (12774678569971 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1143601 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_440 : rowCell 5 440 ≤ (3169881063109 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (115153230238393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12774678569971 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_440_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_440_1
  · norm_num [gridPoint]

theorem exp_5_441_0 : expNegUpper (457634768116799142624239 / 4321460283796132352000 : ℝ) ≤ (102197424983687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1143601 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_441_1 : expNegUpper (45815093714536324601263 / 432146028379613235200 : ℝ) ≤ (3627658723827 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2289337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_441 : rowCell 5 441 ≤ (7032815690981 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (102197424983687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3627658723827 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_441_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_441_1
  · norm_num [gridPoint]

theorem exp_5_442_0 : expNegUpper (45964164706319834348383 / 433552124609247283200 : ℝ) ≤ (90691464942777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2289337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_442_1 : expNegUpper (460159866767769536794061 / 4335521246092472832000 : ℝ) ≤ (16094804628809 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (572869 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_442 : rowCell 5 442 ≤ (2496308234557 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (90691464942777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16094804628809 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_442_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_442_1
  · norm_num [gridPoint]

theorem exp_5_443_0 : expNegUpper (461654681368398363018629 / 4349605046694568448000 : ℝ) ≤ (80474020364461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (572869 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_443_1 : expNegUpper (115543738769939048790097 / 1087401261673642112000 : ℝ) ≤ (35700804056757 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2293619 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_443 : rowCell 5 443 ≤ (5537453639687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (80474020364461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35700804056757 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_443_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_443_1
  · norm_num [gridPoint]

theorem exp_5_444_0 : expNegUpper (4636738810247378479577 / 43637116856024192000 : ℝ) ≤ (8925200707903 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2293619 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_444_1 : expNegUpper (18567848482946474713627 / 174548467424096768000 : ℝ) ≤ (63346620455231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (573941 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_444 : rowCell 5 444 ≤ (4912980855709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8925200707903 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (63346620455231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_444_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_444_1
  · norm_num [gridPoint]

theorem exp_5_445_0 : expNegUpper (465699256024555445030107 / 4377841162816025088000 : ℝ) ≤ (12669323659077 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (573941 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_445_1 : expNegUpper (233111823870912600781993 / 2188920581408012544000 : ℝ) ≤ (14048898402873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1148957 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_445 : rowCell 5 445 ≤ (544820343341 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12669323659077 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14048898402873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_445_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_445_1
  · norm_num [gridPoint]

theorem exp_5_446_0 : expNegUpper (233865408180094900482457 / 2195996739167693056000 : ℝ) ≤ (56195591707803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1148957 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_446_1 : expNegUpper (93651454415316968611877 / 878398695667077222400 : ℝ) ≤ (49847640838263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2300067 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_446 : rowCell 5 446 ≤ (1933191947619 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (56195591707803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (49847640838263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_446_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_446_1
  · norm_num [gridPoint]

theorem exp_5_447_0 : expNegUpper (93953714404795912498237 / 881233726432100454400 : ℝ) ≤ (1993905566419 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2300067 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_447_1 : expNegUpper (7348392110473116235249 / 68846384877507848000 : ℝ) ≤ (44213069197399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2302223 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_447 : rowCell 5 447 ≤ (1714747840281 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1993905566419 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44213069197399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_447_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_447_1
  · norm_num [gridPoint]

theorem sum_5_416_2 : blockSum (rowCell 5) 416 2 ≤ (511860047579081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_416) (by simpa only [blockSum_one] using cell_5_417) (by norm_num)

theorem sum_5_418_2 : blockSum (rowCell 5) 418 2 ≤ (10120613135299 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_418) (by simpa only [blockSum_one] using cell_5_419) (by norm_num)

theorem sum_5_416_4 : blockSum (rowCell 5) 416 4 ≤ (916684572991041 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_416_2 sum_5_418_2 (by norm_num)

theorem sum_5_420_2 : blockSum (rowCell 5) 420 2 ≤ (64009675236289 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_420) (by simpa only [blockSum_one] using cell_5_421) (by norm_num)

theorem sum_5_422_2 : blockSum (rowCell 5) 422 2 ≤ (15808088734039 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_422) (by simpa only [blockSum_one] using cell_5_423) (by norm_num)

theorem sum_5_420_4 : blockSum (rowCell 5) 420 4 ≤ (572977795926069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_420_2 sum_5_422_2 (by norm_num)

theorem sum_5_416_8 : blockSum (rowCell 5) 416 8 ≤ (148966236891711 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_416_4 sum_5_420_4 (by norm_num)

theorem sum_5_424_2 : blockSum (rowCell 5) 424 2 ≤ (199811108361589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_424) (by simpa only [blockSum_one] using cell_5_425) (by norm_num)

theorem sum_5_426_2 : blockSum (rowCell 5) 426 2 ≤ (157789501514739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_426) (by simpa only [blockSum_one] using cell_5_427) (by norm_num)

theorem sum_5_424_4 : blockSum (rowCell 5) 424 4 ≤ (44700076234541 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_424_2 sum_5_426_2 (by norm_num)

theorem sum_5_428_2 : blockSum (rowCell 5) 428 2 ≤ (124559364690159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_428) (by simpa only [blockSum_one] using cell_5_429) (by norm_num)

theorem sum_5_430_2 : blockSum (rowCell 5) 430 2 ≤ (98291521861523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_430) (by simpa only [blockSum_one] using cell_5_431) (by norm_num)

theorem sum_5_428_4 : blockSum (rowCell 5) 428 4 ≤ (111425443275841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_428_2 sum_5_430_2 (by norm_num)

theorem sum_5_424_8 : blockSum (rowCell 5) 424 8 ≤ (58045149642801 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_424_4 sum_5_428_4 (by norm_num)

theorem sum_5_416_16 : blockSum (rowCell 5) 416 16 ≤ (12938211658407 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_416_8 sum_5_424_8 (by norm_num)

theorem sum_5_432_2 : blockSum (rowCell 5) 432 2 ≤ (7753516179381 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_432) (by simpa only [blockSum_one] using cell_5_433) (by norm_num)

theorem sum_5_434_2 : blockSum (rowCell 5) 434 2 ≤ (61140058059287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_434) (by simpa only [blockSum_one] using cell_5_435) (by norm_num)

theorem sum_5_432_4 : blockSum (rowCell 5) 432 4 ≤ (138675219853097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_432_2 sum_5_434_2 (by norm_num)

theorem sum_5_436_2 : blockSum (rowCell 5) 436 2 ≤ (48194672682151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_436) (by simpa only [blockSum_one] using cell_5_437) (by norm_num)

theorem sum_5_438_2 : blockSum (rowCell 5) 438 2 ≤ (37976922653133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_438) (by simpa only [blockSum_one] using cell_5_439) (by norm_num)

theorem sum_5_436_4 : blockSum (rowCell 5) 436 4 ≤ (21542898833821 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_436_2 sum_5_438_2 (by norm_num)

theorem sum_5_432_8 : blockSum (rowCell 5) 432 8 ≤ (224846815188381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_432_4 sum_5_436_4 (by norm_num)

theorem sum_5_440_2 : blockSum (rowCell 5) 440 2 ≤ (29915036697507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_440) (by simpa only [blockSum_one] using cell_5_441) (by norm_num)

theorem sum_5_442_2 : blockSum (rowCell 5) 442 2 ≤ (23556448452159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_442) (by simpa only [blockSum_one] using cell_5_443) (by norm_num)

theorem sum_5_440_4 : blockSum (rowCell 5) 440 4 ≤ (26735742574833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_440_2 sum_5_442_2 (by norm_num)

theorem sum_5_444_2 : blockSum (rowCell 5) 444 2 ≤ (9271543602437 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_444) (by simpa only [blockSum_one] using cell_5_445) (by norm_num)

theorem sum_5_446_2 : blockSum (rowCell 5) 446 2 ≤ (36479397879 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_446) (by simpa only [blockSum_one] using cell_5_447) (by norm_num)

theorem sum_5_444_4 : blockSum (rowCell 5) 444 4 ≤ (16567423178237 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_444_2 sum_5_446_2 (by norm_num)

theorem sum_5_440_8 : blockSum (rowCell 5) 440 8 ≤ (4330316575307 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_440_4 sum_5_444_4 (by norm_num)

theorem sum_5_432_16 : blockSum (rowCell 5) 432 16 ≤ (311453146694521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_432_8 sum_5_440_8 (by norm_num)

theorem sum_5_416_32 : blockSum (rowCell 5) 416 32 ≤ (2381567012039641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_416_16 sum_5_432_16 (by norm_num)

#print axioms sum_5_416_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
