import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_416_0 : expNegUpper (12750010840712944627027 / 124292458617438736000 : ℝ) ≤ (704904264500923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (445737 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_416_1 : expNegUpper (81693751755865571011171 / 795471735151607910400 : ℝ) ≤ (2506359988341649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (139421 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_416 : rowCell 4 416 ≤ (77675006255401 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (704904264500923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2506359988341649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_416_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_416_1
  · norm_num [gridPoint]

theorem exp_4_417_0 : expNegUpper (81970832428895954598011 / 798169736082100326400 : ℝ) ≤ (2506359887681233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (139421 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_417_1 : expNegUpper (205162270713755883580343 / 1995424340205250816000 : ℝ) ≤ (2227694027220901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (279099 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_417 : rowCell 4 417 ≤ (86302866181557 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2506359887681233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2227694027220901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_417_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_417_1
  · norm_num [gridPoint]

theorem exp_4_418_0 : expNegUpper (205856941468239984181927 / 2002180761684359424000 : ℝ) ≤ (445538787671117 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (279099 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_418_1 : expNegUpper (412186232956809878623813 / 4004361523368718848000 : ℝ) ≤ (1979824208300279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (44697 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_418 : rowCell 4 418 ≤ (306816003446231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (445538787671117 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1979824208300279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_418_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_418_1
  · norm_num [gridPoint]

theorem exp_4_419_0 : expNegUpper (16543180770846138436613 / 160715888185307648000 : ℝ) ≤ (247478016231807 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (44697 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_419_1 : expNegUpper (4140538433595608361743 / 40178972046326912000 : ℝ) ≤ (43984223996147 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (139807 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_419 : rowCell 4 419 ≤ (272665319532241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (247478016231807 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43984223996147 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_419_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_419_1
  · norm_num [gridPoint]

theorem exp_4_420_0 : expNegUpper (103862770285209724343383 / 1007863931050604672000 : ℝ) ≤ (879684445301789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (139807 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_420_1 : expNegUpper (415927382628103286541211 / 4031455724202418688000 : ℝ) ≤ (1563315493353341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1119489 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_420 : rowCell 4 420 ≤ (24229313050239 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (879684445301789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1563315493353341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_420_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_420_1
  · norm_num [gridPoint]

theorem exp_4_421_0 : expNegUpper (417328578537874924467539 / 4045037082077901312000 : ℝ) ≤ (1563315432239791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1119489 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_421_1 : expNegUpper (41780686075477587645361 / 404503708207790131200 : ℝ) ≤ (34724496943261 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2241047 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_421 : rowCell 4 421 ≤ (215284026455847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1563315432239791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34724496943261 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_421_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_421_1
  · norm_num [gridPoint]

theorem exp_4_422_0 : expNegUpper (1352296843401936093311 / 13092391220190771200 : ℝ) ≤ (277795964759153 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2241047 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_422_1 : expNegUpper (13538460894577975891631 / 130923912201907712000 : ℝ) ≤ (616985701171449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28039 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_422 : rowCell 4 422 ≤ (95633979983887 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (277795964759153 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (616985701171449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_422_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_422_1
  · norm_num [gridPoint]

theorem exp_4_423_0 : expNegUpper (421101419883353337479209 / 4072268312746131968000 : ℝ) ≤ (616985677373839 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28039 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_423_1 : expNegUpper (52697959193983257728891 / 509033539093266496000 : ℝ) ≤ (1096160772063329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (561299 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_423 : rowCell 4 423 ≤ (84957664082571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (616985677373839 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1096160772063329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_423_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_423_1
  · norm_num [gridPoint]

theorem exp_4_424_0 : expNegUpper (3678232902751939277 / 35529723352512000 : ℝ) ≤ (34255022814557 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (561299 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_424_1 : expNegUpper (29459549788310327009 / 284237786820096000 : ℝ) ≤ (38946069027607 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (561819 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_424 : rowCell 4 424 ≤ (18866572983857 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34255022814557 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38946069027607 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_424_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_424_1
  · norm_num [gridPoint]

theorem exp_4_425_0 : expNegUpper (424898123246297873782847 / 4099590896637383168000 : ℝ) ≤ (973651688635011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (561819 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_425_1 : expNegUpper (212692180844770283069683 / 2049795448318691584000 : ℝ) ≤ (172951142457831 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2249359 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_425 : rowCell 4 425 ≤ (6702915968477 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (973651688635011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (172951142457831 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_425_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_425_1
  · norm_num [gridPoint]

theorem exp_4_426_0 : expNegUpper (213402724082583277495907 / 2056643223020820736000 : ℝ) ≤ (864755679597323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2249359 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_426_1 : expNegUpper (85458736798388710943033 / 822657289208328294400 : ℝ) ≤ (153593859735141 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1125723 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_426 : rowCell 4 426 ≤ (119059772317017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (864755679597323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (153593859735141 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_426_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_426_1
  · norm_num [gridPoint]

theorem exp_4_427_0 : expNegUpper (85743753713083541442193 / 825400966750330982400 : ℝ) ≤ (383984634917853 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1125723 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_427_1 : expNegUpper (107302251276627140802709 / 1031751208437913728000 : ℝ) ≤ (681954015870987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (70423 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_427 : rowCell 4 427 ≤ (21145941731837 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (383984634917853 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (681954015870987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_427_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_427_1
  · norm_num [gridPoint]

theorem exp_4_428_0 : expNegUpper (107659523609847494292341 / 1035186514941855872000 : ℝ) ≤ (136390798086201 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (70423 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_428_1 : expNegUpper (431130335025574238355443 / 4140746059767423488000 : ℝ) ≤ (605518383346621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (225563 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_428 : rowCell 4 428 ≤ (46941821104663 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (136390798086201 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (605518383346621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_428_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_428_1
  · norm_num [gridPoint]

theorem exp_4_429_0 : expNegUpper (17302537431176880463843 / 166180404963557888000 : ℝ) ≤ (121103672181517 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (225563 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_429_1 : expNegUpper (8661153674829584537561 / 83090202481778944000 : ℝ) ≤ (268800938800627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (35277 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_429 : rowCell 4 429 ≤ (41678677407077 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (121103672181517 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (268800938800627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_429_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_429_1
  · norm_num [gridPoint]

theorem exp_4_430_0 : expNegUpper (217247401288926228610081 / 2084148513358113024000 : ℝ) ≤ (134400464452679 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (35277 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_430_1 : expNegUpper (434991061246562175507721 / 4168297026716226048000 : ℝ) ≤ (238630318211979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2259829 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_430 : rowCell 4 430 ≤ (14800936974023 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (134400464452679 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (238630318211979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_430_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_430_1
  · norm_num [gridPoint]

theorem exp_4_431_0 : expNegUpper (436432204827019960770689 / 4182106767649260032000 : ℝ) ≤ (19090424758827 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2259829 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_431_1 : expNegUpper (5461630969164521637169 / 52276334595615750400 : ℝ) ≤ (42365471239869 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2261933 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_431 : rowCell 4 431 ≤ (65695555379573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19090424758827 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42365471239869 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_431_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_431_1
  · norm_num [gridPoint]

theorem exp_4_432_0 : expNegUpper (5479695656490789612209 / 52449241836100614400 : ℝ) ≤ (211827348503913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2261933 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_432_1 : expNegUpper (438875942593616540004511 / 4195939346888049152000 : ℝ) ≤ (23502294316439 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2264041 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_432 : rowCell 4 432 ≤ (11662843160687 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (211827348503913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23502294316439 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_432_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_432_1
  · norm_num [gridPoint]

theorem exp_4_433_0 : expNegUpper (440325155646920728567319 / 4209794764432593408000 : ℝ) ≤ (376036695491913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2264041 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_433_1 : expNegUpper (220413733210132624664879 / 2104897382216296704000 : ℝ) ≤ (66748330179479 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2266153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_433 : rowCell 4 433 ≤ (3234854669387 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (376036695491913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (66748330179479 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_433_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_433_1
  · norm_num [gridPoint]

theorem exp_4_434_0 : expNegUpper (8845614484046625725431 / 84473460405657856000 : ℝ) ≤ (83435409732949 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2266153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_434_1 : expNegUpper (17711402360217860227133 / 168946920811315712000 : ℝ) ≤ (29617795420711 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (567067 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_434 : rowCell 4 434 ≤ (22967151337537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (83435409732949 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29617795420711 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_434_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_434_1
  · norm_num [gridPoint]

theorem exp_4_435_0 : expNegUpper (444242368177833488818477 / 4237574114438947328000 : ℝ) ≤ (296177943657889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (567067 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_435_1 : expNegUpper (111187182585374738944819 / 1059393528609736832000 : ℝ) ≤ (262819380164827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1135193 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_435 : rowCell 4 435 ≤ (40762587077311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (296177943657889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (262819380164827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_435_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_435_1
  · norm_num [gridPoint]

theorem exp_4_436_0 : expNegUpper (111552524391441495734291 / 1062874511725189248000 : ℝ) ≤ (262819370865031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1135193 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_436_1 : expNegUpper (17868739616830449854467 / 170059921876030279680 : ℝ) ≤ (46639572796437 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (568127 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_436 : rowCell 4 436 ≤ (4521252800693 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (262819370865031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (46639572796437 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_436_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_436_1
  · norm_num [gridPoint]

theorem exp_4_437_0 : expNegUpper (17927356894338696614267 / 170617792706732871680 : ℝ) ≤ (29149731973057 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (568127 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_437_1 : expNegUpper (224347174617786012077293 / 2132722408834160896000 : ℝ) ≤ (51724281383377 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1137317 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_437 : rowCell 4 437 ≤ (32092121435541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29149731973057 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51724281383377 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_437_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_437_1
  · norm_num [gridPoint]

theorem exp_4_438_0 : expNegUpper (225081926274138216403037 / 2139707213370820864000 : ℝ) ≤ (51724279576947 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1137317 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_438_1 : expNegUpper (450676316778269935887073 / 4279414426741641728000 : ℝ) ≤ (36709395380699 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2276763 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_438 : rowCell 4 438 ≤ (3558941776553 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (51724279576947 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36709395380699 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_438_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_438_1
  · norm_num [gridPoint]

theorem exp_4_439_0 : expNegUpper (18085995925101267280577 / 171736274964828672000 : ℝ) ≤ (183546970535011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2276763 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_439_1 : expNegUpper (2263322015205968141441 / 21467034370603584000 : ℝ) ≤ (81409125700643 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455779 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_439 : rowCell 4 439 ≤ (25257263171099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (183546970535011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (81409125700643 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_439_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_439_1
  · norm_num [gridPoint]

theorem exp_4_440_0 : expNegUpper (56767758636071476213849 / 538427769975693376000 : ℝ) ≤ (81409122894377 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455779 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_440_1 : expNegUpper (454658618016681748087031 / 4307422159805547008000 : ℝ) ≤ (14441828668877 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2281031 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_440 : rowCell 4 440 ≤ (5600990995271 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (81409122894377 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14441828668877 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_440_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_440_1
  · norm_num [gridPoint]

theorem exp_4_441_0 : expNegUpper (456140375423735462624239 / 4321460283796132352000 : ℝ) ≤ (72209140871411 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2281031 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_441_1 : expNegUpper (45665897169707294201263 / 432146028379613235200 : ℝ) ≤ (320217254783 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2283171 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_441 : rowCell 4 441 ≤ (9935661410537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (72209140871411 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (320217254783 / 2500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_441_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_441_1
  · norm_num [gridPoint]

theorem exp_4_442_0 : expNegUpper (45814482712536128748383 / 433552124609247283200 : ℝ) ≤ (12808689755499 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2283171 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_442_1 : expNegUpper (458665474074705856794061 / 4335521246092472832000 : ℝ) ≤ (4543712608169 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1142657 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_442 : rowCell 4 442 ≤ (17623501788519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12808689755499 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4543712608169 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_442_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_442_1
  · norm_num [gridPoint]

theorem exp_4_443_0 : expNegUpper (460155434185787931018629 / 4349605046694568448000 : ℝ) ≤ (3549775355131 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1142657 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_443_1 : expNegUpper (115169533785479784790097 / 1087401261673642112000 : ℝ) ≤ (50365226837429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114373 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_443 : rowCell 4 443 ≤ (7814322521353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3549775355131 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (50365226837429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_443_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_443_1
  · norm_num [gridPoint]

theorem exp_4_444_0 : expNegUpper (4621722065973540399577 / 43637116856024192000 : ℝ) ≤ (50365225145819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114373 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_444_1 : expNegUpper (18507878595642057433627 / 174548467424096768000 : ℝ) ≤ (44658556613907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2289611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_444 : rowCell 4 444 ≤ (13858439077697 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (50365225145819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44658556613907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_444_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_444_1
  · norm_num [gridPoint]

theorem exp_4_445_0 : expNegUpper (464195154352398261030107 / 4377841162816025088000 : ℝ) ≤ (89317110247281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2289611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_445_1 : expNegUpper (232360986657220696781993 / 2188920581408012544000 : ℝ) ≤ (79190430078381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (572941 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_445 : rowCell 4 445 ≤ (12287721234041 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (89317110247281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (79190430078381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_445_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_445_1
  · norm_num [gridPoint]

theorem exp_4_446_0 : expNegUpper (233112143721629620482457 / 2195996739167693056000 : ℝ) ≤ (15838085490559 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (572941 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_446_1 : expNegUpper (93350634080885531811877 / 878398695667077222400 : ℝ) ≤ (70206130021099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2293921 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_446 : rowCell 4 446 ≤ (5447065597233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15838085490559 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (70206130021099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_446_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_446_1
  · norm_num [gridPoint]

theorem exp_4_447_0 : expNegUpper (4071822746628483708619 / 38314509844873932800 : ℝ) ≤ (35103063854177 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2293921 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_447_1 : expNegUpper (318471852006351140663 / 2993321081630776000 : ℝ) ≤ (1555900628561 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1148041 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_447 : rowCell 4 447 ≤ (9657800776877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35103063854177 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1555900628561 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_447_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_447_1
  · norm_num [gridPoint]

theorem sum_4_416_2 : blockSum (rowCell 4) 416 2 ≤ (733586496003233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_416) (by simpa only [blockSum_one] using cell_4_417) (by norm_num)

theorem sum_4_418_2 : blockSum (rowCell 4) 418 2 ≤ (72435165372309 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_418) (by simpa only [blockSum_one] using cell_4_419) (by norm_num)

theorem sum_4_416_4 : blockSum (rowCell 4) 416 4 ≤ (262613563796341 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_416_2 sum_4_418_2 (by norm_num)

theorem sum_4_420_2 : blockSum (rowCell 4) 420 2 ≤ (457577156958237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_420) (by simpa only [blockSum_one] using cell_4_421) (by norm_num)

theorem sum_4_422_2 : blockSum (rowCell 4) 422 2 ≤ (90295822033229 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_422) (by simpa only [blockSum_one] using cell_4_423) (by norm_num)

theorem sum_4_420_4 : blockSum (rowCell 4) 420 4 ≤ (818760445091153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_420_2 sum_4_422_2 (by norm_num)

theorem sum_4_416_8 : blockSum (rowCell 4) 416 8 ≤ (1065914132036429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_416_4 sum_4_420_4 (by norm_num)

theorem sum_4_424_2 : blockSum (rowCell 4) 424 2 ≤ (71247725810099 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_424) (by simpa only [blockSum_one] using cell_4_425) (by norm_num)

theorem sum_4_426_2 : blockSum (rowCell 4) 426 2 ≤ (112394740488101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_426) (by simpa only [blockSum_one] using cell_4_427) (by norm_num)

theorem sum_4_424_4 : blockSum (rowCell 4) 424 4 ≤ (254890192108299 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_424_2 sum_4_426_2 (by norm_num)

theorem sum_4_428_2 : blockSum (rowCell 4) 428 2 ≤ (4431024925587 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_428) (by simpa only [blockSum_one] using cell_4_429) (by norm_num)

theorem sum_4_430_2 : blockSum (rowCell 4) 430 2 ≤ (17462530031211 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_430) (by simpa only [blockSum_one] using cell_4_431) (by norm_num)

theorem sum_4_428_4 : blockSum (rowCell 4) 428 4 ≤ (19808827329573 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_428_2 sum_4_430_2 (by norm_num)

theorem sum_4_424_8 : blockSum (rowCell 4) 424 8 ≤ (413360810744883 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_424_4 sum_4_428_4 (by norm_num)

theorem sum_4_416_16 : blockSum (rowCell 4) 416 16 ≤ (11556835490479 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_416_8 sum_4_424_8 (by norm_num)

theorem sum_4_432_2 : blockSum (rowCell 4) 432 2 ≤ (110071890513627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_432) (by simpa only [blockSum_one] using cell_4_433) (by norm_num)

theorem sum_4_434_2 : blockSum (rowCell 4) 434 2 ≤ (17339377950477 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_434) (by simpa only [blockSum_one] using cell_4_435) (by norm_num)

theorem sum_4_432_4 : blockSum (rowCell 4) 432 4 ≤ (49192195066503 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_432_2 sum_4_434_2 (by norm_num)

theorem sum_4_436_2 : blockSum (rowCell 4) 436 2 ≤ (13652428768217 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_436) (by simpa only [blockSum_one] using cell_4_437) (by norm_num)

theorem sum_4_438_2 : blockSum (rowCell 4) 438 2 ≤ (53728797383523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_438) (by simpa only [blockSum_one] using cell_4_439) (by norm_num)

theorem sum_4_436_4 : blockSum (rowCell 4) 436 4 ≤ (3812216913269 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_436_2 sum_4_438_2 (by norm_num)

theorem sum_4_432_8 : blockSum (rowCell 4) 432 8 ≤ (15937986074531 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_432_4 sum_4_436_4 (by norm_num)

theorem sum_4_440_2 : blockSum (rowCell 4) 440 2 ≤ (21137643401079 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_440) (by simpa only [blockSum_one] using cell_4_441) (by norm_num)

theorem sum_4_442_2 : blockSum (rowCell 4) 442 2 ≤ (1330085873249 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_442) (by simpa only [blockSum_one] using cell_4_443) (by norm_num)

theorem sum_4_440_4 : blockSum (rowCell 4) 440 4 ≤ (75527433633383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_440_2 sum_4_442_2 (by norm_num)

theorem sum_4_444_2 : blockSum (rowCell 4) 444 2 ≤ (13073080155869 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_444) (by simpa only [blockSum_one] using cell_4_445) (by norm_num)

theorem sum_4_446_2 : blockSum (rowCell 4) 446 2 ≤ (20551931971343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_446) (by simpa only [blockSum_one] using cell_4_447) (by norm_num)

theorem sum_4_444_4 : blockSum (rowCell 4) 444 4 ≤ (46698092283081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_444_2 sum_4_446_2 (by norm_num)

theorem sum_4_440_8 : blockSum (rowCell 4) 440 8 ≤ (7639095369779 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_440_4 sum_4_444_4 (by norm_num)

theorem sum_4_432_16 : blockSum (rowCell 4) 432 16 ≤ (110246311851771 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_432_8 sum_4_440_8 (by norm_num)

theorem sum_4_416_32 : blockSum (rowCell 4) 416 32 ≤ (849883783242427 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_416_16 sum_4_432_16 (by norm_num)

#print axioms sum_4_416_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
