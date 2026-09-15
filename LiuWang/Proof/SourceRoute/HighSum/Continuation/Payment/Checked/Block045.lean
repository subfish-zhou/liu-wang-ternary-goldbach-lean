import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_416_0 : expNegUpper (12570796893996784627027 / 124292458617438736000 : ℝ) ≤ (5961528766839529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2203721 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_416_1 : expNegUpper (80548724292700847811171 / 795471735151607910400 : ℝ) ≤ (5286288044905131 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2205791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_416 : rowCell 2 416 ≤ (65616072589827 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5961528766839529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5286288044905131 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_416_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_416_1
  · norm_num [gridPoint]

theorem exp_2_417_0 : expNegUpper (80821921374093829798011 / 798169736082100326400 : ℝ) ≤ (2643143925529407 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2205791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_417_1 : expNegUpper (202294847566297323580343 / 1995424340205250816000 : ℝ) ≤ (374969848778691 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441573 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_417 : rowCell 2 417 ≤ (181817521936849 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2643143925529407 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (374969848778691 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_417_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_417_1
  · norm_num [gridPoint]

theorem exp_2_418_0 : expNegUpper (9665705206747043818187 / 95341941032588544000 : ℝ) ≤ (4687122939017503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441573 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_418_1 : expNegUpper (19354365603942821648753 / 190683882065177088000 : ℝ) ≤ (16232465773451 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2209943 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_418 : rowCell 2 418 ≤ (40300801796407 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4687122939017503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16232465773451 / 1953125000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_418_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_418_1
  · norm_num [gridPoint]

theorem exp_2_419_0 : expNegUpper (16312621841558233156613 / 160715888185307648000 : ℝ) ≤ (2597194429793 / 312500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2209943 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_419_1 : expNegUpper (4082995791064567081743 / 40178972046326912000 : ℝ) ≤ (3683878638662201 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2212023 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_419 : rowCell 2 419 ≤ (142913835511441 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2597194429793 / 312500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3683878638662201 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_419_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_419_1
  · norm_num [gridPoint]

theorem exp_2_420_0 : expNegUpper (102419349732386940343383 / 1007863931050604672000 : ℝ) ≤ (7367757012571127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2212023 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_420_1 : expNegUpper (410163409395905654541211 / 4031455724202418688000 : ℝ) ≤ (6530991281663269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (553527 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_420 : rowCell 2 420 ≤ (1013509212772243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7367757012571127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6530991281663269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_420_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_420_1
  · norm_num [gridPoint]

theorem exp_2_421_0 : expNegUpper (137181729115830094822513 / 1348345694025967104000 : ℝ) ≤ (408186940534561 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (553527 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_421_1 : expNegUpper (13734439284782824681787 / 134834569402596710400 : ℝ) ≤ (2894383205888197 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (554049 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_421 : rowCell 2 421 ≤ (898367782539311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (408186940534561 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2894383205888197 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_421_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_421_1
  · norm_num [gridPoint]

theorem exp_2_422_0 : expNegUpper (1333609423500393693311 / 13092391220190771200 : ℝ) ≤ (5788766206542257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (554049 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_422_1 : expNegUpper (13351899888436535891631 / 130923912201907712000 : ℝ) ≤ (5130459448244281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2218287 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_422 : rowCell 2 422 ≤ (398119872494417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5788766206542257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5130459448244281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_422_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_422_1
  · norm_num [gridPoint]

theorem exp_2_423_0 : expNegUpper (415298610734781689479209 / 4072268312746131968000 : ℝ) ≤ (2565229633782999 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2218287 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_423_1 : expNegUpper (51973821672798489728891 / 509033539093266496000 : ℝ) ≤ (2273316972675349 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2220381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_423 : rowCell 2 423 ≤ (705662331349319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2565229633782999 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2273316972675349 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_423_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_423_1
  · norm_num [gridPoint]

theorem exp_2_424_0 : expNegUpper (27812284379253857657 / 272394545702592000 : ℝ) ≤ (4546633786301791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2220381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_424_1 : expNegUpper (222761716831140961469 / 2179156365620736000 : ℝ) ≤ (1007227116602247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27781 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_424 : rowCell 2 424 ≤ (625336245656413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4546633786301791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1007227116602247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_424_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_424_1
  · norm_num [gridPoint]

theorem exp_2_425_0 : expNegUpper (59867985162791316826121 / 585655842376769024000 : ℝ) ≤ (40289083264103 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27781 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_425_1 : expNegUpper (29969417397276815295669 / 292827921188384512000 : ℝ) ≤ (892459838188259 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2224581 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_425 : rowCell 2 425 ≤ (554107507764459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (40289083264103 / 10000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (892459838188259 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_425_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_425_1
  · norm_num [gridPoint]

theorem exp_2_426_0 : expNegUpper (210486756039657197495907 / 2056643223020820736000 : ℝ) ≤ (3569839229531691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2224581 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_426_1 : expNegUpper (84294291377036979743033 / 822657289208328294400 : ℝ) ≤ (3162816434543307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1113343 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_426 : rowCell 2 426 ≤ (490951299894673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3569839229531691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3162816434543307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_426_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_426_1
  · norm_num [gridPoint]

theorem exp_2_427_0 : expNegUpper (28191808233364802880731 / 275133655583443660800 : ℝ) ≤ (790704081524123 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1113343 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_427_1 : expNegUpper (35281422418388033600903 / 343917069479304576000 : ℝ) ≤ (1400985132292209 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1114397 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_427 : rowCell 2 427 ≤ (86991519436081 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (790704081524123 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1400985132292209 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_427_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_427_1
  · norm_num [gridPoint]

theorem exp_2_428_0 : expNegUpper (106196685098837702292341 / 1035186514941855872000 : ℝ) ≤ (2801970169147437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1114397 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_428_1 : expNegUpper (425288689960628574355443 / 4140746059767423488000 : ℝ) ≤ (496417922147387 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1115453 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_428 : rowCell 2 428 ≤ (385318386546627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2801970169147437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (496417922147387 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_428_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_428_1
  · norm_num [gridPoint]

theorem exp_2_429_0 : expNegUpper (17068094910251573583843 / 166180404963557888000 : ℝ) ≤ (2482089526755017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1115453 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_429_1 : expNegUpper (8544126593948801177561 / 83090202481778944000 : ℝ) ≤ (2198548080227027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2233021 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_429 : rowCell 2 429 ≤ (341316299561481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2482089526755017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2198548080227027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_429_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_429_1
  · norm_num [gridPoint]

theorem exp_2_430_0 : expNegUpper (71437338429271046870027 / 694716171119371008000 : ℝ) ≤ (68704625197827 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2233021 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_430_1 : expNegUpper (143043332741143167835907 / 1389432342238742016000 : ℝ) ≤ (973619435998437 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (111757 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_430 : rowCell 2 430 ≤ (75578625974507 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (68704625197827 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (973619435998437 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_430_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_430_1
  · norm_num [gridPoint]

theorem exp_2_431_0 : expNegUpper (430551723845700280770689 / 4182106767649260032000 : ℝ) ≤ (486809701744771 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (111757 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_431_1 : expNegUpper (5388246319136694437169 / 52276334595615750400 : ℝ) ≤ (1724516762790369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1118631 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_431 : rowCell 2 431 ≤ (66936928747621 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (486809701744771 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1724516762790369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_431_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_431_1
  · norm_num [gridPoint]

theorem exp_2_432_0 : expNegUpper (772295468855089258887 / 7492748833728659200 : ℝ) ≤ (431129176397137 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1118631 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_432_1 : expNegUpper (61856494516042408572073 / 599419906698292736000 : ℝ) ≤ (763573265179081 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2239387 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_432 : rowCell 2 432 ≤ (237114204581423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (431129176397137 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (763573265179081 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_432_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_432_1
  · norm_num [gridPoint]

theorem exp_2_433_0 : expNegUpper (144808418902471346855773 / 1403264921477531136000 : ℝ) ≤ (1527146480036227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2239387 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_433_1 : expNegUpper (72489546076642010888293 / 701632460738765568000 : ℝ) ≤ (676128552133399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (560379 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_433 : rowCell 2 433 ≤ (41993739266307 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1527146480036227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (676128552133399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_433_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_433_1
  · norm_num [gridPoint]

theorem exp_2_434_0 : expNegUpper (8727422325674621885431 / 84473460405657856000 : ℝ) ≤ (1352257060000337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (560379 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_434_1 : expNegUpper (17475406402637592707133 / 168946920811315712000 : ℝ) ≤ (1197300812447013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2243649 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_434 : rowCell 2 434 ≤ (92958025338631 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1352257060000337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1197300812447013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_434_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_434_1
  · norm_num [gridPoint]

theorem exp_2_435_0 : expNegUpper (438323051280139792818477 / 4237574114438947328000 : ℝ) ≤ (598650386755009 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2243649 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_435_1 : expNegUpper (109709780605724690944819 / 1059393528609736832000 : ℝ) ≤ (530008580416477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (280723 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_435 : rowCell 2 435 ≤ (41151412957843 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (598650386755009 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (530008580416477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_435_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_435_1
  · norm_num [gridPoint]

theorem exp_2_436_0 : expNegUpper (36690089307414898578097 / 354291503908396416000 : ℝ) ≤ (530008563293063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (280723 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_436_1 : expNegUpper (5877322313640900671489 / 56686640625343426560 : ℝ) ≤ (938400645135737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2247923 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_436 : rowCell 2 436 ≤ (72863209683713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (530008563293063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (938400645135737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_436_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_436_1
  · norm_num [gridPoint]

theorem exp_2_437_0 : expNegUpper (17689807500103468454267 / 170617792706732871680 : ℝ) ≤ (938400615016169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2247923 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_437_1 : expNegUpper (221382661679392412077293 / 2132722408834160896000 : ℝ) ≤ (207668037193183 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1125033 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_437 : rowCell 2 437 ≤ (64501187668399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (938400615016169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (207668037193183 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_437_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_437_1
  · norm_num [gridPoint]

theorem exp_2_438_0 : expNegUpper (222107704356651112403037 / 2139707213370820864000 : ℝ) ≤ (830672122284819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1125033 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_438_1 : expNegUpper (444737581922389231887073 / 4279414426741641728000 : ℝ) ≤ (367626764981571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (563053 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_438 : rowCell 2 438 ≤ (456754821793 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (830672122284819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (367626764981571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_438_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_438_1
  · norm_num [gridPoint]

theorem exp_2_439_0 : expNegUpper (849889038692312323837 / 8177917855468032000 : ℝ) ≤ (735253506670567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (563053 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_439_1 : expNegUpper (106360942668147481021 / 1022239731933504000 : ℝ) ≤ (650745044647859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2254361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_439 : rowCell 2 439 ≤ (50534129797607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (735253506670567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (650745044647859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_439_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_439_1
  · norm_num [gridPoint]

theorem exp_2_440_0 : expNegUpper (56021775911926324213849 / 538427769975693376000 : ℝ) ≤ (650745024166529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2254361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_440_1 : expNegUpper (448700465202614036087031 / 4307422159805547008000 : ℝ) ≤ (143976322693791 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1128257 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_440 : rowCell 2 440 ≤ (89448443034191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (650745024166529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (143976322693791 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_440_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_440_1
  · norm_num [gridPoint]

theorem exp_2_441_0 : expNegUpper (450162804651480742624239 / 4321460283796132352000 : ℝ) ≤ (287952636383491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1128257 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_441_1 : expNegUpper (45069110990391172601263 / 432146028379613235200 : ℝ) ≤ (509633394129463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (225867 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_441 : rowCell 2 441 ≤ (15831690975747 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (287952636383491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (509633394129463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_441_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_441_1
  · norm_num [gridPoint]

theorem exp_2_442_0 : expNegUpper (15071918245800435449461 / 144517374869749094400 : ℝ) ≤ (509633378296843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (225867 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_442_1 : expNegUpper (150895967767483712264687 / 1445173748697490944000 : ℝ) ≤ (90190637345669 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226083 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_442 : rowCell 2 442 ≤ (70046835348629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (509633378296843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (90190637345669 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_442_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_442_1
  · norm_num [gridPoint]

theorem exp_2_443_0 : expNegUpper (454158445455346203018629 / 4349605046694568448000 : ℝ) ≤ (14092286650293 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226083 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_443_1 : expNegUpper (113672713847642728790097 / 1087401261673642112000 : ℝ) ≤ (398999156284819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2262993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_443 : rowCell 2 443 ≤ (12395857493319 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14092286650293 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (398999156284819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_443_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_443_1
  · norm_num [gridPoint]

theorem exp_2_444_0 : expNegUpper (4561655088878188079577 / 43637116856024192000 : ℝ) ≤ (79799828809801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2262993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_444_1 : expNegUpper (18267999046424388313627 / 174548467424096768000 : ℝ) ≤ (88250992423363 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2265159 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_444 : rowCell 2 444 ≤ (27418371340949 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (79799828809801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (88250992423363 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_444_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_444_1
  · norm_num [gridPoint]

theorem exp_2_445_0 : expNegUpper (152726249221256508343369 / 1459280387605341696000 : ℝ) ≤ (353003958937959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2265159 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_445_1 : expNegUpper (76452545934151026927331 / 729640193802670848000 : ℝ) ≤ (78071848819591 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2267329 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_445 : rowCell 2 445 ≤ (12128410818039 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (353003958937959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (78071848819591 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_445_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_445_1
  · norm_num [gridPoint]

theorem exp_2_446_0 : expNegUpper (32871297983966928640351 / 313713819881099008000 : ℝ) ≤ (156143692912357 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2267329 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_446_1 : expNegUpper (13163907534737112087411 / 125485527952439603200 : ℝ) ≤ (138123233964929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1134751 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_446 : rowCell 2 446 ≤ (10729104344167 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (156143692912357 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (138123233964929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_446_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_446_1
  · norm_num [gridPoint]

theorem exp_2_447_0 : expNegUpper (92444758243091976498237 / 881233726432100454400 : ℝ) ≤ (69061614905253 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1134751 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_447_1 : expNegUpper (7230694538837916235249 / 68846384877507848000 : ℝ) ≤ (122173379257507 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2271679 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_447 : rowCell 2 447 ≤ (37962125186949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (69061614905253 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (122173379257507 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_447_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_447_1
  · norm_num [gridPoint]

theorem sum_2_416_2 : blockSum (rowCell 2) 416 2 ≤ (3094941990240467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_416) (by simpa only [blockSum_one] using cell_2_417) (by norm_num)

theorem sum_2_418_2 : blockSum (rowCell 2) 418 2 ≤ (304117042697069 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_418) (by simpa only [blockSum_one] using cell_2_419) (by norm_num)

theorem sum_2_416_4 : blockSum (rowCell 2) 416 4 ≤ (5527878331817019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_416_2 sum_2_418_2 (by norm_num)

theorem sum_2_420_2 : blockSum (rowCell 2) 420 2 ≤ (955938497655777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_420) (by simpa only [blockSum_one] using cell_2_421) (by norm_num)

theorem sum_2_422_2 : blockSum (rowCell 2) 422 2 ≤ (1501902076338153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_422) (by simpa only [blockSum_one] using cell_2_423) (by norm_num)

theorem sum_2_420_4 : blockSum (rowCell 2) 420 4 ≤ (3413779071649707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_420_2 sum_2_422_2 (by norm_num)

theorem sum_2_416_8 : blockSum (rowCell 2) 416 8 ≤ (4470828701733363 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_416_4 sum_2_420_4 (by norm_num)

theorem sum_2_424_2 : blockSum (rowCell 2) 424 2 ≤ (147430469177609 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_424) (by simpa only [blockSum_one] using cell_2_425) (by norm_num)

theorem sum_2_426_2 : blockSum (rowCell 2) 426 2 ≤ (462954448537539 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_426) (by simpa only [blockSum_one] using cell_2_427) (by norm_num)

theorem sum_2_424_4 : blockSum (rowCell 2) 424 4 ≤ (42107053009919 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_424_2 sum_2_426_2 (by norm_num)

theorem sum_2_428_2 : blockSum (rowCell 2) 428 2 ≤ (181658671527027 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_428) (by simpa only [blockSum_one] using cell_2_429) (by norm_num)

theorem sum_2_430_2 : blockSum (rowCell 2) 430 2 ≤ (8907222170133 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_430) (by simpa only [blockSum_one] using cell_2_431) (by norm_num)

theorem sum_2_428_4 : blockSum (rowCell 2) 428 4 ≤ (64834845249831 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_428_2 sum_2_430_2 (by norm_num)

theorem sum_2_424_8 : blockSum (rowCell 2) 424 8 ≤ (340204955549257 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_424_4 sum_2_428_4 (by norm_num)

theorem sum_2_416_16 : blockSum (rowCell 2) 416 16 ≤ (192870421233739 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_416_8 sum_2_424_8 (by norm_num)

theorem sum_2_432_2 : blockSum (rowCell 2) 432 2 ≤ (223541450456479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_432) (by simpa only [blockSum_one] using cell_2_433) (by norm_num)

theorem sum_2_434_2 : blockSum (rowCell 2) 434 2 ≤ (175260851254317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_434) (by simpa only [blockSum_one] using cell_2_435) (by norm_num)

theorem sum_2_432_4 : blockSum (rowCell 2) 432 4 ≤ (99700575427699 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_432_2 sum_2_434_2 (by norm_num)

theorem sum_2_436_2 : blockSum (rowCell 2) 436 2 ≤ (8585274834507 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_436) (by simpa only [blockSum_one] using cell_2_437) (by norm_num)

theorem sum_2_438_2 : blockSum (rowCell 2) 438 2 ≤ (26907120630433 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_438) (by simpa only [blockSum_one] using cell_2_439) (by norm_num)

theorem sum_2_436_4 : blockSum (rowCell 2) 436 4 ≤ (61248219968461 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_436_2 sum_2_438_2 (by norm_num)

theorem sum_2_432_8 : blockSum (rowCell 2) 432 8 ≤ (502964985613 / 390625000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_432_4 sum_2_436_4 (by norm_num)

theorem sum_2_440_2 : blockSum (rowCell 2) 440 2 ≤ (84303448956463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_440) (by simpa only [blockSum_one] using cell_2_441) (by norm_num)

theorem sum_2_442_2 : blockSum (rowCell 2) 442 2 ≤ (16503265351903 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_442) (by simpa only [blockSum_one] using cell_2_443) (by norm_num)

theorem sum_2_440_4 : blockSum (rowCell 2) 440 4 ≤ (6012660414563 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_440_2 sum_2_442_2 (by norm_num)

theorem sum_2_444_2 : blockSum (rowCell 2) 444 2 ≤ (51675192977027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_444) (by simpa only [blockSum_one] using cell_2_445) (by norm_num)

theorem sum_2_446_2 : blockSum (rowCell 2) 446 2 ≤ (80878542563617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_446) (by simpa only [blockSum_one] using cell_2_447) (by norm_num)

theorem sum_2_444_4 : blockSum (rowCell 2) 444 4 ≤ (184228928517671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_444_2 sum_2_446_2 (by norm_num)

theorem sum_2_440_8 : blockSum (rowCell 2) 440 8 ≤ (484861949245821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_440_4 sum_2_444_4 (by norm_num)

theorem sum_2_432_16 : blockSum (rowCell 2) 432 16 ≤ (1772452312415101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_432_8 sum_2_440_8 (by norm_num)

theorem sum_2_416_32 : blockSum (rowCell 2) 416 32 ≤ (14116159271374397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_416_16 sum_2_432_16 (by norm_num)

#print axioms sum_2_416_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
