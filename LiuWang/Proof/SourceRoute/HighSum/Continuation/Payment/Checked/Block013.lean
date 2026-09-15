import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_416_0 : expNegUpper (12301975973922544627027 / 124292458617438736000 : ℝ) ≤ (103677354065809983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2166797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_416_1 : expNegUpper (78831183097953763011171 / 795471735151607910400 : ℝ) ≤ (2289954661783449 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (433779 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_416 : rowCell 0 416 ≤ (88997924117733 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (103677354065809983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2289954661783449 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_416_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_416_1
  · norm_num [gridPoint]

theorem exp_0_417_0 : expNegUpper (79098554791890642598011 / 798169736082100326400 : ℝ) ≤ (18319636718460761 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (433779 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_417_1 : expNegUpper (197993712845109483580343 / 1995424340205250816000 : ℝ) ≤ (40460158935406343 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (542749 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_417 : rowCell 0 417 ≤ (12580204123781613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18319636718460761 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40460158935406343 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_417_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_417_1
  · norm_num [gridPoint]

theorem exp_0_418_0 : expNegUpper (22073790127984424909103 / 222464529076039936000 : ℝ) ≤ (40460157672273569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (542749 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_418_1 : expNegUpper (44202760530198146513757 / 444929058152079872000 : ℝ) ≤ (14296383587281947 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2173101 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_418 : rowCell 0 418 ≤ (11113307774728839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (40460157672273569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14296383587281947 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_418_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_418_1
  · norm_num [gridPoint]

theorem exp_0_419_0 : expNegUpper (15966783447626375236613 / 160715888185307648000 : ℝ) ≤ (35740957859913221 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2173101 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_419_1 : expNegUpper (3996681827268005161743 / 40178972046326912000 : ℝ) ≤ (63139754198411663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2175209 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_419 : rowCell 0 419 ≤ (981673311959449 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35740957859913221 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (63139754198411663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_419_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_419_1
  · norm_num [gridPoint]

theorem exp_0_420_0 : expNegUpper (100254218903152764343383 / 1007863931050604672000 : ℝ) ≤ (63139752253669047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2175209 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_420_1 : expNegUpper (401517449547609206541211 / 4031455724202418688000 : ℝ) ≤ (55767068040241179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (54433 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_420 : rowCell 0 420 ≤ (2167698041544573 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (63139752253669047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (55767068040241179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_420_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_420_1
  · norm_num [gridPoint]

theorem exp_0_421_0 : expNegUpper (44763344506879258274171 / 449448564675322368000 : ℝ) ≤ (11153413266821253 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (54433 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_421_1 : expNegUpper (4481918391406089293929 / 44944856467532236800 : ℝ) ≤ (49251689402727277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1089717 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_421 : rowCell 0 421 ≤ (382903101055913 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11153413266821253 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (49251689402727277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_421_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_421_1
  · norm_num [gridPoint]

theorem exp_0_422_0 : expNegUpper (1305578293648080093311 / 13092391220190771200 : ℝ) ≤ (6156460988252049 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1089717 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_422_1 : expNegUpper (13072058379224375891631 / 130923912201907712000 : ℝ) ≤ (21747183053080009 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (136347 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_422 : rowCell 0 422 ≤ (3381562792550403 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6156460988252049 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21747183053080009 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_422_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_422_1
  · norm_num [gridPoint]

theorem exp_0_423_0 : expNegUpper (406594397011924217479209 / 4072268312746131968000 : ℝ) ≤ (10873591198311781 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (136347 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_423_1 : expNegUpper (50887615391021337728891 / 509033539093266496000 : ℝ) ≤ (4800910436925483 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2183673 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_423 : rowCell 0 423 ≤ (1194468355344113 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10873591198311781 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4800910436925483 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_423_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_423_1
  · norm_num [gridPoint]

theorem exp_0_424_0 : expNegUpper (9077010855495780819 / 90798181900864000 : ℝ) ≤ (38407282343788367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2183673 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_424_1 : expNegUpper (72706489837427881023 / 726385455206912000 : ℝ) ≤ (33912752847106837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2185797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_424 : rowCell 0 424 ≤ (329602621321981 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38407282343788367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33912752847106837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_424_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_424_1
  · norm_num [gridPoint]

theorem exp_0_425_0 : expNegUpper (410342555479401233782847 / 4099590896637383168000 : ℝ) ≤ (6782550367406741 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2185797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_425_1 : expNegUpper (205426533185188843069683 / 2049795448318691584000 : ℝ) ≤ (29942049406149631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (87517 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_425 : rowCell 0 425 ≤ (4656349476200921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6782550367406741 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29942049406149631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_425_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_425_1
  · norm_num [gridPoint]

theorem exp_0_426_0 : expNegUpper (206112803975268077495907 / 2056643223020820736000 : ℝ) ≤ (29942048520275523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (87517 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_426_1 : expNegUpper (82547623245009382943033 / 822657289208328294400 : ℝ) ≤ (2643438307486801 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (438011 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_426 : rowCell 0 426 ≤ (256938752663633 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29942048520275523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2643438307486801 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_426_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_426_1
  · norm_num [gridPoint]

theorem exp_0_427_0 : expNegUpper (9202547908956745493577 / 91711218527814553600 : ℝ) ≤ (5286876459593571 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (438011 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_427_1 : expNegUpper (11517476802552171200301 / 114639023159768192000 : ℝ) ≤ (11667993346727373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2192189 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_427 : rowCell 0 427 ≤ (3629300022420427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5286876459593571 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11667993346727373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_427_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_427_1
  · norm_num [gridPoint]

theorem exp_0_428_0 : expNegUpper (104002427332323014292341 / 1035186514941855872000 : ℝ) ≤ (23335986012163899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2192189 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_428_1 : expNegUpper (416526222363210078355443 / 4140746059767423488000 : ℝ) ≤ (20599308550172677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2194327 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_428 : rowCell 0 428 ≤ (50059393009403 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23335986012163899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20599308550172677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_428_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_428_1
  · norm_num [gridPoint]

theorem exp_0_429_0 : expNegUpper (16716431128863613263843 / 166180404963557888000 : ℝ) ≤ (10299653976380171 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2194327 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_429_1 : expNegUpper (8368585972627626137561 / 83090202481778944000 : ℝ) ≤ (18182297269489233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (549117 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_429 : rowCell 0 429 ≤ (2827989495654881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10299653976380171 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18182297269489233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_429_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_429_1
  · norm_num [gridPoint]

theorem exp_0_430_0 : expNegUpper (23323215142904834290009 / 231572057039790336000 : ℝ) ≤ (9091148372829697 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (549117 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_430_1 : expNegUpper (46704267076525610611969 / 463144114079580672000 : ℝ) ≤ (8023884283116881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2198611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_430 : rowCell 0 430 ≤ (2496087116117553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9091148372829697 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8023884283116881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_430_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_430_1
  · norm_num [gridPoint]

theorem exp_0_431_0 : expNegUpper (421731002373720760770689 / 4182106767649260032000 : ℝ) ≤ (16047768106950267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2198611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_431_1 : expNegUpper (5278169344094953637169 / 52276334595615750400 : ℝ) ≤ (442588891977753 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2200759 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_431 : rowCell 0 431 ≤ (440597003360537 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16047768106950267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (442588891977753 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_431_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_431_1
  · norm_num [gridPoint]

theorem exp_0_432_0 : expNegUpper (5295627220227877612209 / 52449241836100614400 : ℝ) ≤ (14162844140621011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2200759 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_432_1 : expNegUpper (424174740140317340004511 / 4195939346888049152000 : ℝ) ≤ (12498457265960251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2202909 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_432 : rowCell 0 432 ≤ (1944166052080889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14162844140621011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12498457265960251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_432_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_432_1
  · norm_num [gridPoint]

theorem exp_0_433_0 : expNegUpper (47286156477572667618591 / 467754973825843712000 : ℝ) ≤ (12498456912950871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2202909 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_433_1 : expNegUpper (23672332862179571629431 / 233877486912921856000 : ℝ) ≤ (551445464150431 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2205063 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_433 : rowCell 0 433 ≤ (1715636680877433 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12498456912950871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (551445464150431 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_433_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_433_1
  · norm_num [gridPoint]

theorem exp_0_434_0 : expNegUpper (8550134088116616125431 / 84473460405657856000 : ℝ) ≤ (5514454486775453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2205063 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_434_1 : expNegUpper (17121412466267191427133 / 168946920811315712000 : ℝ) ≤ (1946296919113797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110361 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_434 : rowCell 0 434 ≤ (4730832971801 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5514454486775453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1946296919113797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_434_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_434_1
  · norm_num [gridPoint]

theorem exp_0_435_0 : expNegUpper (429444075933599248818477 / 4237574114438947328000 : ℝ) ≤ (486574216215271 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110361 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_435_1 : expNegUpper (107493677636249618944819 / 1059393528609736832000 : ℝ) ≤ (2146526078200467 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110469 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_435 : rowCell 0 435 ≤ (267147004125281 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (486574216215271 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2146526078200467 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_435_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_435_1
  · norm_num [gridPoint]

theorem exp_0_436_0 : expNegUpper (11982987024272166192699 / 118097167969465472000 : ℝ) ≤ (1073263009378999 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110469 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_436_1 : expNegUpper (1919645325229008917163 / 18895546875114475520 : ℝ) ≤ (1515004377484607 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (276443 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_436 : rowCell 0 436 ≤ (294620956235957 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1073263009378999 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1515004377484607 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_436_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_436_1
  · norm_num [gridPoint]

theorem exp_0_437_0 : expNegUpper (17333483408750626214267 / 170617792706732871680 : ℝ) ≤ (7575021679023117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (276443 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_437_1 : expNegUpper (216935892271802012077293 / 2132722408834160896000 : ℝ) ≤ (6682553404736583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2213711 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_437 : rowCell 0 437 ≤ (16244924760123 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7575021679023117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6682553404736583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_437_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_437_1
  · norm_num [gridPoint]

theorem exp_0_438_0 : expNegUpper (217646371480420456403037 / 2139707213370820864000 : ℝ) ≤ (3341276611044543 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2213711 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_438_1 : expNegUpper (435829479638568175887073 / 4279414426741641728000 : ℝ) ≤ (5894838913649871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2215881 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_438 : rowCell 0 438 ≤ (57322170908677 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3341276611044543 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5894838913649871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_438_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_438_1
  · norm_num [gridPoint]

theorem exp_0_439_0 : expNegUpper (1943353404854944008953 / 19081808329425408000 : ℝ) ≤ (1178967750716301 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2215881 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_439_1 : expNegUpper (243218496363198949049 / 2385226041178176000 : ℝ) ≤ (5199631244780193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (443611 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_439 : rowCell 0 439 ≤ (32360748798737 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1178967750716301 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5199631244780193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_439_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_439_1
  · norm_num [gridPoint]

theorem exp_0_440_0 : expNegUpper (54902801825708596213849 / 538427769975693376000 : ℝ) ≤ (324976944031721 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (443611 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_440_1 : expNegUpper (439763235981512468087031 / 4307422159805547008000 : ℝ) ≤ (2293054582855061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2220231 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_440 : rowCell 0 440 ≤ (89198121547537 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (324976944031721 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2293054582855061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_440_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_440_1
  · norm_num [gridPoint]

theorem exp_0_441_0 : expNegUpper (441196448493098662624239 / 4321460283796132352000 : ℝ) ≤ (4586109042791867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2220231 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_441_1 : expNegUpper (44173931721416990201263 / 432146028379613235200 : ℝ) ≤ (4044712082526157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (555603 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_441 : rowCell 0 441 ≤ (314683615355773 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4586109042791867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4044712082526157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_441_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_441_1
  · norm_num [gridPoint]

theorem exp_0_442_0 : expNegUpper (4924184752744341416487 / 48172458289916364800 : ℝ) ≤ (404471197482119 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (555603 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_442_1 : expNegUpper (49302394127118784088229 / 481724582899163648000 : ℝ) ≤ (891748453787129 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444919 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_442 : rowCell 0 442 ≤ (34690776552907 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (404471197482119 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (891748453787129 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_442_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_442_1
  · norm_num [gridPoint]

theorem exp_0_443_0 : expNegUpper (445162962359683611018629 / 4349605046694568448000 : ℝ) ≤ (44587421509739 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444919 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_443_1 : expNegUpper (111427483940887144790097 / 1087401261673642112000 : ℝ) ≤ (3145493256215249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2226781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_443 : rowCell 0 443 ≤ (3824067039941 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (44587421509739 / 12500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3145493256215249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_443_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_443_1
  · norm_num [gridPoint]

theorem exp_0_444_0 : expNegUpper (4471554623235159599577 / 43637116856024192000 : ℝ) ≤ (3145493173534797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2226781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_444_1 : expNegUpper (17908179722597884633627 / 174548467424096768000 : ℝ) ≤ (1386809986747297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2228971 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_444 : rowCell 0 444 ≤ (215813524317301 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3145493173534797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1386809986747297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_444_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_444_1
  · norm_num [gridPoint]

theorem exp_0_445_0 : expNegUpper (49906015292314046781123 / 486426795868447232000 : ℝ) ≤ (2773619901059193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2228971 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_445_1 : expNegUpper (24983623835589072975777 / 243213397934223616000 : ℝ) ≤ (2445553037582409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (446233 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_445 : rowCell 0 445 ≤ (380586779786433 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2773619901059193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2445553037582409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_445_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_445_1
  · norm_num [gridPoint]

theorem exp_0_446_0 : expNegUpper (225579499136976820482457 / 2195996739167693056000 : ℝ) ≤ (2445552974126019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (446233 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_446_1 : expNegUpper (90342430736571163811877 / 878398695667077222400 : ℝ) ≤ (1078075776603851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2233361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_446 : rowCell 0 446 ≤ (335560428477087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2445552974126019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1078075776603851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_446_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_446_1
  · norm_num [gridPoint]

theorem exp_0_447_0 : expNegUpper (90634010849047253298237 / 881233726432100454400 : ℝ) ≤ (2156151497620291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2233361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_447_1 : expNegUpper (7089457452875676235249 / 68846384877507848000 : ℝ) ≤ (1900875546669223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2235561 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_447 : rowCell 0 447 ≤ (295842057054827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2156151497620291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1900875546669223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_447_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_447_1
  · norm_num [gridPoint]

theorem sum_0_416_2 : blockSum (rowCell 0) 416 2 ≤ (26819871982618893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_416) (by simpa only [blockSum_one] using cell_0_417) (by norm_num)

theorem sum_0_418_2 : blockSum (rowCell 0) 418 2 ≤ (20930040894323329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_418) (by simpa only [blockSum_one] using cell_0_419) (by norm_num)

theorem sum_0_416_4 : blockSum (rowCell 0) 416 4 ≤ (23874956438471111 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_416_2 sum_0_418_2 (by norm_num)

theorem sum_0_420_2 : blockSum (rowCell 0) 420 2 ≤ (2041106773412069 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_420) (by simpa only [blockSum_one] using cell_0_421) (by norm_num)

theorem sum_0_422_2 : blockSum (rowCell 0) 422 2 ≤ (12735467361821371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_422) (by simpa only [blockSum_one] using cell_0_423) (by norm_num)

theorem sum_0_420_4 : blockSum (rowCell 0) 420 4 ≤ (29064321549117923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_420_2 sum_0_422_2 (by norm_num)

theorem sum_0_416_8 : blockSum (rowCell 0) 416 8 ≤ (15362846885212029 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_416_4 sum_0_420_4 (by norm_num)

theorem sum_0_424_2 : blockSum (rowCell 0) 424 2 ≤ (9929991417352617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_424) (by simpa only [blockSum_one] using cell_0_425) (by norm_num)

theorem sum_0_426_2 : blockSum (rowCell 0) 426 2 ≤ (1548064013007711 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_426) (by simpa only [blockSum_one] using cell_0_427) (by norm_num)

theorem sum_0_424_4 : blockSum (rowCell 0) 424 4 ≤ (4417577870597793 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_424_2 sum_0_426_2 (by norm_num)

theorem sum_0_428_2 : blockSum (rowCell 0) 428 2 ≤ (6031790648256673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_428) (by simpa only [blockSum_one] using cell_0_429) (by norm_num)

theorem sum_0_430_2 : blockSum (rowCell 0) 430 2 ≤ (2349536066460119 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_430) (by simpa only [blockSum_one] using cell_0_431) (by norm_num)

theorem sum_0_428_4 : blockSum (rowCell 0) 428 4 ≤ (10730862781176911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_428_2 sum_0_430_2 (by norm_num)

theorem sum_0_424_8 : blockSum (rowCell 0) 424 8 ≤ (28401174263568083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_424_4 sum_0_428_4 (by norm_num)

theorem sum_0_416_16 : blockSum (rowCell 0) 416 16 ≤ (26303852172407057 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_416_8 sum_0_424_8 (by norm_num)

theorem sum_0_432_2 : blockSum (rowCell 0) 432 2 ≤ (1829901366479161 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_432) (by simpa only [blockSum_one] using cell_0_433) (by norm_num)

theorem sum_0_434_2 : blockSum (rowCell 0) 434 2 ≤ (113984062864109 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_434) (by simpa only [blockSum_one] using cell_0_435) (by norm_num)

theorem sum_0_432_4 : blockSum (rowCell 0) 432 4 ≤ (6509404304561047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_432_2 sum_0_434_2 (by norm_num)

theorem sum_0_436_2 : blockSum (rowCell 0) 436 2 ≤ (22181590095917 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_436) (by simpa only [blockSum_one] using cell_0_437) (by norm_num)

theorem sum_0_438_2 : blockSum (rowCell 0) 438 2 ≤ (1726173454507257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_438) (by simpa only [blockSum_one] using cell_0_439) (by norm_num)

theorem sum_0_436_4 : blockSum (rowCell 0) 436 4 ≤ (3944332464098957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_436_2 sum_0_438_2 (by norm_num)

theorem sum_0_432_8 : blockSum (rowCell 0) 432 8 ≤ (2613434192165001 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_432_4 sum_0_436_4 (by norm_num)

theorem sum_0_440_2 : blockSum (rowCell 0) 440 2 ≤ (671476101545921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_440) (by simpa only [blockSum_one] using cell_0_441) (by norm_num)

theorem sum_0_442_2 : blockSum (rowCell 0) 442 2 ≤ (13056662574487 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_442) (by simpa only [blockSum_one] using cell_0_443) (by norm_num)

theorem sum_0_440_4 : blockSum (rowCell 0) 440 4 ≤ (1193742604525401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_440_2 sum_0_442_2 (by norm_num)

theorem sum_0_444_2 : blockSum (rowCell 0) 444 2 ≤ (162442765684207 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_444) (by simpa only [blockSum_one] using cell_0_445) (by norm_num)

theorem sum_0_446_2 : blockSum (rowCell 0) 446 2 ≤ (315701242765957 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_446) (by simpa only [blockSum_one] using cell_0_447) (by norm_num)

theorem sum_0_444_4 : blockSum (rowCell 0) 444 4 ≤ (1443616313952949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_444_2 sum_0_446_2 (by norm_num)

theorem sum_0_440_8 : blockSum (rowCell 0) 440 8 ≤ (3831101523003751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_440_4 sum_0_444_4 (by norm_num)

theorem sum_0_432_16 : blockSum (rowCell 0) 432 16 ≤ (2856967658332751 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_432_8 sum_0_440_8 (by norm_num)

theorem sum_0_416_32 : blockSum (rowCell 0) 416 32 ≤ (119500246981291983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_416_16 sum_0_432_16 (by norm_num)

#print axioms sum_0_416_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
