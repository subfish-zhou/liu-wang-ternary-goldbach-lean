import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_416_0 : expNegUpper (12705207354033904627027 / 124292458617438736000 : ℝ) ≤ (808666593519151 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2222417 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_416_1 : expNegUpper (81407494890074390211171 / 795471735151607910400 : ℝ) ≤ (448991174512579 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1112237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_416 : rowCell 3 416 ≤ (556770191366771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (808666593519151 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (448991174512579 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_416_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_416_1
  · norm_num [gridPoint]

theorem exp_3_417_0 : expNegUpper (81683604665195423398011 / 798169736082100326400 : ℝ) ≤ (3591929254977651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1112237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_417_1 : expNegUpper (204445414926891243580343 / 1995424340205250816000 : ℝ) ≤ (3190624857789149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1113267 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_417 : rowCell 3 417 ≤ (123647484900979 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3591929254977651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3190624857789149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_417_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_417_1
  · norm_num [gridPoint]

theorem exp_3_418_0 : expNegUpper (22793073159622440909103 / 222464529076039936000 : ℝ) ≤ (1595312366639153 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1113267 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_418_1 : expNegUpper (45638899348700802513757 / 444929058152079872000 : ℝ) ≤ (708473475867713 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2228597 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_418 : rowCell 3 418 ≤ (109828327911303 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1595312366639153 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (708473475867713 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_418_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_418_1
  · norm_num [gridPoint]

theorem exp_3_419_0 : expNegUpper (16485541038524162116613 / 160715888185307648000 : ℝ) ≤ (2833893793625557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2228597 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_419_1 : expNegUpper (4126152772962848041743 / 40178972046326912000 : ℝ) ≤ (1258408160735127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (278833 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_419 : rowCell 3 419 ≤ (195089294435703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2833893793625557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1258408160735127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_419_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_419_1
  · norm_num [gridPoint]

theorem exp_3_420_0 : expNegUpper (103501915147004028343383 / 1007863931050604672000 : ℝ) ≤ (2516816224570923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (278833 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_420_1 : expNegUpper (414486389320053878541211 / 4031455724202418688000 : ℝ) ≤ (139688214867039 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1116367 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_420 : rowCell 3 420 ≤ (346507542365549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2516816224570923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (139688214867039 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_420_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_420_1
  · norm_num [gridPoint]

theorem exp_3_421_0 : expNegUpper (46209192304475418274171 / 449448564675322368000 : ℝ) ≤ (1117505676200169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1116367 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_421_1 : expNegUpper (4626260446688367693929 / 44944856467532236800 : ℝ) ≤ (1984579367366649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (279351 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_421 : rowCell 3 421 ≤ (153848173161973 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1117505676200169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1984579367366649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_421_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_421_1
  · norm_num [gridPoint]

theorem exp_3_422_0 : expNegUpper (1347624988426550493311 / 13092391220190771200 : ℝ) ≤ (396915858395971 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (279351 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_422_1 : expNegUpper (13491820643042615891631 / 130923912201907712000 : ℝ) ≤ (881024306582093 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1118443 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_422 : rowCell 3 422 ≤ (1067216691227 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (396915858395971 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (881024306582093 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_422_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_422_1
  · norm_num [gridPoint]

theorem exp_3_423_0 : expNegUpper (419650717596210425479209 / 4072268312746131968000 : ℝ) ≤ (881024273339047 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1118443 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_423_1 : expNegUpper (52516924813687065728891 / 509033539093266496000 : ℝ) ≤ (1564329335369563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2238967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_423 : rowCell 3 423 ≤ (30320307962693 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (881024273339047 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1564329335369563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_423_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_423_1
  · norm_num [gridPoint]

theorem exp_3_424_0 : expNegUpper (9367636761879038419 / 90798181900864000 : ℝ) ≤ (782164638368957 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2238967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_424_1 : expNegUpper (75027613496856540223 / 726385455206912000 : ℝ) ≤ (1388671679502351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2241051 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_424 : rowCell 3 424 ≤ (215335482815837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (782164638368957 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1388671679502351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_424_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_424_1
  · norm_num [gridPoint]

theorem exp_3_425_0 : expNegUpper (423442566469608209782847 / 4099590896637383168000 : ℝ) ≤ (13886716278013 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2241051 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_425_1 : expNegUpper (211965616078812139069683 / 2049795448318691584000 : ℝ) ≤ (1232628621594307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2243139 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_425 : rowCell 3 425 ≤ (191147569260371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13886716278013 / 10000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1232628621594307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_425_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_425_1
  · norm_num [gridPoint]

theorem exp_3_426_0 : expNegUpper (212673732071851757495907 / 2056643223020820736000 : ℝ) ≤ (49305143040327 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2243139 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_426_1 : expNegUpper (85167625443050778143033 / 822657289208328294400 : ℝ) ≤ (27350571104417 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224523 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_426 : rowCell 3 426 ≤ (33932302382153 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (49305143040327 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27350571104417 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_426_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_426_1
  · norm_num [gridPoint]

theorem exp_3_427_0 : expNegUpper (9494630162204028693577 / 91711218527814553600 : ℝ) ≤ (218804560797069 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224523 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_427_1 : expNegUpper (11881972807917931200301 / 114639023159768192000 : ℝ) ≤ (970917209260011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (89893 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_427 : rowCell 3 427 ≤ (30115456197079 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (218804560797069 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (970917209260011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_427_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_427_1
  · norm_num [gridPoint]

theorem exp_3_428_0 : expNegUpper (107293813982095046292341 / 1035186514941855872000 : ℝ) ≤ (242729293456943 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (89893 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_428_1 : expNegUpper (429669923759337822355443 / 4140746059767423488000 : ℝ) ≤ (172317688144657 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (140589 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_428 : rowCell 3 428 ≤ (133627955804827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (242729293456943 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (172317688144657 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_428_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_428_1
  · norm_num [gridPoint]

theorem exp_3_429_0 : expNegUpper (17243926800945553743843 / 166180404963557888000 : ℝ) ≤ (861588409489011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (140589 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_429_1 : expNegUpper (8631896904609388697561 / 83090202481778944000 : ℝ) ≤ (764503669945009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1125763 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_429 : rowCell 3 429 ≤ (3705502980451 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (861588409489011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (764503669945009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_429_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_429_1
  · norm_num [gridPoint]

theorem exp_3_430_0 : expNegUpper (24057061643183106290009 / 231572057039790336000 : ℝ) ≤ (382251821206717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1125763 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_430_1 : expNegUpper (48169532832308778611969 / 463144114079580672000 : ℝ) ≤ (27131981421549 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2253631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_430 : rowCell 3 430 ≤ (6575656500297 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (382251821206717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27131981421549 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_430_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_430_1
  · norm_num [gridPoint]

theorem exp_3_431_0 : expNegUpper (434962084581690040770689 / 4182106767649260032000 : ℝ) ≤ (678299511272751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2253631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_431_1 : expNegUpper (5443284806657564837169 / 52276334595615750400 : ℝ) ≤ (60176356115943 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112787 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_431 : rowCell 3 431 ≤ (46671674649211 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (678299511272751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (60176356115943 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_431_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_431_1
  · norm_num [gridPoint]

theorem exp_3_432_0 : expNegUpper (5461288812864498412209 / 52449241836100614400 : ℝ) ≤ (150440884943333 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112787 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_432_1 : expNegUpper (437405822348286620004511 / 4195939346888049152000 : ℝ) ≤ (66727195617219 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (564463 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_432 : rowCell 3 432 ≤ (41403797202091 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (150440884943333 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (66727195617219 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_432_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_432_1
  · norm_num [gridPoint]

theorem exp_3_433_0 : expNegUpper (48761131212449339618591 / 467754973825843712000 : ℝ) ≤ (106763509218233 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (564463 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_433_1 : expNegUpper (24408606607231219629431 / 233877486912921856000 : ℝ) ≤ (118375720136157 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (35312 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_433 : rowCell 3 433 ≤ (9181838815591 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (106763509218233 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (118375720136157 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_433_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_433_1
  · norm_num [gridPoint]

theorem exp_3_434_0 : expNegUpper (8816066444453624765431 / 84473460405657856000 : ℝ) ≤ (236751431968619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (35312 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_434_1 : expNegUpper (17652403370822793347133 / 168946920811315712000 : ℝ) ≤ (419967193521987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (282761 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_434 : rowCell 3 434 ≤ (16288159829233 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (236751431968619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (419967193521987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_434_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_434_1
  · norm_num [gridPoint]

theorem exp_3_435_0 : expNegUpper (442762538953410064818477 / 4237574114438947328000 : ℝ) ≤ (419967178888839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (282761 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_435_1 : expNegUpper (110817832090462226944819 / 1059393528609736832000 : ℝ) ≤ (372452817630623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2264211 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_435 : rowCell 3 435 ≤ (1444599452151 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (419967178888839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (372452817630623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_435_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_435_1
  · norm_num [gridPoint]

theorem exp_3_436_0 : expNegUpper (12353551141571366192699 / 118097167969465472000 : ℝ) ≤ (18622640236899 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2264211 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_436_1 : expNegUpper (1978838494205945877163 / 18895546875114475520 : ℝ) ≤ (165143127415499 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2266337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_436 : rowCell 3 436 ≤ (25622181795447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18622640236899 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (165143127415499 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_436_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_436_1
  · norm_num [gridPoint]

theorem exp_3_437_0 : expNegUpper (17867969545779889574267 / 170617792706732871680 : ℝ) ≤ (82571560868169 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2266337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_437_1 : expNegUpper (223606046383187612077293 / 2132722408834160896000 : ℝ) ≤ (146434449681799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2268467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_437 : rowCell 3 437 ≤ (4544103288157 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (82571560868169 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (146434449681799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_437_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_437_1
  · norm_num [gridPoint]

theorem exp_3_438_0 : expNegUpper (224338370794766440403037 / 2139707213370820864000 : ℝ) ≤ (58573777871547 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2268467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_438_1 : expNegUpper (449191633064299759887073 / 4279414426741641728000 : ℝ) ≤ (129834380722983 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11353 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_438 : rowCell 3 438 ≤ (1259110684911 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (58573777871547 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (129834380722983 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_438_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_438_1
  · norm_num [gridPoint]

theorem exp_3_439_0 : expNegUpper (2002934932995621128953 / 19081808329425408000 : ℝ) ≤ (64917188158041 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11353 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_439_1 : expNegUpper (250654051156916709049 / 2385226041178176000 : ℝ) ≤ (230213099543997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2272737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_439 : rowCell 3 439 ≤ (35722624788913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (64917188158041 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (230213099543997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_439_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_439_1
  · norm_num [gridPoint]

theorem exp_3_440_0 : expNegUpper (56581262955035188213849 / 538427769975693376000 : ℝ) ≤ (115106545890401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2272737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_440_1 : expNegUpper (453169079813164820087031 / 4307422159805547008000 : ℝ) ≤ (204081862176427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2274877 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_440 : rowCell 3 440 ≤ (15834589114717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (115106545890401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (204081862176427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_440_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_440_1
  · norm_num [gridPoint]

theorem exp_3_441_0 : expNegUpper (454645982730671782624239 / 4321460283796132352000 : ℝ) ≤ (102040927669549 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2274877 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_441_1 : expNegUpper (45516700624878263801263 / 432146028379613235200 : ℝ) ≤ (45225462731549 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2277021 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_441 : rowCell 3 441 ≤ (3509169718083 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (102040927669549 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45225462731549 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_441_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_441_1
  · norm_num [gridPoint]

theorem exp_3_442_0 : expNegUpper (5073866746528047016487 / 48172458289916364800 : ℝ) ≤ (36180368980949 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2277021 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_442_1 : expNegUpper (50796786820182464088229 / 481724582899163648000 : ℝ) ≤ (160341525897427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (35612 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_442 : rowCell 3 442 ≤ (777617912023 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36180368980949 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (160341525897427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_442_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_442_1
  · norm_num [gridPoint]

theorem exp_3_443_0 : expNegUpper (458656187003177499018629 / 4349605046694568448000 : ℝ) ≤ (160341520594877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (35612 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_443_1 : expNegUpper (114795328801020520790097 / 1087401261673642112000 : ℝ) ≤ (28421276678843 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2281319 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_443 : rowCell 3 443 ≤ (1378423305589 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (160341520594877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28421276678843 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_443_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_443_1
  · norm_num [gridPoint]

theorem exp_3_444_0 : expNegUpper (4606705321699702319577 / 43637116856024192000 : ℝ) ≤ (71053189362533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2281319 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_444_1 : expNegUpper (18447908708337640153627 / 174548467424096768000 : ℝ) ≤ (125934843216903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2283473 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_444 : rowCell 3 444 ≤ (9772903361147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (71053189362533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (125934843216903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_444_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_444_1
  · norm_num [gridPoint]

theorem exp_3_445_0 : expNegUpper (51410116964471230781123 / 486426795868447232000 : ℝ) ≤ (62967419552893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2283473 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_445_1 : expNegUpper (25734461049280976975777 / 243213397934223616000 : ℝ) ≤ (22318917954153 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2285631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_445 : rowCell 3 445 ≤ (692834374361 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (62967419552893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22318917954153 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_445_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_445_1
  · norm_num [gridPoint]

theorem exp_3_446_0 : expNegUpper (232358879263164340482457 / 2195996739167693056000 : ℝ) ≤ (111594586151241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2285631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_446_1 : expNegUpper (93049813746454095011877 / 878398695667077222400 : ℝ) ≤ (98879317248569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (142987 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_446 : rowCell 3 446 ≤ (7673973066781 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (111594586151241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (98879317248569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_446_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_446_1
  · norm_num [gridPoint]

theorem exp_3_447_0 : expNegUpper (93350131940114338098237 / 881233726432100454400 : ℝ) ≤ (98879314062079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (142987 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_447_1 : expNegUpper (7301313081819036235249 / 68846384877507848000 : ℝ) ≤ (87605834560753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2289957 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_447 : rowCell 3 447 ≤ (3399666145707 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (98879314062079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (87605834560753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_447_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_447_1
  · norm_num [gridPoint]

theorem sum_3_416_2 : blockSum (rowCell 3) 416 2 ≤ (1051360130970687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_416) (by simpa only [blockSum_one] using cell_3_417) (by norm_num)

theorem sum_3_418_2 : blockSum (rowCell 3) 418 2 ≤ (414745950258309 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_418) (by simpa only [blockSum_one] using cell_3_419) (by norm_num)

theorem sum_3_416_4 : blockSum (rowCell 3) 416 4 ≤ (376170406297461 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_416_2 sum_3_418_2 (by norm_num)

theorem sum_3_420_2 : blockSum (rowCell 3) 420 2 ≤ (130840777737899 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_420) (by simpa only [blockSum_one] using cell_3_421) (by norm_num)

theorem sum_3_422_2 : blockSum (rowCell 3) 422 2 ≤ (64471242081957 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_422) (by simpa only [blockSum_one] using cell_3_423) (by norm_num)

theorem sum_3_420_4 : blockSum (rowCell 3) 420 4 ≤ (1169973825345151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_420_2 sum_3_422_2 (by norm_num)

theorem sum_3_416_8 : blockSum (rowCell 3) 416 8 ≤ (381353232104057 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_416_4 sum_3_420_4 (by norm_num)

theorem sum_3_424_2 : blockSum (rowCell 3) 424 2 ≤ (25405190754763 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_424) (by simpa only [blockSum_one] using cell_3_425) (by norm_num)

theorem sum_3_426_2 : blockSum (rowCell 3) 426 2 ≤ (2001492455601 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_426) (by simpa only [blockSum_one] using cell_3_427) (by norm_num)

theorem sum_3_424_4 : blockSum (rowCell 3) 424 4 ≤ (45420115310773 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_424_2 sum_3_426_2 (by norm_num)

theorem sum_3_428_2 : blockSum (rowCell 3) 428 2 ≤ (252204051179259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_428) (by simpa only [blockSum_one] using cell_3_429) (by norm_num)

theorem sum_3_430_2 : blockSum (rowCell 3) 430 2 ≤ (99276926651587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_430) (by simpa only [blockSum_one] using cell_3_431) (by norm_num)

theorem sum_3_428_4 : blockSum (rowCell 3) 428 4 ≤ (450757904482433 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_428_2 sum_3_430_2 (by norm_num)

theorem sum_3_424_8 : blockSum (rowCell 3) 424 8 ≤ (1177479749454801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_424_4 sum_3_428_4 (by norm_num)

theorem sum_3_416_16 : blockSum (rowCell 3) 416 16 ≤ (4228305606287257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_416_8 sum_3_424_8 (by norm_num)

theorem sum_3_432_2 : blockSum (rowCell 3) 432 2 ≤ (15626230492891 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_432) (by simpa only [blockSum_one] using cell_3_433) (by norm_num)

theorem sum_3_434_2 : blockSum (rowCell 3) 434 2 ≤ (30734154350743 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_434) (by simpa only [blockSum_one] using cell_3_435) (by norm_num)

theorem sum_3_432_4 : blockSum (rowCell 3) 432 4 ≤ (139599461165941 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_432_2 sum_3_434_2 (by norm_num)

theorem sum_3_436_2 : blockSum (rowCell 3) 436 2 ≤ (6042837279529 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_436) (by simpa only [blockSum_one] using cell_3_437) (by norm_num)

theorem sum_3_438_2 : blockSum (rowCell 3) 438 2 ≤ (15202833341213 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_438) (by simpa only [blockSum_one] using cell_3_439) (by norm_num)

theorem sum_3_436_4 : blockSum (rowCell 3) 436 4 ≤ (172699563178529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_436_2 sum_3_438_2 (by norm_num)

theorem sum_3_432_8 : blockSum (rowCell 3) 432 8 ≤ (451898485510411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_432_4 sum_3_436_4 (by norm_num)

theorem sum_3_440_2 : blockSum (rowCell 3) 440 2 ≤ (29871267987049 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_440) (by simpa only [blockSum_one] using cell_3_441) (by norm_num)

theorem sum_3_442_2 : blockSum (rowCell 3) 442 2 ≤ (586731825927 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_442) (by simpa only [blockSum_one] using cell_3_443) (by norm_num)

theorem sum_3_440_4 : blockSum (rowCell 3) 440 4 ≤ (53340541024129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_440_2 sum_3_442_2 (by norm_num)

theorem sum_3_444_2 : blockSum (rowCell 3) 444 2 ≤ (36866666081319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_444) (by simpa only [blockSum_one] using cell_3_445) (by norm_num)

theorem sum_3_446_2 : blockSum (rowCell 3) 446 2 ≤ (2894661071639 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_446) (by simpa only [blockSum_one] using cell_3_447) (by norm_num)

theorem sum_3_444_4 : blockSum (rowCell 3) 444 4 ≤ (65813276797709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_444_2 sum_3_446_2 (by norm_num)

theorem sum_3_440_8 : blockSum (rowCell 3) 440 8 ≤ (172494358845967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_440_4 sum_3_444_4 (by norm_num)

theorem sum_3_432_16 : blockSum (rowCell 3) 432 16 ≤ (312196422178189 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_432_8 sum_3_440_8 (by norm_num)

theorem sum_3_416_32 : blockSum (rowCell 3) 416 32 ≤ (970539690128727 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_416_16 sum_3_432_16 (by norm_num)

#print axioms sum_3_416_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
