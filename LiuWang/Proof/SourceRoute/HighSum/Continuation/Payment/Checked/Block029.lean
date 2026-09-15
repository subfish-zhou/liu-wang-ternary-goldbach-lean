import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_416_0 : expNegUpper (12436386433959664627027 / 124292458617438736000 : ℝ) ≤ (35158939936611667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2185181 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_416_1 : expNegUpper (79689953695327305411171 / 795471735151607910400 : ℝ) ≤ (31119588624479751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (437453 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_416 : rowCell 1 416 ≤ (4833089849790291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35158939936611667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31119588624479751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_416_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_416_1
  · norm_num [gridPoint]

theorem exp_1_417_0 : expNegUpper (79960238082992236198011 / 798169736082100326400 : ℝ) ≤ (15559793782422863 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (437453 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_417_1 : expNegUpper (200144280205703403580343 / 1995424340205250816000 : ℝ) ≤ (172138092262451 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2189353 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_417 : rowCell 1 417 ≤ (855532515825647 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15559793782422863 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (172138092262451 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_417_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_417_1
  · norm_num [gridPoint]

theorem exp_1_418_0 : expNegUpper (66940653415591290727309 / 667393587228119808000 : ℝ) ≤ (13771046915248617 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2189353 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_418_1 : expNegUpper (134044420409097095541271 / 1334787174456239616000 : ℝ) ≤ (24373916931785563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (547861 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_418 : rowCell 1 418 ≤ (3785762148076581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13771046915248617 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24373916931785563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_418_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_418_1
  · norm_num [gridPoint]

theorem exp_1_419_0 : expNegUpper (16139702644592304196613 / 160715888185307648000 : ℝ) ≤ (6093479028247589 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (547861 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_419_1 : expNegUpper (4039838809166286121743 / 40178972046326912000 : ℝ) ≤ (10784229034611393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2193539 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_419 : rowCell 1 419 ≤ (3350159201718787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6093479028247589 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10784229034611393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_419_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_419_1
  · norm_num [gridPoint]

theorem exp_1_420_0 : expNegUpper (101336784317769852343383 / 1007863931050604672000 : ℝ) ≤ (4313691469908221 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2193539 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_420_1 : expNegUpper (405840429471757430541211 / 4031455724202418688000 : ℝ) ≤ (19084397689598103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2195637 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_420 : rowCell 1 420 ≤ (2964442713503481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4313691469908221 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19084397689598103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_420_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_420_1
  · norm_num [gridPoint]

theorem exp_1_421_0 : expNegUpper (10441221639864148832501 / 103718899540459008000 : ℝ) ≤ (3816879411415079 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2195637 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_421_1 : expNegUpper (1045392094576965098599 / 10371889954045900800 : ℝ) ≤ (1688509772958839 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1098869 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_421 : rowCell 1 421 ≤ (20491624032707 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3816879411415079 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1688509772958839 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_421_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_421_1
  · norm_num [gridPoint]

theorem exp_1_422_0 : expNegUpper (1319593858574236893311 / 13092391220190771200 : ℝ) ≤ (16885097173706571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1098869 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_422_1 : expNegUpper (13211979133830455891631 / 130923912201907712000 : ℝ) ≤ (466814840433307 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2199843 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_422 : rowCell 1 422 ≤ (1160287149149267 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16885097173706571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (466814840433307 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_422_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_422_1
  · norm_num [gridPoint]

theorem exp_1_423_0 : expNegUpper (410946503873352953479209 / 4072268312746131968000 : ℝ) ≤ (14938074405371361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2199843 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_423_1 : expNegUpper (51430718531909913728891 / 509033539093266496000 : ℝ) ≤ (13214532110101771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2201951 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_423 : rowCell 1 423 ≤ (1026456680232859 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14938074405371361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13214532110101771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_423_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_423_1
  · norm_num [gridPoint]

theorem exp_1_424_0 : expNegUpper (27521658472870600057 / 272394545702592000 : ℝ) ≤ (82590823005339 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2201951 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_424_1 : expNegUpper (220440593171712302269 / 2179156365620736000 : ℝ) ≤ (2922235628172207 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1102031 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_424 : rowCell 1 424 ≤ (1815983712408257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (82590823005339 / 6250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2922235628172207 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_424_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_424_1
  · norm_num [gridPoint]

theorem exp_1_425_0 : expNegUpper (414709225809470225782847 / 4099590896637383168000 : ℝ) ≤ (5844471067763773 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1102031 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_425_1 : expNegUpper (207606227483063275069683 / 2049795448318691584000 : ℝ) ≤ (5169340051499529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2206177 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_425 : rowCell 1 425 ≤ (321254800815043 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5844471067763773 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5169340051499529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_425_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_425_1
  · norm_num [gridPoint]

theorem exp_1_426_0 : expNegUpper (208299780007462637495907 / 2056643223020820736000 : ℝ) ≤ (10338679771625623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2206177 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_426_1 : expNegUpper (83420957311023181343033 / 822657289208328294400 : ℝ) ≤ (9143691881631071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441659 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_426 : rowCell 1 426 ≤ (1420672044648761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10338679771625623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9143691881631071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_426_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_426_1
  · norm_num [gridPoint]

theorem exp_1_427_0 : expNegUpper (27899725980117519680731 / 275133655583443660800 : ℝ) ≤ (9143691590505927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441659 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_427_1 : expNegUpper (34916926413022273600903 / 343917069479304576000 : ℝ) ≤ (8086206824574663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (138151 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_427 : rowCell 1 427 ≤ (628209836207267 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9143691590505927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8086206824574663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_427_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_427_1
  · norm_num [gridPoint]

theorem exp_1_428_0 : expNegUpper (105099556215580358292341 / 1035186514941855872000 : ℝ) ≤ (8086206568826021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (138151 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_428_1 : expNegUpper (420907456161919326355443 / 4140746059767423488000 : ℝ) ≤ (3491444134911 / 488281250000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2212541 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_428 : rowCell 1 428 ≤ (1111072697945887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8086206568826021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3491444134911 / 488281250000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_428_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_428_1
  · norm_num [gridPoint]

theorem exp_1_429_0 : expNegUpper (16892263019557593423843 / 166180404963557888000 : ℝ) ≤ (7150477363641379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2212541 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_429_1 : expNegUpper (8456356283288213657561 / 83090202481778944000 : ℝ) ≤ (6322551285355673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2214669 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_429 : rowCell 1 429 ≤ (491232676879521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7150477363641379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6322551285355673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_429_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_429_1
  · norm_num [gridPoint]

theorem exp_1_430_0 : expNegUpper (70703491928992774870027 / 694716171119371008000 : ℝ) ≤ (3161275544012193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2214669 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_430_1 : expNegUpper (141578066985359999835907 / 1389432342238742016000 : ℝ) ≤ (1397516519602271 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2771 / 1250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_430 : rowCell 1 430 ≤ (173735749303663 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3161275544012193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1397516519602271 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_430_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_430_1
  · norm_num [gridPoint]

theorem exp_1_431_0 : expNegUpper (426141363109710520770689 / 4182106767649260032000 : ℝ) ≤ (5590065905090459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2771 / 1250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_431_1 : expNegUpper (5333207831615824037169 / 52276334595615750400 : ℝ) ≤ (988414140402583 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (443787 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_431 : rowCell 1 431 ≤ (768012863856461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5590065905090459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (988414140402583 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_431_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_431_1
  · norm_num [gridPoint]

theorem exp_1_432_0 : expNegUpper (5350847751106751212209 / 52449241836100614400 : ℝ) ≤ (308879409362167 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (443787 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_432_1 : expNegUpper (428585100876307100004511 / 4195939346888049152000 : ℝ) ≤ (4368864343114919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2221073 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_432 : rowCell 1 432 ≤ (169740434421009 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (308879409362167 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4368864343114919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_432_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_432_1
  · norm_num [gridPoint]

theorem exp_1_433_0 : expNegUpper (143333444167594674855773 / 1403264921477531136000 : ℝ) ≤ (2184432104718373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2221073 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_433_1 : expNegUpper (71753272331590362888293 / 701632460738765568000 : ℝ) ≤ (3861854597245013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444643 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_433 : rowCell 1 433 ≤ (300095705084831 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2184432104718373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3861854597245013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_433_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_433_1
  · norm_num [gridPoint]

theorem exp_1_434_0 : expNegUpper (664521400530432231187 / 6497958492742912000 : ℝ) ≤ (3861854479856183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444643 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_434_1 : expNegUpper (1330646879573260928241 / 12995916985485824000 : ℝ) ≤ (3413431471787639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27817 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_434 : rowCell 1 434 ≤ (53052038798359 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3861854479856183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3413431471787639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_434_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_434_1
  · norm_num [gridPoint]

theorem exp_1_435_0 : expNegUpper (433883563606869520818477 / 4237574114438947328000 : ℝ) ≤ (853357842177429 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27817 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_435_1 : expNegUpper (108601729120987154944819 / 1059393528609736832000 : ℝ) ≤ (1508427816989581 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (556877 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_435 : rowCell 1 435 ≤ (117225576361763 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (853357842177429 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1508427816989581 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_435_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_435_1
  · norm_num [gridPoint]

theorem exp_1_436_0 : expNegUpper (36319525190115698578097 / 354291503908396416000 : ℝ) ≤ (3016855543473177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (556877 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_436_1 : expNegUpper (5818129144663963711489 / 56686640625343426560 : ℝ) ≤ (2666159302456457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (111483 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_436 : rowCell 1 436 ≤ (10360263709971 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3016855543473177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2666159302456457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_436_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_436_1
  · norm_num [gridPoint]

theorem exp_1_437_0 : expNegUpper (17511645454427047334267 / 170617792706732871680 : ℝ) ≤ (106646368919761 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (111483 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_437_1 : expNegUpper (219159276975597212077293 / 2132722408834160896000 : ℝ) ≤ (2356058360058397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1115907 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_437 : rowCell 1 437 ≤ (366224618304793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (106646368919761 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2356058360058397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_437_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_437_1
  · norm_num [gridPoint]

theorem exp_1_438_0 : expNegUpper (219877037918535784403037 / 2139707213370820864000 : ℝ) ≤ (471211658059263 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1115907 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_438_1 : expNegUpper (440283530780478703887073 / 4279414426741641728000 : ℝ) ≤ (2081874424605181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2233973 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_438 : rowCell 1 438 ≤ (323618040775791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (471211658059263 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2081874424605181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_438_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_438_1
  · norm_num [gridPoint]

theorem exp_1_439_0 : expNegUpper (5889641742705509146859 / 57245424988276224000 : ℝ) ≤ (2081874363363063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2233973 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_439_1 : expNegUpper (737091043883314607147 / 7155678123534528000 : ℝ) ≤ (1839465755739117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1118067 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_439 : rowCell 1 439 ≤ (57189528912789 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2081874363363063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1839465755739117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_439_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_439_1
  · norm_num [gridPoint]

theorem exp_1_440_0 : expNegUpper (55462288868817460213849 / 538427769975693376000 : ℝ) ≤ (1839465701979733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1118067 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_440_1 : expNegUpper (444231850592063252087031 / 4307422159805547008000 : ℝ) ≤ (812583000776679 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2238299 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_440 : rowCell 1 440 ≤ (6316101414417 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1839465701979733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (812583000776679 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_440_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_440_1
  · norm_num [gridPoint]

theorem exp_1_441_0 : expNegUpper (445679626572289702624239 / 4321460283796132352000 : ℝ) ≤ (1625165954365329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2238299 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_441_1 : expNegUpper (44621521355904081401263 / 432146028379613235200 : ℝ) ≤ (179466237549637 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (560117 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_441 : rowCell 1 441 ≤ (3487551183639 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1625165954365329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (179466237549637 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_441_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_441_1
  · norm_num [gridPoint]

theorem exp_1_442_0 : expNegUpper (14922236252016729849461 / 144517374869749094400 : ℝ) ≤ (1435729858979683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (560117 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_442_1 : expNegUpper (149401575074420032264687 / 1445173748697490944000 : ℝ) ≤ (634142576236117 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2242639 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_442 : rowCell 1 442 ≤ (197179204023561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1435729858979683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (634142576236117 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_442_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_442_1
  · norm_num [gridPoint]

theorem exp_1_443_0 : expNegUpper (449660703907514907018629 / 4349605046694568448000 : ℝ) ≤ (317071279030487 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2242639 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_443_1 : expNegUpper (112550098894264936790097 / 1087401261673642112000 : ℝ) ≤ (112028976400281 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1122407 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_443 : rowCell 1 443 ≤ (87088513121971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (317071279030487 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (112028976400281 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_443_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_443_1
  · norm_num [gridPoint]

theorem exp_1_444_0 : expNegUpper (4516604856056673839577 / 43637116856024192000 : ℝ) ≤ (280072433025411 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1122407 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_444_1 : expNegUpper (18088089384511136473627 / 174548467424096768000 : ℝ) ≤ (494747122544597 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2246993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_444 : rowCell 1 444 ≤ (76923671562899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (280072433025411 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (494747122544597 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_444_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_444_1
  · norm_num [gridPoint]

theorem exp_1_445_0 : expNegUpper (151222147549099324343369 / 1459280387605341696000 : ℝ) ≤ (98949421709427 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2246993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_445_1 : expNegUpper (75701708720459122927331 / 729640193802670848000 : ℝ) ≤ (873908111944099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1124587 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_445 : rowCell 1 445 ≤ (16985121498001 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (98949421709427 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (873908111944099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_445_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_445_1
  · norm_num [gridPoint]

theorem exp_1_446_0 : expNegUpper (227839292512372660482457 / 2195996739167693056000 : ℝ) ≤ (109238510922321 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1124587 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_446_1 : expNegUpper (91244891739865474211877 / 878398695667077222400 : ℝ) ≤ (96471275752091 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2251359 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_446 : rowCell 1 446 ≤ (120004339693477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (109238510922321 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (96471275752091 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_446_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_446_1
  · norm_num [gridPoint]

theorem exp_1_447_0 : expNegUpper (7041491118928431915249 / 67787209725546188800 : ℝ) ≤ (154354036892353 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2251359 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_447_1 : expNegUpper (550775076604368941173 / 5295875759808296000 : ℝ) ≤ (340761198704121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (563387 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_447 : rowCell 1 447 ≤ (21195080152503 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (154354036892353 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (340761198704121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_447_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_447_1
  · norm_num [gridPoint]

theorem sum_1_416_2 : blockSum (rowCell 1) 416 2 ≤ (4555376214459263 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_416) (by simpa only [blockSum_one] using cell_1_417) (by norm_num)

theorem sum_1_418_2 : blockSum (rowCell 1) 418 2 ≤ (891990168724421 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_418) (by simpa only [blockSum_one] using cell_1_419) (by norm_num)

theorem sum_1_416_4 : blockSum (rowCell 1) 416 4 ≤ (8123336889356947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_416_2 sum_1_418_2 (by norm_num)

theorem sum_1_420_2 : blockSum (rowCell 1) 420 2 ≤ (5587370589689977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_420) (by simpa only [blockSum_one] using cell_1_421) (by norm_num)

theorem sum_1_422_2 : blockSum (rowCell 1) 422 2 ≤ (1093371914691063 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_422) (by simpa only [blockSum_one] using cell_1_423) (by norm_num)

theorem sum_1_420_4 : blockSum (rowCell 1) 420 4 ≤ (9960858248454229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_420_2 sum_1_422_2 (by norm_num)

theorem sum_1_416_8 : blockSum (rowCell 1) 416 8 ≤ (26207532027168123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_416_4 sum_1_420_4 (by norm_num)

theorem sum_1_424_2 : blockSum (rowCell 1) 424 2 ≤ (213891107280217 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_424) (by simpa only [blockSum_one] using cell_1_425) (by norm_num)

theorem sum_1_426_2 : blockSum (rowCell 1) 426 2 ≤ (535418343412659 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_426) (by simpa only [blockSum_one] using cell_1_427) (by norm_num)

theorem sum_1_424_4 : blockSum (rowCell 1) 424 4 ≤ (6099349433546767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_424_2 sum_1_426_2 (by norm_num)

theorem sum_1_428_2 : blockSum (rowCell 1) 428 2 ≤ (2093538051704929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_428) (by simpa only [blockSum_one] using cell_1_429) (by norm_num)

theorem sum_1_430_2 : blockSum (rowCell 1) 430 2 ≤ (204586451296847 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_430) (by simpa only [blockSum_one] using cell_1_431) (by norm_num)

theorem sum_1_428_4 : blockSum (rowCell 1) 428 4 ≤ (746045932415941 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_428_2 sum_1_430_2 (by norm_num)

theorem sum_1_424_8 : blockSum (rowCell 1) 424 8 ≤ (1228697386953309 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_424_4 sum_1_428_4 (by norm_num)

theorem sum_1_416_16 : blockSum (rowCell 1) 416 16 ≤ (7207422224558919 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_416_8 sum_1_424_8 (by norm_num)

theorem sum_1_432_2 : blockSum (rowCell 1) 432 2 ≤ (639576573926849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_432) (by simpa only [blockSum_one] using cell_1_433) (by norm_num)

theorem sum_1_434_2 : blockSum (rowCell 1) 434 2 ≤ (499711346715321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_434) (by simpa only [blockSum_one] using cell_1_435) (by norm_num)

theorem sum_1_432_4 : blockSum (rowCell 1) 432 4 ≤ (113928792064217 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_432_2 sum_1_434_2 (by norm_num)

theorem sum_1_436_2 : blockSum (rowCell 1) 436 2 ≤ (780635166703633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_436) (by simpa only [blockSum_one] using cell_1_437) (by norm_num)

theorem sum_1_438_2 : blockSum (rowCell 1) 438 2 ≤ (76195710667467 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_438) (by simpa only [blockSum_one] using cell_1_439) (by norm_num)

theorem sum_1_436_4 : blockSum (rowCell 1) 436 4 ≤ (1390200852043369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_436_2 sum_1_438_2 (by norm_num)

theorem sum_1_432_8 : blockSum (rowCell 1) 432 8 ≤ (3668776693327709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_432_4 sum_1_436_4 (by norm_num)

theorem sum_1_440_2 : blockSum (rowCell 1) 440 2 ≤ (59480916541197 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_440) (by simpa only [blockSum_one] using cell_1_441) (by norm_num)

theorem sum_1_442_2 : blockSum (rowCell 1) 442 2 ≤ (371356230267503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_442) (by simpa only [blockSum_one] using cell_1_443) (by norm_num)

theorem sum_1_440_4 : blockSum (rowCell 1) 440 4 ≤ (847203562597079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_440_2 sum_1_442_2 (by norm_num)

theorem sum_1_444_2 : blockSum (rowCell 1) 444 2 ≤ (144864157554903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_444) (by simpa only [blockSum_one] using cell_1_445) (by norm_num)

theorem sum_1_446_2 : blockSum (rowCell 1) 446 2 ≤ (28247467556999 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_446) (by simpa only [blockSum_one] using cell_1_447) (by norm_num)

theorem sum_1_444_4 : blockSum (rowCell 1) 444 4 ≤ (257854027782899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_444_2 sum_1_446_2 (by norm_num)

theorem sum_1_440_8 : blockSum (rowCell 1) 440 8 ≤ (1362911618162877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_440_4 sum_1_444_4 (by norm_num)

theorem sum_1_432_16 : blockSum (rowCell 1) 432 16 ≤ (2515844155745293 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_432_8 sum_1_440_8 (by norm_num)

theorem sum_1_416_32 : blockSum (rowCell 1) 416 32 ≤ (41068799434285181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_416_16 sum_1_432_16 (by norm_num)

#print axioms sum_1_416_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
