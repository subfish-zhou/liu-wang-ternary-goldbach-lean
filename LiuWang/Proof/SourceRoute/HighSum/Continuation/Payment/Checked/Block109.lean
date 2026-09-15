import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_416_0 : expNegUpper (12817216070731504627027 / 124292458617438736000 : ℝ) ≤ (820986597249039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2238119 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_416_1 : expNegUpper (82123137054552342211171 / 795471735151607910400 : ℝ) ≤ (730444022106021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (560041 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_416 : rowCell 6 416 ≤ (226263429253637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (820986597249039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (730444022106021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_416_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_416_1
  · norm_num [gridPoint]

theorem exp_6_417_0 : expNegUpper (82401674074446751398011 / 798169736082100326400 : ℝ) ≤ (1460887983626641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (560041 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_417_1 : expNegUpper (206237554394052843580343 / 1995424340205250816000 : ℝ) ≤ (649823239438341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2242211 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_417 : rowCell 6 417 ≤ (12581290823339 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1460887983626641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (649823239438341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_417_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_417_1
  · norm_num [gridPoint]

theorem exp_6_418_0 : expNegUpper (206935866015697008181927 / 2002180761684359424000 : ℝ) ≤ (1299646425341689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2242211 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_418_1 : expNegUpper (414340441184563862623813 / 4004361523368718848000 : ℝ) ≤ (1156088804014737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2244263 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_418 : rowCell 6 418 ≤ (179074419249291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1299646425341689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1156088804014737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_418_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_418_1
  · norm_num [gridPoint]

theorem exp_6_419_0 : expNegUpper (16629640369329102916613 / 160715888185307648000 : ℝ) ≤ (578044378356877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2244263 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_419_1 : expNegUpper (4162116924544748841743 / 40178972046326912000 : ℝ) ≤ (257072156077339 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1123159 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_419 : rowCell 6 419 ≤ (159286761150759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (578044378356877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (257072156077339 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_419_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_419_1
  · norm_num [gridPoint]

theorem exp_6_420_0 : expNegUpper (104404052992518268343383 / 1007863931050604672000 : ℝ) ≤ (257072145630007 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1123159 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_420_1 : expNegUpper (418088872590177398541211 / 4031455724202418688000 : ℝ) ≤ (457263945518147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (281047 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_420 : rowCell 6 420 ≤ (141671922750903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (257072145630007 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (457263945518147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_420_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_420_1
  · norm_num [gridPoint]

theorem exp_6_421_0 : expNegUpper (419497350234269164467539 / 4045037082077901312000 : ℝ) ≤ (914527854119531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (281047 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_421_1 : expNegUpper (41997199158401005245361 / 404503708207790131200 : ℝ) ≤ (40663727070289 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1125219 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_421 : rowCell 6 421 ≤ (125992903004171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (914527854119531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40663727070289 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_421_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_421_1
  · norm_num [gridPoint]

theorem exp_6_422_0 : expNegUpper (1359304625865014493311 / 13092391220190771200 : ℝ) ≤ (81327450879621 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1125219 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_422_1 : expNegUpper (13608421271881015891631 / 130923912201907712000 : ℝ) ≤ (723162518012971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (281563 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_422 : rowCell 6 422 ≤ (112038368387567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (81327450879621 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (723162518012971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_422_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_422_1
  · norm_num [gridPoint]

theorem exp_6_423_0 : expNegUpper (423277473314067705479209 / 4072268312746131968000 : ℝ) ≤ (90395311151311 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (281563 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_423_1 : expNegUpper (52969510764427545728891 / 509033539093266496000 : ℝ) ≤ (321486958648251 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2254573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_423 : rowCell 6 423 ≤ (24904973537667 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (90395311151311 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (321486958648251 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_423_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_423_1
  · norm_num [gridPoint]

theorem exp_6_424_0 : expNegUpper (85035295622869489771 / 817183637107776000 : ℝ) ≤ (642973891858771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2254573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_424_1 : expNegUpper (681051330620280510007 / 6537469096862208000 : ℝ) ≤ (571623042142169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1128323 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_424 : rowCell 6 424 ≤ (44284749833391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (642973891858771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (571623042142169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_424_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_424_1
  · norm_num [gridPoint]

theorem exp_6_425_0 : expNegUpper (427081458411332369782847 / 4099590896637383168000 : ℝ) ≤ (285811509838993 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1128323 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_425_1 : expNegUpper (213782027993707499069683 / 2049795448318691584000 : ℝ) ≤ (25407107864659 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1129361 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_425 : rowCell 6 425 ≤ (9842180850783 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (285811509838993 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25407107864659 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_425_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_425_1
  · norm_num [gridPoint]

theorem exp_6_426_0 : expNegUpper (214496212098680557495907 / 2056643223020820736000 : ℝ) ≤ (254071068728299 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1129361 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_426_1 : expNegUpper (85895403831395610143033 / 822657289208328294400 : ℝ) ≤ (56458595914653 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1130401 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_426 : rowCell 6 426 ≤ (69990273506217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (254071068728299 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (56458595914653 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_426_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_426_1
  · norm_num [gridPoint]

theorem exp_6_427_0 : expNegUpper (86181877092954466242193 / 825400966750330982400 : ℝ) ≤ (451668749802343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1130401 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_427_1 : expNegUpper (107848995284675780802709 / 1031751208437913728000 : ℝ) ≤ (401434255782911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452577 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_427 : rowCell 6 427 ≤ (62209037627009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (451668749802343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (401434255782911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_427_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_427_1
  · norm_num [gridPoint]

theorem exp_6_428_0 : expNegUpper (108208088051476166292341 / 1035186514941855872000 : ℝ) ≤ (80286848063853 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452577 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_428_1 : expNegUpper (433320951924928862355443 / 4140746059767423488000 : ℝ) ≤ (2854029929907 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (566243 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_428 : rowCell 6 428 ≤ (27643874399849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (80286848063853 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2854029929907 / 8000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_428_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_428_1
  · norm_num [gridPoint]

theorem exp_6_429_0 : expNegUpper (915287019817045818097 / 8746337103345152000 : ℝ) ≤ (7135074551737 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (566243 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_429_1 : expNegUpper (458159938429467278819 / 4373168551672576000 : ℝ) ≤ (158508510382117 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2267063 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_429 : rowCell 6 429 ≤ (12282992077667 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7135074551737 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (158508510382117 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_429_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_429_1
  · norm_num [gridPoint]

theorem exp_6_430_0 : expNegUpper (218348171039343636610081 / 2084148513358113024000 : ℝ) ≤ (63403401742691 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2267063 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_430_1 : expNegUpper (437188959880236927507721 / 4168297026716226048000 : ℝ) ≤ (140840242736383 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2269157 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_430 : rowCell 6 430 ≤ (2182877958417 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (63403401742691 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (140840242736383 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_430_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_430_1
  · norm_num [gridPoint]

theorem exp_6_431_0 : expNegUpper (438637385195014840770689 / 4182106767649260032000 : ℝ) ≤ (281680474835891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2269157 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_431_1 : expNegUpper (5489150212924956837169 / 52276334595615750400 : ℝ) ≤ (250259904507729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454251 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_431 : rowCell 6 431 ≤ (19394785188461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (281680474835891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (250259904507729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_431_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_431_1
  · norm_num [gridPoint]

theorem exp_6_432_0 : expNegUpper (5507305921930226412209 / 52449241836100614400 : ℝ) ≤ (125129947559811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454251 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_432_1 : expNegUpper (441081122961611420004511 / 4195939346888049152000 : ℝ) ≤ (13895249063173 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (568339 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_432 : rowCell 6 432 ≤ (8615310281547 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (125129947559811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13895249063173 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_432_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_432_1
  · norm_num [gridPoint]

theorem exp_6_433_0 : expNegUpper (442537617749235736567319 / 4209794764432593408000 : ℝ) ≤ (222323976725487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (568339 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_433_1 : expNegUpper (221518143827710096664879 / 2104897382216296704000 : ℝ) ≤ (98744312646027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2275461 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_433 : rowCell 6 433 ≤ (3826639014313 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (222323976725487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (98744312646027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_433_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_433_1
  · norm_num [gridPoint]

theorem exp_6_434_0 : expNegUpper (8889936543436127165431 / 84473460405657856000 : ℝ) ≤ (19748861798063 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2275461 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_434_1 : expNegUpper (17799900844310460547133 / 168946920811315712000 : ℝ) ≤ (175411787192447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2277569 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_434 : rowCell 6 434 ≤ (27192232572929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19748861798063 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (175411787192447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_434_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_434_1
  · norm_num [gridPoint]

theorem exp_6_435_0 : expNegUpper (446462112014468624818477 / 4237574114438947328000 : ℝ) ≤ (43852945185231 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2277569 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_435_1 : expNegUpper (111741208327743506944819 / 1059393528609736832000 : ℝ) ≤ (77894460728983 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2279681 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_435 : rowCell 6 435 ≤ (12075726383737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43852945185231 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (77894460728983 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_435_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_435_1
  · norm_num [gridPoint]

theorem exp_6_436_0 : expNegUpper (112108370567390295734291 / 1062874511725189248000 : ℝ) ≤ (155788915765659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2279681 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_436_1 : expNegUpper (17957529370295855294467 / 170059921876030279680 : ℝ) ≤ (69174443479731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2281797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_436 : rowCell 6 436 ≤ (5362198209787 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (155788915765659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (69174443479731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_436_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_436_1
  · norm_num [gridPoint]

theorem exp_6_437_0 : expNegUpper (18016437917176907174267 / 170617792706732871680 : ℝ) ≤ (138348881937419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2281797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_437_1 : expNegUpper (225458866969683612077293 / 2132722408834160896000 : ℝ) ≤ (122850310866511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (570979 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_437 : rowCell 6 437 ≤ (19046879810413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (138348881937419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (122850310866511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_437_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_437_1
  · norm_num [gridPoint]

theorem exp_6_438_0 : expNegUpper (226197259493195880403037 / 2139707213370820864000 : ℝ) ≤ (24570061287231 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (570979 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_438_1 : expNegUpper (452903342349225199887073 / 4279414426741641728000 : ℝ) ≤ (109078342501093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1143019 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_438 : rowCell 6 438 ≤ (169124454539 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24570061287231 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (109078342501093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_438_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_438_1
  · norm_num [gridPoint]

theorem exp_6_439_0 : expNegUpper (18175368217312282960577 / 171736274964828672000 : ℝ) ≤ (21815667718603 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1143019 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_439_1 : expNegUpper (2274475347396544781441 / 21467034370603584000 : ℝ) ≤ (1210521982777 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (572041 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_439 : rowCell 6 439 ≤ (3753969623817 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21815667718603 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1210521982777 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_439_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_439_1
  · norm_num [gridPoint]

theorem exp_6_440_0 : expNegUpper (57047502157625908213849 / 538427769975693376000 : ℝ) ≤ (96841755175057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (572041 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_440_1 : expNegUpper (456892925321957140087031 / 4307422159805547008000 : ℝ) ≤ (85970382388401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1145147 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_440 : rowCell 6 440 ≤ (1666353164551 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (96841755175057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (85970382388401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_440_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_440_1
  · norm_num [gridPoint]

theorem exp_6_441_0 : expNegUpper (458381964463330982624239 / 4321460283796132352000 : ℝ) ≤ (21492594837033 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1145147 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_441_1 : expNegUpper (45889691986950839801263 / 432146028379613235200 : ℝ) ≤ (76312782268507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2292427 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_441 : rowCell 6 441 ≤ (2958458486591 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21492594837033 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (76312782268507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_441_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_441_1
  · norm_num [gridPoint]

theorem exp_6_442_0 : expNegUpper (46039005703211687148383 / 433552124609247283200 : ℝ) ≤ (38156389793631 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2292427 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_442_1 : expNegUpper (460907063114301376794061 / 4335521246092472832000 : ℝ) ≤ (67734220765597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (573641 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_442 : rowCell 6 442 ≤ (5252018341479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38156389793631 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (67734220765597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_442_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_442_1
  · norm_num [gridPoint]

theorem exp_6_443_0 : expNegUpper (462404304959703579018629 / 4349605046694568448000 : ℝ) ≤ (67734218401159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (573641 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_443_1 : expNegUpper (115730841262168680790097 / 1087401261673642112000 : ℝ) ≤ (60114826039523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (35886 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_443 : rowCell 6 443 ≤ (9322867184991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (67734218401159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (60114826039523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_443_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_443_1
  · norm_num [gridPoint]

theorem exp_6_444_0 : expNegUpper (4644247182384297519577 / 43637116856024192000 : ℝ) ≤ (7514352994327 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (35886 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_444_1 : expNegUpper (18597833426598683353627 / 174548467424096768000 : ℝ) ≤ (52097619519 / 976562500000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (71839 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_444 : rowCell 6 444 ≤ (4136904159643 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7514352994327 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (52097619519 / 976562500000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_444_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_444_1
  · norm_num [gridPoint]

theorem exp_6_445_0 : expNegUpper (466451306860634037030107 / 4377841162816025088000 : ℝ) ≤ (53347960549171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (71839 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_445_1 : expNegUpper (233487242477758552781993 / 2188920581408012544000 : ℝ) ≤ (47338778115013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (460199 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_445 : rowCell 6 445 ≤ (1468433488827 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (53347960549171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47338778115013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_445_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_445_1
  · norm_num [gridPoint]

theorem exp_6_446_0 : expNegUpper (234242040409327540482457 / 2195996739167693056000 : ℝ) ≤ (47338776494299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (460199 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_446_1 : expNegUpper (93801864582532687011877 / 878398695667077222400 : ℝ) ≤ (42002911629303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1151573 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_446 : rowCell 6 446 ≤ (814359520737 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47338776494299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42002911629303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_446_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_446_1
  · norm_num [gridPoint]

theorem exp_6_447_0 : expNegUpper (94104610020966306098237 / 881233726432100454400 : ℝ) ≤ (10500727550129 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1151573 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_447_1 : expNegUpper (7360161867636636235249 / 68846384877507848000 : ℝ) ≤ (9316334660063 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (23053 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_447 : rowCell 6 447 ≤ (5780311923037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10500727550129 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9316334660063 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_447_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_447_1
  · norm_num [gridPoint]

theorem sum_6_416_2 : blockSum (rowCell 6) 416 2 ≤ (427564082427061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_416) (by simpa only [blockSum_one] using cell_6_417) (by norm_num)

theorem sum_6_418_2 : blockSum (rowCell 6) 418 2 ≤ (6767223608001 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_418) (by simpa only [blockSum_one] using cell_6_419) (by norm_num)

theorem sum_6_416_4 : blockSum (rowCell 6) 416 4 ≤ (765925262827111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_416_2 sum_6_418_2 (by norm_num)

theorem sum_6_420_2 : blockSum (rowCell 6) 420 2 ≤ (133832412877537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_420) (by simpa only [blockSum_one] using cell_6_421) (by norm_num)

theorem sum_6_422_2 : blockSum (rowCell 6) 422 2 ≤ (42331652507647 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_422) (by simpa only [blockSum_one] using cell_6_423) (by norm_num)

theorem sum_6_420_4 : blockSum (rowCell 6) 420 4 ≤ (479323088293309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_420_2 sum_6_422_2 (by norm_num)

theorem sum_6_416_8 : blockSum (rowCell 6) 416 8 ≤ (62262417556021 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_416_4 sum_6_420_4 (by norm_num)

theorem sum_6_424_2 : blockSum (rowCell 6) 424 2 ≤ (83653473236523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_424) (by simpa only [blockSum_one] using cell_6_425) (by norm_num)

theorem sum_6_426_2 : blockSum (rowCell 6) 426 2 ≤ (66099655566613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_426) (by simpa only [blockSum_one] using cell_6_427) (by norm_num)

theorem sum_6_424_4 : blockSum (rowCell 6) 424 4 ≤ (2339892637549 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_424_2 sum_6_426_2 (by norm_num)

theorem sum_6_428_2 : blockSum (rowCell 6) 428 2 ≤ (52209858555183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_428) (by simpa only [blockSum_one] using cell_6_429) (by norm_num)

theorem sum_6_430_2 : blockSum (rowCell 6) 430 2 ≤ (41223564772631 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_430) (by simpa only [blockSum_one] using cell_6_431) (by norm_num)

theorem sum_6_428_4 : blockSum (rowCell 6) 428 4 ≤ (46716711663907 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_428_2 sum_6_430_2 (by norm_num)

theorem sum_6_424_8 : blockSum (rowCell 6) 424 8 ≤ (4863731042619 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_424_4 sum_6_428_4 (by norm_num)

theorem sum_6_416_16 : blockSum (rowCell 6) 416 16 ≤ (21645268192279 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_416_8 sum_6_424_8 (by norm_num)

theorem sum_6_432_2 : blockSum (rowCell 6) 432 2 ≤ (16268588310173 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_432) (by simpa only [blockSum_one] using cell_6_433) (by norm_num)

theorem sum_6_434_2 : blockSum (rowCell 6) 434 2 ≤ (51343685340403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_434) (by simpa only [blockSum_one] using cell_6_435) (by norm_num)

theorem sum_6_432_4 : blockSum (rowCell 6) 432 4 ≤ (23283607716219 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_432_2 sum_6_434_2 (by norm_num)

theorem sum_6_436_2 : blockSum (rowCell 6) 436 2 ≤ (40495672649561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_436) (by simpa only [blockSum_one] using cell_6_437) (by norm_num)

theorem sum_6_438_2 : blockSum (rowCell 6) 438 2 ≤ (1995520246823 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_438) (by simpa only [blockSum_one] using cell_6_439) (by norm_num)

theorem sum_6_436_4 : blockSum (rowCell 6) 436 4 ≤ (72423996598729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_436_2 sum_6_438_2 (by norm_num)

theorem sum_6_432_8 : blockSum (rowCell 6) 432 8 ≤ (11802627198739 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_432_4 sum_6_436_4 (by norm_num)

theorem sum_6_440_2 : blockSum (rowCell 6) 440 2 ≤ (6291164815693 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_440) (by simpa only [blockSum_one] using cell_6_441) (by norm_num)

theorem sum_6_442_2 : blockSum (rowCell 6) 442 2 ≤ (19826903867949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_442) (by simpa only [blockSum_one] using cell_6_443) (by norm_num)

theorem sum_6_440_4 : blockSum (rowCell 6) 440 4 ≤ (44991563130721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_440_2 sum_6_442_2 (by norm_num)

theorem sum_6_444_2 : blockSum (rowCell 6) 444 2 ≤ (15615975763421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_444) (by simpa only [blockSum_one] using cell_6_445) (by norm_num)

theorem sum_6_446_2 : blockSum (rowCell 6) 446 2 ≤ (12295188088933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_446) (by simpa only [blockSum_one] using cell_6_447) (by norm_num)

theorem sum_6_444_4 : blockSum (rowCell 6) 444 4 ≤ (13955581926177 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_444_2 sum_6_446_2 (by norm_num)

theorem sum_6_440_8 : blockSum (rowCell 6) 440 8 ≤ (2916109079323 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_440_4 sum_6_444_4 (by norm_num)

theorem sum_6_432_16 : blockSum (rowCell 6) 432 16 ≤ (261744762162899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_432_8 sum_6_440_8 (by norm_num)

theorem sum_6_416_32 : blockSum (rowCell 6) 416 32 ≤ (1993366217545219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_416_16 sum_6_432_16 (by norm_num)

#print axioms sum_6_416_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
