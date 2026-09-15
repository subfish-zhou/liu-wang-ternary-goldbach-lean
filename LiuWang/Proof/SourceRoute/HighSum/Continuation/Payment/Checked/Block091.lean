import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_352_0 : expNegUpper (1890380216400319874929 / 19759387837319683200 : ℝ) ≤ (2828070170197760967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (527887 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_352_1 : expNegUpper (302807833260077663633711 / 3161502053971149312000 : ℝ) ≤ (253409617972543939 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (26417 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_352 : rowCell 5 352 ≤ (19550699390386489 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2828070170197760967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (253409617972543939 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_352_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_352_1
  · norm_num [gridPoint]

theorem exp_5_353_0 : expNegUpper (303959905953457668656039 / 3173530407055282688000 : ℝ) ≤ (2534096015211662847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (26417 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_353_1 : expNegUpper (152154329413055694630359 / 1586765203527641344000 : ℝ) ≤ (2270369699370519983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (84607 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_353 : rowCell 5 353 ≤ (350345956419498217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2534096015211662847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2270369699370519983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_353_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_353_1
  · norm_num [gridPoint]

theorem exp_5_354_0 : expNegUpper (6109284866470508342239 / 63711631968903424000 : ℝ) ≤ (567592388273005329 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (84607 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_354_1 : expNegUpper (12232590150543436943437 / 127423263937806848000 : ℝ) ≤ (2033812957531153313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1058497 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_354 : rowCell 5 354 ≤ (156932427856808141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (567592388273005329 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2033812957531153313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_354_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_354_1
  · norm_num [gridPoint]

theorem exp_5_355_0 : expNegUpper (306973856726593072085437 / 3197655628140814848000 : ℝ) ≤ (2033812827482489131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1058497 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_355_1 : expNegUpper (76831532016209978334599 / 799413907035203712000 : ℝ) ≤ (1821657442335838487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2118817 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_355 : rowCell 5 355 ≤ (28114435597422299 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2033812827482489131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1821657442335838487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_355_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_355_1
  · norm_num [gridPoint]

theorem exp_5_356_0 : expNegUpper (77122189038749820076391 / 802438124035553408000 : ℝ) ≤ (910828663365130571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2118817 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_356_1 : expNegUpper (61768558344442401049439 / 641950499228442726400 : ℝ) ≤ (407853346584461217 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2120643 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_356 : rowCell 5 356 ≤ (251801018765145063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (910828663365130571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (407853346584461217 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_356_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_356_1
  · norm_num [gridPoint]

theorem exp_5_357_0 : expNegUpper (62001790320216537700279 / 644374440489873510400 : ℝ) ≤ (20392666044795873 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2120643 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_357_1 : expNegUpper (155182377364020423020693 / 1610936101224683776000 : ℝ) ≤ (292168413537076801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1061237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_357 : rowCell 5 357 ≤ (225490038412706563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20392666044795873 / 12500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (292168413537076801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_357_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_357_1
  · norm_num [gridPoint]

theorem exp_5_358_0 : expNegUpper (155767226528590971700997 / 1617007373531138304000 : ℝ) ≤ (730420988182442977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1061237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_358_1 : expNegUpper (311892027074665082450033 / 3234014747062276608000 : ℝ) ≤ (81745676504928281 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (531077 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_358 : rowCell 5 358 ≤ (201901400177670307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (730420988182442977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (81745676504928281 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_358_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_358_1
  · norm_num [gridPoint]

theorem exp_5_359_0 : expNegUpper (12522610820625427669457 / 129847205199237632000 : ℝ) ≤ (130793074292942233 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (531077 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_359_1 : expNegUpper (1567123093772116806011 / 16230900649904704000 : ℝ) ≤ (1170870518087155603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1063073 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_359 : rowCell 5 359 ≤ (22594551875167101 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (130793074292942233 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1170870518087155603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_359_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_359_1
  · norm_num [gridPoint]

theorem exp_5_360_0 : expNegUpper (1268554088583800726749 / 13138582061311936000 : ℝ) ≤ (1170870445984478871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1063073 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_360_1 : expNegUpper (10160081927730784807321 / 105108656490495488000 : ℝ) ≤ (524017608567382699 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (531997 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_360 : rowCell 5 360 ≤ (161804594502712001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1170870445984478871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (524017608567382699 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_360_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_360_1
  · norm_num [gridPoint]

theorem exp_5_361_0 : expNegUpper (316142893408961255623039 / 3270579410735534592000 : ℝ) ≤ (209607030615561493 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (531997 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_361_1 : expNegUpper (6330116001653932653067 / 65411588214710691840 : ℝ) ≤ (937963873917600479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2129833 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_361 : rowCell 5 361 ≤ (36205208336126491 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (209607030615561493 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (937963873917600479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_361_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_361_1
  · norm_num [gridPoint]

theorem exp_5_362_0 : expNegUpper (6353794376570207292667 / 65656266171429283840 : ℝ) ≤ (29311369281725201 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2129833 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_362_1 : expNegUpper (318054409715888918810461 / 3282813308571464192000 : ℝ) ≤ (839343813366575471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1065841 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_362 : rowCell 5 362 ≤ (32400717301815927 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29311369281725201 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (839343813366575471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_362_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_362_1
  · norm_num [gridPoint]

theorem exp_5_363_0 : expNegUpper (319241900219768553993749 / 3295070044713148928000 : ℝ) ≤ (209835940706378223 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1065841 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_363_1 : expNegUpper (79902094662892458556837 / 823767511178287232000 : ℝ) ≤ (750995850742036227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (426707 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_363 : rowCell 5 363 ≤ (115968993442092247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (209835940706378223 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (750995850742036227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_363_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_363_1
  · norm_num [gridPoint]

theorem exp_5_364_0 : expNegUpper (3207994475750744704333 / 33073496191605888000 : ℝ) ≤ (750995805856327063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (426707 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_364_1 : expNegUpper (12846708675283121025323 / 132293984766423552000 : ℝ) ≤ (671860882182842363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (66731 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_364 : rowCell 5 364 ≤ (20751197607924379 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (750995805856327063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (671860882182842363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_364_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_364_1
  · norm_num [gridPoint]

theorem exp_5_365_0 : expNegUpper (322362370886766760681067 / 3319652031913783808000 : ℝ) ≤ (671860842324246299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (66731 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_365_1 : expNegUpper (161366217199876069878353 / 1659826015956891904000 : ℝ) ≤ (300493902103936419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2137253 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_365 : rowCell 5 365 ≤ (92817266880077997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (671860842324246299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (300493902103936419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_365_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_365_1
  · norm_num [gridPoint]

theorem exp_5_366_0 : expNegUpper (161965340073592035733057 / 1665988641486366976000 : ℝ) ≤ (120197553763479831 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2137253 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_366_1 : expNegUpper (64860508239386164665461 / 666395456594546790400 : ℝ) ≤ (268761316209265703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2139117 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_366 : rowCell 5 366 ≤ (83021201338562667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (120197553763479831 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (268761316209265703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_366_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_366_1
  · norm_num [gridPoint]

theorem exp_5_367_0 : expNegUpper (65100877069733009903501 / 668865074467487846400 : ℝ) ≤ (134380650249717313 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2139117 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_367_1 : expNegUpper (20367377954122045192121 / 209020335771089952000 : ℝ) ≤ (240349351054482833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (428197 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_367 : rowCell 5 367 ≤ (37124806115412667 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (134380650249717313 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (240349351054482833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_367_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_367_1
  · norm_num [gridPoint]

theorem exp_5_368_0 : expNegUpper (20442718530221771347769 / 209793518750493728000 : ℝ) ≤ (480698674217734353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (428197 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_368_1 : expNegUpper (327458962599156485725663 / 3356696300007899648000 : ℝ) ≤ (21491392238753359 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2142857 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_368 : rowCell 5 368 ≤ (4149775738507781 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (480698674217734353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21491392238753359 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_368_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_368_1
  · norm_num [gridPoint]

theorem exp_5_369_0 : expNegUpper (13146720941766903773423 / 134763602639364608000 : ℝ) ≤ (429827820018798537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2142857 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_369_1 : expNegUpper (6580905943777615160231 / 67381801319682304000 : ℝ) ≤ (96073111183028789 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (536183 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_369 : rowCell 5 369 ≤ (59366381141811989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (429827820018798537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (96073111183028789 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_369_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_369_1
  · norm_num [gridPoint]

theorem exp_5_370_0 : expNegUpper (165128988261438227280191 / 1690753335133042944000 : ℝ) ≤ (384292422760889307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (536183 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_370_1 : expNegUpper (330637061027464186660661 / 3381506670266085888000 : ℝ) ≤ (343538289302656677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (536653 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_370 : rowCell 5 370 ≤ (53074069434079143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (384292422760889307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (343538289302656677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_370_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_370_1
  · norm_num [gridPoint]

theorem exp_5_371_0 : expNegUpper (331853365411998568967789 / 3393946112853811712000 : ℝ) ≤ (34353826980532097 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (536653 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_371_1 : expNegUpper (16611713205362270920103 / 169697305642690585600 : ℝ) ≤ (153534067205247761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (429699 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_371 : rowCell 5 371 ≤ (47442803524608627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34353826980532097 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (153534067205247761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_371_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_371_1
  · norm_num [gridPoint]

theorem exp_5_372_0 : expNegUpper (16672710010193879214343 / 170320419687364633600 : ℝ) ≤ (153534058555201903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (429699 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_372_1 : expNegUpper (333836916420563099964811 / 3406408393747292672000 : ℝ) ≤ (3430448937437483 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2150381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_372 : rowCell 5 372 ≤ (5300474558269349 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (153534058555201903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3430448937437483 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_372_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_372_1
  · norm_num [gridPoint]

theorem exp_5_373_0 : expNegUpper (335060490890852147246659 / 3418893512946528768000 : ℝ) ≤ (137217949823107403 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2150381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_373_1 : expNegUpper (167722513979877939038989 / 1709446756473264384000 : ℝ) ≤ (245241536516442141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (134517 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_373 : rowCell 5 373 ≤ (37895345542677497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (137217949823107403 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (245241536516442141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_373_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_373_1
  · norm_num [gridPoint]

theorem exp_5_374_0 : expNegUpper (269337797972208723661 / 2745121176361216000 : ℝ) ≤ (245241522900357787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (134517 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_374_1 : expNegUpper (539293773947459839153 / 5490242352722432000 : ℝ) ≤ (109563095012592331 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1077083 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_374 : rowCell 5 374 ≤ (33862110831897637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (245241522900357787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (109563095012592331 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_374_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_374_1
  · norm_num [gridPoint]

theorem exp_5_375_0 : expNegUpper (338289479919442503004697 / 3443932266262266368000 : ℝ) ≤ (43825235589501229 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1077083 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_375_1 : expNegUpper (42334708585640163858977 / 430491533282783296000 : ℝ) ≤ (48942034719077193 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (67377 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_375 : rowCell 5 375 ≤ (7563616584851339 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43825235589501229 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (48942034719077193 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_375_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_375_1
  · norm_num [gridPoint]

theorem exp_5_376_0 : expNegUpper (42489024780716948657633 / 432060737547345984000 : ℝ) ≤ (97884064082186829 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (67377 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_376_1 : expNegUpper (68060443571194251802123 / 691297180075753574400 : ℝ) ≤ (87439465121322391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (431593 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_376 : rowCell 5 376 ≤ (27027916502256323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (97884064082186829 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (87439465121322391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_376_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_376_1
  · norm_num [gridPoint]

theorem exp_5_377_0 : expNegUpper (68308082487295762014883 / 693812474560204902400 : ℝ) ≤ (8743946037151601 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (431593 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_377_1 : expNegUpper (170966133111025445308043 / 1734531186400512256000 : ℝ) ≤ (31239997832663949 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (215987 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_377 : rowCell 5 377 ≤ (2414257156407929 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8743946037151601 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31239997832663949 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_377_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_377_1
  · norm_num [gridPoint]

theorem exp_5_378_0 : expNegUpper (171587066242005406086907 / 1740830841764518144000 : ℝ) ≤ (31239996147944339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (215987 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_378_1 : expNegUpper (343567823775698852417293 / 3481661683529036288000 : ℝ) ≤ (17437444626005717 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2161779 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_378 : rowCell 5 378 ≤ (21562675960120647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31239996147944339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17437444626005717 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_378_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_378_1
  · norm_num [gridPoint]

theorem exp_5_379_0 : expNegUpper (13792534735226809691533 / 139771353302512128000 : ℝ) ≤ (69749774769686807 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2161779 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_379_1 : expNegUpper (3452089005092537911433 / 34942838325628032000 : ℝ) ≤ (12456993998093447 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (540923 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_379 : rowCell 5 379 ≤ (19256184425752857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (69749774769686807 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12456993998093447 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_379_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_379_1
  · norm_num [gridPoint]

theorem exp_5_380_0 : expNegUpper (86614532529698936786753 / 876732204975581312000 : ℝ) ≤ (62284966679815921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (540923 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_380_1 : expNegUpper (346855506415054353523171 / 3506928819902325248000 : ℝ) ≤ (22245007333901917 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (270701 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_380 : rowCell 5 380 ≤ (17194381061568379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (62284966679815921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22245007333901917 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_380_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_380_1
  · norm_num [gridPoint]

theorem exp_5_381_0 : expNegUpper (348108427690725973478939 / 3519596645547602432000 : ℝ) ≤ (111225030800051251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (270701 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_381_1 : expNegUpper (34850765148543918628597 / 351959664554760243200 : ℝ) ≤ (12412264587386259 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (270941 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_381 : rowCell 5 381 ≤ (15351537057527717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (111225030800051251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12412264587386259 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_381_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_381_1
  · norm_num [gridPoint]

theorem exp_5_382_0 : expNegUpper (34976427108879956801317 / 353228730949863475200 : ℝ) ≤ (49649055748323071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (270941 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_382_1 : expNegUpper (350165345712746936160761 / 3532287309498634752000 : ℝ) ≤ (88639825310959099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2169451 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_382 : rowCell 5 382 ≤ (548184128100027 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (49649055748323071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (88639825310959099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_382_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_382_1
  · norm_num [gridPoint]

theorem exp_5_383_0 : expNegUpper (351425670305355177478769 / 3545000811755422208000 : ℝ) ≤ (88639820700206239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2169451 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_383_1 : expNegUpper (2748660930385283202161 / 27695318841839236000 : ℝ) ≤ (79116391172935091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2171379 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_383 : rowCell 5 383 ≤ (12232933688261071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (88639820700206239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (79116391172935091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_383_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_383_1
  · norm_num [gridPoint]

theorem sum_5_352_2 : blockSum (rowCell 5) 352 2 ≤ (741359944227227997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_352) (by simpa only [blockSum_one] using cell_5_353) (by norm_num)

theorem sum_5_354_2 : blockSum (rowCell 5) 354 2 ≤ (74376151460979909 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_354) (by simpa only [blockSum_one] using cell_5_355) (by norm_num)

theorem sum_5_352_4 : blockSum (rowCell 5) 352 4 ≤ (1336369155915067269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_352_2 sum_5_354_2 (by norm_num)

theorem sum_5_356_2 : blockSum (rowCell 5) 356 2 ≤ (238645528588925813 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_356) (by simpa only [blockSum_one] using cell_5_357) (by norm_num)

theorem sum_5_358_2 : blockSum (rowCell 5) 358 2 ≤ (76531563035801423 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_358) (by simpa only [blockSum_one] using cell_5_359) (by norm_num)

theorem sum_5_356_4 : blockSum (rowCell 5) 356 4 ≤ (859948872356858741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_356_2 sum_5_358_2 (by norm_num)

theorem sum_5_352_8 : blockSum (rowCell 5) 352 8 ≤ (219631802827192601 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_352_4 sum_5_356_4 (by norm_num)

theorem sum_5_360_2 : blockSum (rowCell 5) 360 2 ≤ (61325085569443593 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_360) (by simpa only [blockSum_one] using cell_5_361) (by norm_num)

theorem sum_5_362_2 : blockSum (rowCell 5) 362 2 ≤ (49114372529871191 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_362) (by simpa only [blockSum_one] using cell_5_363) (by norm_num)

theorem sum_5_360_4 : blockSum (rowCell 5) 360 4 ≤ (3451233065603587 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_360_2 sum_5_362_2 (by norm_num)

theorem sum_5_364_2 : blockSum (rowCell 5) 364 2 ≤ (49143313729924973 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_364) (by simpa only [blockSum_one] using cell_5_365) (by norm_num)

theorem sum_5_366_2 : blockSum (rowCell 5) 366 2 ≤ (157270813569388001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_366) (by simpa only [blockSum_one] using cell_5_367) (by norm_num)

theorem sum_5_364_4 : blockSum (rowCell 5) 364 4 ≤ (353844068489087893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_364_2 sum_5_366_2 (by norm_num)

theorem sum_5_360_8 : blockSum (rowCell 5) 360 8 ≤ (906041358985661813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_360_4 sum_5_364_4 (by norm_num)

theorem sum_5_352_16 : blockSum (rowCell 5) 352 16 ≤ (3102359387257587823 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_352_8 sum_5_360_8 (by norm_num)

theorem sum_5_368_2 : blockSum (rowCell 5) 368 2 ≤ (25152558591587297 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_368) (by simpa only [blockSum_one] using cell_5_369) (by norm_num)

theorem sum_5_370_2 : blockSum (rowCell 5) 370 2 ≤ (10051687295868777 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_370) (by simpa only [blockSum_one] using cell_5_371) (by norm_num)

theorem sum_5_368_4 : blockSum (rowCell 5) 368 4 ≤ (45255933183324851 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_368_2 sum_5_370_2 (by norm_num)

theorem sum_5_372_2 : blockSum (rowCell 5) 372 2 ≤ (80299142008832289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_372) (by simpa only [blockSum_one] using cell_5_373) (by norm_num)

theorem sum_5_374_2 : blockSum (rowCell 5) 374 2 ≤ (64116577171302993 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_374) (by simpa only [blockSum_one] using cell_5_375) (by norm_num)

theorem sum_5_372_4 : blockSum (rowCell 5) 372 4 ≤ (72207859590067641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_372_2 sum_5_374_2 (by norm_num)

theorem sum_5_368_8 : blockSum (rowCell 5) 368 8 ≤ (370695385096759537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_368_4 sum_5_372_4 (by norm_num)

theorem sum_5_376_2 : blockSum (rowCell 5) 376 2 ≤ (51170488066335613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_376) (by simpa only [blockSum_one] using cell_5_377) (by norm_num)

theorem sum_5_378_2 : blockSum (rowCell 5) 378 2 ≤ (1275589387058547 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_378) (by simpa only [blockSum_one] using cell_5_379) (by norm_num)

theorem sum_5_376_4 : blockSum (rowCell 5) 376 4 ≤ (91989348452209117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_376_2 sum_5_378_2 (by norm_num)

theorem sum_5_380_2 : blockSum (rowCell 5) 380 2 ≤ (1017059941221753 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_380) (by simpa only [blockSum_one] using cell_5_381) (by norm_num)

theorem sum_5_382_2 : blockSum (rowCell 5) 382 2 ≤ (12968768445380873 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_382) (by simpa only [blockSum_one] using cell_5_383) (by norm_num)

theorem sum_5_380_4 : blockSum (rowCell 5) 380 4 ≤ (29241727504928921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_380_2 sum_5_382_2 (by norm_num)

theorem sum_5_376_8 : blockSum (rowCell 5) 376 8 ≤ (150472803462066959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_376_4 sum_5_380_4 (by norm_num)

theorem sum_5_368_16 : blockSum (rowCell 5) 368 16 ≤ (508953309139479 / 976562500000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_368_8 sum_5_376_8 (by norm_num)

theorem sum_5_352_32 : blockSum (rowCell 5) 352 32 ≤ (3623527575816414319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_352_16 sum_5_368_16 (by norm_num)

#print axioms sum_5_352_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
