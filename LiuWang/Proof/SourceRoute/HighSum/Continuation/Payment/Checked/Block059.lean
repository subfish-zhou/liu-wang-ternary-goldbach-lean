import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_352_0 : expNegUpper (208266735283044963881 / 2195487537479964800 : ℝ) ≤ (1587260232075726423 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (8393 / 4000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_352_1 : expNegUpper (33361772437017553737079 / 351278005996794368000 : ℝ) ≤ (5680338023132469809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (84003 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_352 : rowCell 3 352 ≤ (438596560391909631 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1587260232075726423 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5680338023132469809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_352_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_352_1
  · norm_num [gridPoint]

theorem exp_3_353_0 : expNegUpper (301398315647444484656039 / 3173530407055282688000 : ℝ) ≤ (5680337670056618767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (84003 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_353_1 : expNegUpper (150875961504822478630359 / 1586765203527641344000 : ℝ) ≤ (2540699730854707749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (131369 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_353 : rowCell 3 353 ≤ (39237777019829177 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5680337670056618767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2540699730854707749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_353_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_353_1
  · norm_num [gridPoint]

theorem exp_3_354_0 : expNegUpper (6057955970559309622239 / 63711631968903424000 : ℝ) ≤ (5081399148249576659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (131369 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_354_1 : expNegUpper (12130126538302909583437 / 127423263937806848000 : ℝ) ≤ (4545021557616945289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (262967 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_354 : rowCell 3 354 ≤ (175491811652284927 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5081399148249576659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4545021557616945289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_354_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_354_1
  · norm_num [gridPoint]

theorem exp_3_355_0 : expNegUpper (33822506382387376009493 / 355295069793423872000 : ℝ) ≤ (4545021279360335421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (262967 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_355_1 : expNegUpper (8465546757479999370511 / 88823767448355968000 : ℝ) ≤ (4064735881605330897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2105573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_355 : rowCell 3 355 ≤ (627831227506315693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4545021279360335421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4064735881605330897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_355_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_355_1
  · norm_num [gridPoint]

theorem exp_3_356_0 : expNegUpper (76478150595086460076391 / 802438124035553408000 : ℝ) ≤ (4064735634626880057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2105573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_356_1 : expNegUpper (61254298487421063449439 / 641950499228442726400 : ℝ) ≤ (181736772386555273 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2107413 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_356 : rowCell 3 356 ≤ (28072617440954743 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4064735634626880057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (181736772386555273 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_356_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_356_1
  · norm_num [gridPoint]

theorem exp_3_357_0 : expNegUpper (61485588667376499300279 / 644374440489873510400 : ℝ) ≤ (1817367614270002219 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2107413 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_357_1 : expNegUpper (153894300476693703020693 / 1610936101224683776000 : ℝ) ≤ (3249807888376067129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2109257 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_357 : rowCell 3 357 ≤ (502027069417226543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1817367614270002219 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3249807888376067129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_357_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_357_1
  · norm_num [gridPoint]

theorem exp_3_358_0 : expNegUpper (17163810572413055522333 / 179667485947904256000 : ℝ) ≤ (3249807693868120267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2109257 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_358_1 : expNegUpper (34367890978940543383337 / 359334971895808512000 : ℝ) ≤ (1452637645722268519 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (32986 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_358 : rowCell 3 358 ≤ (112208545311592147 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3249807693868120267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1452637645722268519 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_358_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_358_1
  · norm_num [gridPoint]

theorem exp_3_359_0 : expNegUpper (12418982130893679829457 / 129847205199237632000 : ℝ) ≤ (726318779714924029 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (32986 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_359_1 : expNegUpper (1554193780003382086011 / 16230900649904704000 : ℝ) ≤ (2596940045246497731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422591 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_359 : rowCell 3 359 ≤ (401226473163060157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (726318779714924029 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2596940045246497731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_359_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_359_1
  · norm_num [gridPoint]

theorem exp_3_360_0 : expNegUpper (1258088073532024726749 / 13138582061311936000 : ℝ) ≤ (1298469946065509489 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422591 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_360_1 : expNegUpper (10076510403753568807321 / 105108656490495488000 : ℝ) ≤ (46420721996466547 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (211481 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_360 : rowCell 3 360 ≤ (179311613913683103 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1298469946065509489 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (46420721996466547 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_360_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_360_1
  · norm_num [gridPoint]

theorem exp_3_361_0 : expNegUpper (34838051909619339513671 / 363397712303948288000 : ℝ) ≤ (2321035963996053149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (211481 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_361_1 : expNegUpper (697578285221902632563 / 7267954246078965760 : ℝ) ≤ (414837022144410981 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2116669 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_361 : rowCell 3 361 ≤ (320503469599878757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2321035963996053149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (414837022144410981 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_361_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_361_1
  · norm_num [gridPoint]

theorem exp_3_362_0 : expNegUpper (6301688762331528252667 / 65656266171429283840 : ℝ) ≤ (1037092495122187441 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2116669 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_362_1 : expNegUpper (315453983493501718810461 / 3282813308571464192000 : ℝ) ≤ (1853356983030588081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2118531 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_362 : rowCell 3 362 ≤ (143199944671100957 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1037092495122187441 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1853356983030588081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_362_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_362_1
  · norm_num [gridPoint]

theorem exp_3_363_0 : expNegUpper (316631765018287849993749 / 3295070044713148928000 : ℝ) ≤ (1853356876179681889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2118531 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_363_1 : expNegUpper (79250774484908970556837 / 823767511178287232000 : ℝ) ≤ (206979297544614989 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2120397 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_363 : rowCell 3 363 ≤ (63973344803917137 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1853356876179681889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (206979297544614989 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_363_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_363_1
  · norm_num [gridPoint]

theorem exp_3_364_0 : expNegUpper (353538286537830016037 / 3674832910178432000 : ℝ) ≤ (413958571400481629 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2120397 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_364_1 : expNegUpper (1415811474135988096147 / 14699331640713728000 : ℝ) ≤ (1479180805830575003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2122267 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_364 : rowCell 3 364 ≤ (11430405854118961 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (413958571400481629 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1479180805830575003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_364_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_364_1
  · norm_num [gridPoint]

theorem exp_3_365_0 : expNegUpper (319742526706192552681067 / 3319652031913783808000 : ℝ) ≤ (184897590226421423 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2122267 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_365_1 : expNegUpper (160058722354362341878353 / 1659826015956891904000 : ℝ) ≤ (132121190054320401 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (106207 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_365 : rowCell 3 365 ≤ (40841429199968457 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (184897590226421423 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (132121190054320401 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_365_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_365_1
  · norm_num [gridPoint]

theorem exp_3_366_0 : expNegUpper (160652990738531555733057 / 1665988641486366976000 : ℝ) ≤ (660605913025755079 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (106207 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_366_1 : expNegUpper (64336539403271323065461 / 666395456594546790400 : ℝ) ≤ (1179969639507711903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2126017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_366 : rowCell 3 366 ≤ (182388399623801437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (660605913025755079 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1179969639507711903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_366_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_366_1
  · norm_num [gridPoint]

theorem exp_3_367_0 : expNegUpper (7174996270866607500389 / 74318341607498649600 : ℝ) ≤ (73748098341891839 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2126017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_367_1 : expNegUpper (2244814920804387243569 / 23224481752343328000 : ℝ) ≤ (65856196034199249 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1063949 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_367 : rowCell 3 367 ≤ (162881129146204651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (73748098341891839 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (65856196034199249 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_367_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_367_1
  · norm_num [gridPoint]

theorem exp_3_368_0 : expNegUpper (20278068052145867347769 / 209793518750493728000 : ℝ) ≤ (1053699078010786803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1063949 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_368_1 : expNegUpper (324829409439488773725663 / 3356696300007899648000 : ℝ) ≤ (18816555956800383 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1064891 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_368 : rowCell 3 368 ≤ (145442691744780793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1053699078010786803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18816555956800383 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_368_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_368_1
  · norm_num [gridPoint]

theorem exp_3_369_0 : expNegUpper (13041150456216455133423 / 134763602639364608000 : ℝ) ≤ (37633109838326843 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1064891 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_369_1 : expNegUpper (6528217790793325880231 / 67381801319682304000 : ℝ) ≤ (83994658943082727 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (213167 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_369 : rowCell 3 369 ≤ (129855664451007711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (37633109838326843 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (83994658943082727 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_369_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_369_1
  · norm_num [gridPoint]

theorem exp_3_370_0 : expNegUpper (18200769994142693697799 / 187861481681449216000 : ℝ) ≤ (83994654345190689 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (213167 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_370_1 : expNegUpper (36444199876522552295629 / 375722963362898432000 : ℝ) ≤ (93724150890859241 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1066781 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_370 : rowCell 3 370 ≤ (57962625447005929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (83994654345190689 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (93724150890859241 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_370_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_370_1
  · norm_num [gridPoint]

theorem exp_3_371_0 : expNegUpper (329204394294143848967789 / 3393946112853811712000 : ℝ) ≤ (749793166383566707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1066781 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_371_1 : expNegUpper (16479507373946872520103 / 169697305642690585600 : ℝ) ≤ (334618479035484901 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1067729 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_371 : rowCell 3 371 ≤ (51738475792551121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (749793166383566707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (334618479035484901 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_371_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_371_1
  · norm_num [gridPoint]

theorem exp_3_372_0 : expNegUpper (16540018729823805614343 / 170320419687364633600 : ℝ) ≤ (334618460985442257 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1067729 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_372_1 : expNegUpper (331187945302708379964811 / 3406408393747292672000 : ℝ) ≤ (14931629553189329 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2137357 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_372 : rowCell 3 372 ≤ (18470894260768737 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (334618460985442257 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14931629553189329 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_372_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_372_1
  · norm_num [gridPoint]

theorem exp_3_373_0 : expNegUpper (36933534532655991471851 / 379877056994058752000 : ℝ) ≤ (597265150144891307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2137357 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_373_1 : expNegUpper (18488400130686355893221 / 189938528497029376000 : ℝ) ≤ (26648552911585473 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2139259 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_373 : rowCell 3 373 ≤ (10302229970176899 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (597265150144891307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26648552911585473 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_373_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_373_1
  · norm_num [gridPoint]

theorem exp_3_374_0 : expNegUpper (267206970303012742861 / 2745121176361216000 : ℝ) ≤ (532971029899758103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2139259 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_374_1 : expNegUpper (535039885792342680753 / 5490242352722432000 : ℝ) ≤ (2972141601285151 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1070583 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_374 : rowCell 3 374 ≤ (14708344815463867 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (532971029899758103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2972141601285151 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_374_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_374_1
  · norm_num [gridPoint]

theorem exp_3_375_0 : expNegUpper (335621090843400775004697 / 3443932266262266368000 : ℝ) ≤ (118885657777567727 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1070583 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_375_1 : expNegUpper (42001766762328291858977 / 430491533282783296000 : ℝ) ≤ (212126554202175501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (85723 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_375 : rowCell 3 375 ≤ (1312278274712819 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (118885657777567727 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (212126554202175501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_375_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_375_1
  · norm_num [gridPoint]

theorem exp_3_376_0 : expNegUpper (4683874370557598739737 / 48006748616371776000 : ℝ) ≤ (13257908943066591 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (85723 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_376_1 : expNegUpper (7502973972887322911347 / 76810797786194841600 : ℝ) ≤ (37845178805241721 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2144989 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_376 : rowCell 3 376 ≤ (58533960609052011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13257908943066591 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37845178805241721 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_376_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_376_1
  · norm_num [gridPoint]

theorem exp_3_377_0 : expNegUpper (67772462876268715614883 / 693812474560204902400 : ℝ) ≤ (47306471046163897 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2144989 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_377_1 : expNegUpper (169629511328231205308043 / 1734531186400512256000 : ℝ) ≤ (4219454905124719 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1073453 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_377 : rowCell 3 377 ≤ (26105979186303841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47306471046163897 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4219454905124719 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_377_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_377_1
  · norm_num [gridPoint]

theorem exp_3_378_0 : expNegUpper (170245589969664414086907 / 1740830841764518144000 : ℝ) ≤ (42194546872596309 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1073453 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_378_1 : expNegUpper (340889725720563620417293 / 3481661683529036288000 : ℝ) ≤ (60209167815151747 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2148827 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_378 : rowCell 3 378 ≤ (23283723596589401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42194546872596309 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (60209167815151747 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_378_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_378_1
  · norm_num [gridPoint]

theorem exp_3_379_0 : expNegUpper (1520558050428628916837 / 15530150366945792000 : ℝ) ≤ (301045823643913791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2148827 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_379_1 : expNegUpper (380584386627302007937 / 3882537591736448000 : ℝ) ≤ (134226946451574307 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (67211 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_379 : rowCell 3 379 ≤ (1297763468453543 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (301045823643913791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (134226946451574307 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_379_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_379_1
  · norm_num [gridPoint]

theorem exp_3_380_0 : expNegUpper (85941367148755064786753 / 876732204975581312000 : ℝ) ≤ (53690775848228061 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (67211 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_380_1 : expNegUpper (344167699380825617523171 / 3506928819902325248000 : ℝ) ≤ (239363449271305789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (53817 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_380 : rowCell 3 380 ≤ (7406099167451731 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (53690775848228061 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (239363449271305789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_380_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_380_1
  · norm_num [gridPoint]

theorem exp_3_381_0 : expNegUpper (345410911677403733478939 / 3519596645547602432000 : ℝ) ≤ (239363437177361679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (53817 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_381_1 : expNegUpper (34581498996166369828597 / 351959664554760243200 : ℝ) ≤ (42680281380570061 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2154611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_381 : rowCell 3 381 ≤ (16508009605621831 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (239363437177361679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42680281380570061 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_381_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_381_1
  · norm_num [gridPoint]

theorem exp_3_382_0 : expNegUpper (3856243339843673066813 / 39247636772207052800 : ℝ) ≤ (106700698099027943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2154611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_382_1 : expNegUpper (38607536633269410684529 / 392476367722070528000 : ℝ) ≤ (190234070132740313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2156547 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_382 : rowCell 3 382 ≤ (29433460846080941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (106700698099027943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (190234070132740313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_382_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_382_1
  · norm_num [gridPoint]

theorem exp_3_383_0 : expNegUpper (348718445312939433478769 / 3545000811755422208000 : ℝ) ≤ (190234060658467001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2156547 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_383_1 : expNegUpper (2727548660831619202161 / 27695318841839236000 : ℝ) ≤ (169563026581020777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1079243 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_383 : rowCell 3 383 ≤ (3279590857087377 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (190234060658467001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (169563026581020777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_383_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_383_1
  · norm_num [gridPoint]

theorem sum_3_352_2 : blockSum (rowCell 3) 352 2 ≤ (830974330590201401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_352) (by simpa only [blockSum_one] using cell_3_353) (by norm_num)

theorem sum_3_354_2 : blockSum (rowCell 3) 354 2 ≤ (1329798474115455401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_354) (by simpa only [blockSum_one] using cell_3_355) (by norm_num)

theorem sum_3_352_4 : blockSum (rowCell 3) 352 4 ≤ (2991747135295858203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_352_2 sum_3_354_2 (by norm_num)

theorem sum_3_356_2 : blockSum (rowCell 3) 356 2 ≤ (1063479418236321403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_356) (by simpa only [blockSum_one] using cell_3_357) (by norm_num)

theorem sum_3_358_2 : blockSum (rowCell 3) 358 2 ≤ (170012130881885749 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_358) (by simpa only [blockSum_one] using cell_3_359) (by norm_num)

theorem sum_3_356_4 : blockSum (rowCell 3) 356 4 ≤ (478385018161437537 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_356_2 sum_3_358_2 (by norm_num)

theorem sum_3_352_8 : blockSum (rowCell 3) 352 8 ≤ (4905287207941608351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_352_4 sum_3_356_4 (by norm_num)

theorem sum_3_360_2 : blockSum (rowCell 3) 360 2 ≤ (679126697427244963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_360) (by simpa only [blockSum_one] using cell_3_361) (by norm_num)

theorem sum_3_362_2 : blockSum (rowCell 3) 362 2 ≤ (271146634278935231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_362) (by simpa only [blockSum_one] using cell_3_363) (by norm_num)

theorem sum_3_360_4 : blockSum (rowCell 3) 360 4 ≤ (48856798639404617 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_360_2 sum_3_362_2 (by norm_num)

theorem sum_3_364_2 : blockSum (rowCell 3) 364 2 ≤ (86563052616444301 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_364) (by simpa only [blockSum_one] using cell_3_365) (by norm_num)

theorem sum_3_366_2 : blockSum (rowCell 3) 366 2 ≤ (43158691096250761 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_366) (by simpa only [blockSum_one] using cell_3_367) (by norm_num)

theorem sum_3_364_4 : blockSum (rowCell 3) 364 4 ≤ (778084791852227593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_364_2 sum_3_366_2 (by norm_num)

theorem sum_3_360_8 : blockSum (rowCell 3) 360 8 ≤ (999752378918671509 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_360_4 sum_3_364_4 (by norm_num)

theorem sum_3_352_16 : blockSum (rowCell 3) 352 16 ≤ (6904791965778951369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_352_8 sum_3_360_8 (by norm_num)

theorem sum_3_368_2 : blockSum (rowCell 3) 368 2 ≤ (34412294524473563 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_368) (by simpa only [blockSum_one] using cell_3_369) (by norm_num)

theorem sum_3_370_2 : blockSum (rowCell 3) 370 2 ≤ (2194022024791141 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_370) (by simpa only [blockSum_one] using cell_3_371) (by norm_num)

theorem sum_3_368_4 : blockSum (rowCell 3) 368 4 ≤ (123675139668725651 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_368_2 sum_3_370_2 (by norm_num)

theorem sum_3_372_2 : blockSum (rowCell 3) 372 2 ≤ (174772311065258877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_372) (by simpa only [blockSum_one] using cell_3_373) (by norm_num)

theorem sum_3_374_2 : blockSum (rowCell 3) 374 2 ≤ (27831127562592057 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_374) (by simpa only [blockSum_one] using cell_3_375) (by norm_num)

theorem sum_3_372_4 : blockSum (rowCell 3) 372 4 ≤ (156963974439109581 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_372_2 sum_3_374_2 (by norm_num)

theorem sum_3_368_8 : blockSum (rowCell 3) 368 8 ≤ (404314253776560883 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_368_4 sum_3_372_4 (by norm_num)

theorem sum_3_376_2 : blockSum (rowCell 3) 376 2 ≤ (110745918981659693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_376) (by simpa only [blockSum_one] using cell_3_377) (by norm_num)

theorem sum_3_378_2 : blockSum (rowCell 3) 378 2 ≤ (44047939091846089 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_378) (by simpa only [blockSum_one] using cell_3_379) (by norm_num)

theorem sum_3_376_4 : blockSum (rowCell 3) 376 4 ≤ (198841797165351871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_376_2 sum_3_378_2 (by norm_num)

theorem sum_3_380_2 : blockSum (rowCell 3) 380 2 ≤ (70046515048502317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_380) (by simpa only [blockSum_one] using cell_3_381) (by norm_num)

theorem sum_3_382_2 : blockSum (rowCell 3) 382 2 ≤ (55670187702779957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_382) (by simpa only [blockSum_one] using cell_3_383) (by norm_num)

theorem sum_3_380_4 : blockSum (rowCell 3) 380 4 ≤ (62858351375641137 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_380_2 sum_3_382_2 (by norm_num)

theorem sum_3_376_8 : blockSum (rowCell 3) 376 8 ≤ (64911699983326829 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_376_4 sum_3_380_4 (by norm_num)

theorem sum_3_368_16 : blockSum (rowCell 3) 368 16 ≤ (1133187007469755911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_368_8 sum_3_376_8 (by norm_num)

theorem sum_3_352_32 : blockSum (rowCell 3) 352 32 ≤ (100474737165608841 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_352_16 sum_3_368_16 (by norm_num)

#print axioms sum_3_352_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
