import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_352_0 : expNegUpper (616810406422677291643 / 6586462612439894400 : ℝ) ≤ (21356744168053694909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1039229 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_352_1 : expNegUpper (98809376647592821211237 / 1053834017990383104000 : ℝ) ≤ (9531709851189125547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (130019 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_352 : rowCell 2 352 ≤ (736868666105718711 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21356744168053694909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9531709851189125547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_352_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_352_1
  · norm_num [gridPoint]

theorem exp_2_353_0 : expNegUpper (297555930188424708656039 / 3173530407055282688000 : ℝ) ≤ (9531709298219309877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (130019 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_353_1 : expNegUpper (148958409642472654630359 / 1586765203527641344000 : ℝ) ≤ (8507137933268489239 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2082153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_353 : rowCell 2 353 ≤ (2630817893793799703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9531709298219309877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8507137933268489239 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_353_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_353_1
  · norm_num [gridPoint]

theorem exp_2_354_0 : expNegUpper (5980962626692511542239 / 63711631968903424000 : ℝ) ≤ (8507137443468444249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2082153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_354_1 : expNegUpper (11976431119942118543437 / 127423263937806848000 : ℝ) ≤ (15183551044303068809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (416801 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_354 : rowCell 2 354 ≤ (1173947197320126393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8507137443468444249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15183551044303068809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_354_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_354_1
  · norm_num [gridPoint]

theorem exp_2_355_0 : expNegUpper (14311695643515540575497 / 152269315625753088000 : ℝ) ≤ (15183550176702808879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (416801 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_355_1 : expNegUpper (3582262096142143730219 / 38067328906438272000 : ℝ) ≤ (2709634761473092147 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1042931 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_355 : rowCell 2 355 ≤ (2095143126576525157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15183550176702808879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2709634761473092147 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_355_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_355_1
  · norm_num [gridPoint]

theorem exp_2_356_0 : expNegUpper (75512092929591420076391 / 802438124035553408000 : ℝ) ≤ (13548173039041693247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1042931 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_356_1 : expNegUpper (60482908701889057049439 / 641950499228442726400 : ℝ) ≤ (12087485993342100573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2087721 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_356 : rowCell 2 356 ≤ (1869375288678838153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13548173039041693247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12087485993342100573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_356_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_356_1
  · norm_num [gridPoint]

theorem exp_2_357_0 : expNegUpper (60711286188116441700279 / 644374440489873510400 : ℝ) ≤ (2417497062601401587 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2087721 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_357_1 : expNegUpper (151962185145703623020693 / 1610936101224683776000 : ℝ) ≤ (10782992949999573133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (417917 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_357 : rowCell 2 357 ≤ (208466977829219289 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2417497062601401587 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10782992949999573133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_357_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_357_1
  · norm_num [gridPoint]

theorem exp_2_358_0 : expNegUpper (50844966028802430566999 / 539002457843712768000 : ℝ) ≤ (1078299234764007901 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (417917 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_358_1 : expNegUpper (101813168804721534150011 / 1078004915687425536000 : ℝ) ≤ (9618139328818156439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (522863 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_358 : rowCell 2 358 ≤ (1487668850989075097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1078299234764007901 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9618139328818156439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_358_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_358_1
  · norm_num [gridPoint]

theorem exp_2_359_0 : expNegUpper (12263539096296058069457 / 129847205199237632000 : ℝ) ≤ (4809069397776506327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (522863 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_359_1 : expNegUpper (1534799809350280006011 / 16230900649904704000 : ℝ) ≤ (4289053923717716727 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2093323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_359 : rowCell 2 359 ≤ (1326886653397060801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4809069397776506327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4289053923717716727 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_359_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_359_1
  · norm_num [gridPoint]

theorem exp_2_360_0 : expNegUpper (1242389050954360726749 / 13138582061311936000 : ℝ) ≤ (1072263421923525523 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2093323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_360_1 : expNegUpper (9951153117787744807321 / 105108656490495488000 : ℝ) ≤ (7649638697468552383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2095197 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_360 : rowCell 2 360 ≤ (591670911624163511 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1072263421923525523 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7649638697468552383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_360_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_360_1
  · norm_num [gridPoint]

theorem exp_2_361_0 : expNegUpper (103213942617664418541013 / 1090193136911844864000 : ℝ) ≤ (7649638279654742131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2095197 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_361_1 : expNegUpper (2066779138337303417689 / 21803862738236897280 : ℝ) ≤ (1705216876498452217 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (83883 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_361 : rowCell 2 361 ≤ (1055202282734534133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7649638279654742131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1705216876498452217 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_361_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_361_1
  · norm_num [gridPoint]

theorem exp_2_362_0 : expNegUpper (889075762996215670381 / 9379466595918469120 : ℝ) ≤ (682086713622057237 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (83883 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_362_1 : expNegUpper (44507620594274416972923 / 468973329795923456000 : ℝ) ≤ (6081179967977845529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (524739 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_362 : rowCell 2 362 ≤ (235207216630273453 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (682086713622057237 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6081179967977845529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_362_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_362_1
  · norm_num [gridPoint]

theorem exp_2_363_0 : expNegUpper (312716562216066793993749 / 3295070044713148928000 : ℝ) ≤ (3040589820377444333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (524739 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_363_1 : expNegUpper (78273794217933738556837 / 823767511178287232000 : ℝ) ≤ (5421081455404004541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2100841 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_363 : rowCell 2 363 ≤ (838755213194610073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3040589820377444333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5421081455404004541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_363_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_363_1
  · norm_num [gridPoint]

theorem exp_2_364_0 : expNegUpper (1047539911158352768111 / 11024498730535296000 : ℝ) ≤ (2710540582932218849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2100841 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_364_1 : expNegUpper (4195231718378350208441 / 44097994922141184000 : ℝ) ≤ (966416015741810549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (210273 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_364 : rowCell 2 364 ≤ (149533945955770919 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2710540582932218849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (966416015741810549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_364_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_364_1
  · norm_num [gridPoint]

theorem exp_2_365_0 : expNegUpper (315812760435331240681067 / 3319652031913783808000 : ℝ) ≤ (4832079822539093947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (210273 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_365_1 : expNegUpper (158097480086091749878353 / 1659826015956891904000 : ℝ) ≤ (2153290914619948173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1052311 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_365 : rowCell 2 365 ≤ (666399418164051743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4832079822539093947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2153290914619948173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_365_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_365_1
  · norm_num [gridPoint]

theorem exp_2_366_0 : expNegUpper (158684466735940835733057 / 1665988641486366976000 : ℝ) ≤ (4306581602616442579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1052311 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_366_1 : expNegUpper (63550586149099060665461 / 666395456594546790400 : ℝ) ≤ (119931142793318739 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1053259 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_366 : rowCell 2 366 ≤ (29694768675859829 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4306581602616442579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (119931142793318739 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_366_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_366_1
  · norm_num [gridPoint]

theorem exp_2_367_0 : expNegUpper (21262033496633051301167 / 222955024822495948800 : ℝ) ≤ (153511854756855709 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1053259 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_367_1 : expNegUpper (6652422928971881730707 / 69673445257029984000 : ℝ) ≤ (3419653761317017877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2108417 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_367 : rowCell 2 367 ≤ (16538118245698009 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (153511854756855709 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3419653761317017877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_367_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_367_1
  · norm_num [gridPoint]

theorem exp_2_368_0 : expNegUpper (20031092335032011347769 / 209793518750493728000 : ℝ) ≤ (68393071680180547 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2108417 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_368_1 : expNegUpper (320885079699987205725663 / 3356696300007899648000 : ℝ) ≤ (152336346859045763 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (26379 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_368 : rowCell 2 368 ≤ (235767138621960061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (68393071680180547 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (152336346859045763 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_368_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_368_1
  · norm_num [gridPoint]

theorem exp_2_369_0 : expNegUpper (1840399246841540310489 / 19251943234194944000 : ℝ) ≤ (3046726780370246591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (26379 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_369_1 : expNegUpper (921312223045270280033 / 9625971617097472000 : ℝ) ≤ (2714166014425248943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2112227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_369 : rowCell 2 369 ≤ (420089478398607859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3046726780370246591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2714166014425248943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_369_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_369_1
  · norm_num [gridPoint]

theorem exp_2_370_0 : expNegUpper (53941280825351089093397 / 563584445044347648000 : ℝ) ≤ (2714165875755961459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2112227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_370_1 : expNegUpper (108012968560187048886887 / 1127168890088695296000 : ℝ) ≤ (2417636650641402981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2114137 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_370 : rowCell 2 370 ≤ (187107825414364063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2714165875755961459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2417636650641402981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_370_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_370_1
  · norm_num [gridPoint]

theorem exp_2_371_0 : expNegUpper (325230937617361768967789 / 3393946112853811712000 : ℝ) ≤ (1208818264013345069 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2114137 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_371_1 : expNegUpper (16281198626823774920103 / 169697305642690585600 : ℝ) ≤ (134579119627126359 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (42321 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_371 : rowCell 2 371 ≤ (3333143127452299 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1208818264013345069 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (134579119627126359 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_371_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_371_1
  · norm_num [gridPoint]

theorem exp_2_372_0 : expNegUpper (16340981809268695214343 / 170320419687364633600 : ℝ) ≤ (107663290281283337 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (42321 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_372_1 : expNegUpper (327214488625926299964811 / 3406408393747292672000 : ℝ) ≤ (1917593619134070231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2117967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_372 : rowCell 2 372 ≤ (296850726666244453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (107663290281283337 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1917593619134070231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_372_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_372_1
  · norm_num [gridPoint]

theorem exp_2_373_0 : expNegUpper (109471263549493862415553 / 1139631170982176256000 : ℝ) ≤ (479398380823835989 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2117967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_373_1 : expNegUpper (54801743990208699679663 / 569815585491088128000 : ℝ) ≤ (53360273235382271 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (132493 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_373 : rowCell 2 373 ≤ (264347172642853491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (479398380823835989 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (53360273235382271 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_373_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_373_1
  · norm_num [gridPoint]

theorem exp_2_374_0 : expNegUpper (264010728799218771661 / 2745121176361216000 : ℝ) ≤ (853764329406924471 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (132493 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_374_1 : expNegUpper (528659053559666943153 / 5490242352722432000 : ℝ) ≤ (38007760023182911 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (530453 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_374 : rowCell 2 374 ≤ (29422115530997627 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (853764329406924471 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38007760023182911 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_374_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_374_1
  · norm_num [gridPoint]

theorem exp_2_375_0 : expNegUpper (331618507229338183004697 / 3443932266262266368000 : ℝ) ≤ (760155163023051097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (530453 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_375_1 : expNegUpper (41502354027360483858977 / 430491533282783296000 : ℝ) ≤ (135347289932007547 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (106187 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_375 : rowCell 2 375 ≤ (26194856838539777 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (760155163023051097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (135347289932007547 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_375_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_375_1
  · norm_num [gridPoint]

theorem exp_2_376_0 : expNegUpper (1983506484117645174173 / 20574320835587904000 : ℝ) ≤ (1353472833140051637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (106187 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_376_1 : expNegUpper (3177440430151113704863 / 32918913336940646400 : ℝ) ≤ (602407230664288149 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2125671 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_376 : rowCell 2 376 ≤ (93276303986946737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1353472833140051637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (602407230664288149 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_376_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_376_1
  · norm_num [gridPoint]

theorem exp_2_377_0 : expNegUpper (66969033459728146014883 / 693812474560204902400 : ℝ) ≤ (1204814402844178871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2125671 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_377_1 : expNegUpper (167624578654039845308043 / 1734531186400512256000 : ℝ) ≤ (1072369226891595799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1063803 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_377 : rowCell 2 377 ≤ (16605427618750003 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1204814402844178871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1072369226891595799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_377_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_377_1
  · norm_num [gridPoint]

theorem exp_2_378_0 : expNegUpper (168233375561152926086907 / 1740830841764518144000 : ℝ) ≤ (1072369175212796767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1063803 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_378_1 : expNegUpper (336872578637860772417293 / 3481661683529036288000 : ℝ) ≤ (954382197544091653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (266193 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_378 : rowCell 2 378 ≤ (29558506202173753 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1072369175212796767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (954382197544091653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_378_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_378_1
  · norm_num [gridPoint]

theorem exp_2_379_0 : expNegUpper (4507918010601312030511 / 46590451100837376000 : ℝ) ≤ (477191075941603101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (266193 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_379_1 : expNegUpper (1128338397158496103811 / 11647612775209344000 : ℝ) ≤ (212321704107220277 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1065743 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_379 : rowCell 2 379 ≤ (1052201293225249 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (477191075941603101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (212321704107220277 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_379_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_379_1
  · norm_num [gridPoint]

theorem exp_2_380_0 : expNegUpper (84931619077339256786753 / 876732204975581312000 : ℝ) ≤ (424643388044435677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1065743 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_380_1 : expNegUpper (340135988829482513523171 / 3506928819902325248000 : ℝ) ≤ (3778424548220057 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (266679 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_380 : rowCell 2 380 ≤ (14629497161298839 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (424643388044435677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3778424548220057 / 5000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_380_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_380_1
  · norm_num [gridPoint]

theorem exp_2_381_0 : expNegUpper (341364637657420373478939 / 3519596645547602432000 : ℝ) ≤ (755684874008118097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (266679 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_381_1 : expNegUpper (34177599767600046628597 / 351959664554760243200 : ℝ) ≤ (672328742770071957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2135381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_381 : rowCell 2 381 ≤ (104132035916449443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (755684874008118097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (672328742770071957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_381_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_381_1
  · norm_num [gridPoint]

theorem exp_2_382_0 : expNegUpper (11433611494387569600439 / 117742910316621158400 : ℝ) ≤ (336164355646312221 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2135381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_382_1 : expNegUpper (114473851893147112053587 / 1177429103166211584000 : ℝ) ≤ (299052485897610133 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2137333 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_382 : rowCell 2 382 ≤ (46320582788013893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (336164355646312221 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (299052485897610133 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_382_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_382_1
  · norm_num [gridPoint]

theorem exp_2_383_0 : expNegUpper (49236801117759402496967 / 506428687393631744000 : ℝ) ≤ (598104943993491693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2137333 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_383_1 : expNegUpper (385125750928731886023 / 3956474120262748000 : ℝ) ≤ (266010145222920393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2139289 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_383 : rowCell 2 383 ≤ (82409747442206441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (598104943993491693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (266010145222920393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_383_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_383_1
  · norm_num [gridPoint]

theorem sum_2_352_2 : blockSum (rowCell 2) 352 2 ≤ (5578292558216674547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_352) (by simpa only [blockSum_one] using cell_2_353) (by norm_num)

theorem sum_2_354_2 : blockSum (rowCell 2) 354 2 ≤ (4443037521216777943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_354) (by simpa only [blockSum_one] using cell_2_355) (by norm_num)

theorem sum_2_352_4 : blockSum (rowCell 2) 352 4 ≤ (1002133007943345249 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_352_2 sum_2_354_2 (by norm_num)

theorem sum_2_356_2 : blockSum (rowCell 2) 356 2 ≤ (707422222262518493 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_356) (by simpa only [blockSum_one] using cell_2_357) (by norm_num)

theorem sum_2_358_2 : blockSum (rowCell 2) 358 2 ≤ (1407277752193067949 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_358) (by simpa only [blockSum_one] using cell_2_359) (by norm_num)

theorem sum_2_356_4 : blockSum (rowCell 2) 356 4 ≤ (6351666615698728363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_356_2 sum_2_358_2 (by norm_num)

theorem sum_2_352_8 : blockSum (rowCell 2) 352 8 ≤ (16372996695132180853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_352_4 sum_2_356_4 (by norm_num)

theorem sum_2_360_2 : blockSum (rowCell 2) 360 2 ≤ (447708821196572231 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_360) (by simpa only [blockSum_one] using cell_2_361) (by norm_num)

theorem sum_2_362_2 : blockSum (rowCell 2) 362 2 ≤ (355916815943140777 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_362) (by simpa only [blockSum_one] using cell_2_363) (by norm_num)

theorem sum_2_360_4 : blockSum (rowCell 2) 360 4 ≤ (50226602321232063 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_360_2 sum_2_362_2 (by norm_num)

theorem sum_2_364_2 : blockSum (rowCell 2) 364 2 ≤ (707034573971453169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_364) (by simpa only [blockSum_one] using cell_2_365) (by norm_num)

theorem sum_2_366_2 : blockSum (rowCell 2) 366 2 ≤ (280778789344883217 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_366) (by simpa only [blockSum_one] using cell_2_367) (by norm_num)

theorem sum_2_364_4 : blockSum (rowCell 2) 364 4 ≤ (1268592152661219603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_364_2 sum_2_366_2 (by norm_num)

theorem sum_2_360_8 : blockSum (rowCell 2) 360 8 ≤ (3277656245510502123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_360_4 sum_2_364_4 (by norm_num)

theorem sum_2_352_16 : blockSum (rowCell 2) 352 16 ≤ (22928309186153185099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_352_8 sum_2_360_8 (by norm_num)

theorem sum_2_368_2 : blockSum (rowCell 2) 368 2 ≤ (891623755642527981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_368) (by simpa only [blockSum_one] using cell_2_369) (by norm_num)

theorem sum_2_370_2 : blockSum (rowCell 2) 370 2 ≤ (353764981786979013 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_370) (by simpa only [blockSum_one] using cell_2_371) (by norm_num)

theorem sum_2_368_4 : blockSum (rowCell 2) 368 4 ≤ (1599153719216486007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_368_2 sum_2_370_2 (by norm_num)

theorem sum_2_372_2 : blockSum (rowCell 2) 372 2 ≤ (70149737413637243 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_372) (by simpa only [blockSum_one] using cell_2_373) (by norm_num)

theorem sum_2_374_2 : blockSum (rowCell 2) 374 2 ≤ (13904243092384351 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_374) (by simpa only [blockSum_one] using cell_2_375) (by norm_num)

theorem sum_2_372_4 : blockSum (rowCell 2) 372 4 ≤ (125766709783174647 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_372_2 sum_2_374_2 (by norm_num)

theorem sum_2_368_8 : blockSum (rowCell 2) 368 8 ≤ (2605287397481883183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_368_4 sum_2_372_4 (by norm_num)

theorem sum_2_376_2 : blockSum (rowCell 2) 376 2 ≤ (11018965130043547 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_376) (by simpa only [blockSum_one] using cell_2_377) (by norm_num)

theorem sum_2_378_2 : blockSum (rowCell 2) 378 2 ≤ (27931769266402489 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_378) (by simpa only [blockSum_one] using cell_2_379) (by norm_num)

theorem sum_2_376_4 : blockSum (rowCell 2) 376 4 ≤ (315962288412709197 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_376_2 sum_2_378_2 (by norm_num)

theorem sum_2_380_2 : blockSum (rowCell 2) 380 2 ≤ (44233602641368031 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_380) (by simpa only [blockSum_one] using cell_2_381) (by norm_num)

theorem sum_2_382_2 : blockSum (rowCell 2) 382 2 ≤ (175050913018234227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_382) (by simpa only [blockSum_one] using cell_2_383) (by norm_num)

theorem sum_2_380_4 : blockSum (rowCell 2) 380 4 ≤ (198109463112537191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_380_2 sum_2_382_2 (by norm_num)

theorem sum_2_376_8 : blockSum (rowCell 2) 376 8 ≤ (128517937881311597 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_376_4 sum_2_380_4 (by norm_num)

theorem sum_2_368_16 : blockSum (rowCell 2) 368 16 ≤ (3633430900532375959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_368_8 sum_2_376_8 (by norm_num)

theorem sum_2_352_32 : blockSum (rowCell 2) 352 32 ≤ (13280870043342780529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_352_16 sum_2_368_16 (by norm_num)

#print axioms sum_2_352_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
