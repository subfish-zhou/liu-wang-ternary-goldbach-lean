import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_384_0 : expNegUpper (108222636446195377689 / 1111792860099364000 : ℝ) ≤ (53202026589283057 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2139289 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_384_1 : expNegUpper (13869174365057856566503 / 142309486092718592000 : ℝ) ≤ (473188596396980879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2141249 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_384 : rowCell 2 384 ≤ (14660146671102053 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (53202026589283057 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (473188596396980879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_384_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_384_1
  · norm_num [gridPoint]

theorem exp_2_385_0 : expNegUpper (115990947078164636040109 / 1190165443728754176000 : ℝ) ≤ (473188574715019511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2141249 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_385_1 : expNegUpper (58065270759114652624621 / 595082721864377088000 : ℝ) ≤ (420819517212798529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (535803 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_385 : rowCell 2 385 ≤ (65191873273771583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (473188574715019511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (420819517212798529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_385_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_385_1
  · norm_num [gridPoint]

theorem exp_2_386_0 : expNegUpper (174819415818330281377207 / 1791639174180157696000 : ℝ) ≤ (210409749033940851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (535803 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_386_1 : expNegUpper (2800475832873655370889 / 28666226786882523136 : ℝ) ≤ (93552038340958893 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1072589 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_386 : rowCell 2 386 ≤ (57974130625056407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (210409749033940851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (93552038340958893 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_386_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_386_1
  · norm_num [gridPoint]

theorem exp_2_387_0 : expNegUpper (2810483342613310553889 / 28768665630720987136 : ℝ) ≤ (374208136460605001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1072589 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_387_1 : expNegUpper (87933233195585519432959 / 899020800960030848000 : ℝ) ≤ (41590738809338583 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (536787 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_387 : rowCell 2 387 ≤ (25775132919290433 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (374208136460605001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41590738809338583 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_387_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_387_1
  · norm_num [gridPoint]

theorem exp_2_388_0 : expNegUpper (29415634149736860357877 / 300742574802140544000 : ℝ) ≤ (83181473888001569 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (536787 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_388_1 : expNegUpper (117803998522144010529641 / 1202970299208562176000 : ℝ) ≤ (29581230624363109 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1074561 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_388 : rowCell 2 388 ≤ (45833570377228553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (83181473888001569 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29581230624363109 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_388_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_388_1
  · norm_num [gridPoint]

theorem exp_2_389_0 : expNegUpper (14186816701581388986347 / 144870457188680192000 : ℝ) ≤ (295812293070561527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1074561 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_389_1 : expNegUpper (7101933549076308593229 / 72435228594340096000 : ℝ) ≤ (262967649397861341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2151099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_389 : rowCell 2 389 ≤ (20373367716825979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (295812293070561527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (262967649397861341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_389_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_389_1
  · norm_num [gridPoint]

theorem exp_2_390_0 : expNegUpper (25454203646219976218403 / 259616771436719872000 : ℝ) ≤ (262967637770305029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2151099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_390_1 : expNegUpper (50969569776690131239783 / 519233542873439744000 : ℝ) ≤ (58436624686296151 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2153079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_390 : rowCell 2 390 ≤ (3622084110131653 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (262967637770305029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (58436624686296151 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_390_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_390_1
  · norm_num [gridPoint]

theorem exp_2_391_0 : expNegUpper (3850031401202320410973 / 39220763535665664000 : ℝ) ≤ (233746488482710167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2153079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_391_1 : expNegUpper (96366381319305684239 / 980519088391641600 : ℝ) ≤ (207751819975490021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2155063 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_391 : rowCell 2 391 ≤ (2012153331963029 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (233746488482710167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (207751819975490021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_391_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_391_1
  · norm_num [gridPoint]

theorem exp_2_392_0 : expNegUpper (8993815883152044121907 / 91511251395637260800 : ℝ) ≤ (3246122045603447 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2155063 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_392_1 : expNegUpper (360184537659112756462311 / 3660450055825490432000 : ℝ) ≤ (18462976647054551 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (43141 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_392 : rowCell 2 392 ≤ (28612817153541429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3246122045603447 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18462976647054551 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_392_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_392_1
  · norm_num [gridPoint]

theorem exp_2_393_0 : expNegUpper (361458006082216213754079 / 3673391941139829248000 : ℝ) ≤ (92314879239169353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (43141 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_393_1 : expNegUpper (180945897941528199343619 / 1836695970569914624000 : ℝ) ≤ (640878976933891 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2159041 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_393 : rowCell 2 393 ≤ (198649503032787 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (92314879239169353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (640878976933891 / 3906250000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_393_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_393_1
  · norm_num [gridPoint]

theorem exp_2_394_0 : expNegUpper (2421126950483718610553 / 24575711098399488000 : ℝ) ≤ (82032505521490849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2159041 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_394_1 : expNegUpper (4848062975626489583639 / 49151422196798976000 : ℝ) ≤ (145776618858963549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (540259 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_394 : rowCell 2 394 ≤ (22593930025789213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (82032505521490849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (145776618858963549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_394_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_394_1
  · norm_num [gridPoint]

theorem exp_2_395_0 : expNegUpper (364885754789445145091957 / 3699344226685772288000 : ℝ) ≤ (145776612636927491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (540259 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_395_1 : expNegUpper (91330832379560590862109 / 924836056671443072000 : ℝ) ≤ (129514260540409791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1081517 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_395 : rowCell 2 395 ≤ (4014891560747061 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (145776612636927491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (129514260540409791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_395_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_395_1
  · norm_num [gridPoint]

theorem exp_2_396_0 : expNegUpper (91652038181304230252541 / 928088656729344128000 : ℝ) ≤ (129514255051196111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1081517 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_396_1 : expNegUpper (73409524982832395888567 / 742470925383475302400 : ℝ) ≤ (115054964916618721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (433007 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_396 : rowCell 2 396 ≤ (17834207250211623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (129514255051196111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (115054964916618721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_396_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_396_1
  · norm_num [gridPoint]

theorem exp_2_397_0 : expNegUpper (3507964251163921581587 / 35479884432902246400 : ℝ) ≤ (23010992014864931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (433007 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_397_1 : expNegUpper (8780419508382957463933 / 88699711082255616000 : ℝ) ≤ (102200122227912157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (6772 / 3125 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_397 : rowCell 2 397 ≤ (3168487158318423 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23010992014864931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (102200122227912157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_397_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_397_1
  · norm_num [gridPoint]

theorem exp_2_398_0 : expNegUpper (185035022861384163495217 / 1869221971148925184000 : ℝ) ≤ (20440023591330853 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (6772 / 3125 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_398_1 : expNegUpper (370513322824347712304553 / 3738443942297850368000 : ℝ) ≤ (18154569592498397 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (271131 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_398 : rowCell 2 398 ≤ (14071762048973213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20440023591330853 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18154569592498397 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_398_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_398_1
  · norm_num [gridPoint]

theorem exp_2_399_0 : expNegUpper (594895297230760400817 / 6002436571914752000 : ℝ) ≤ (90772844195243739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (271131 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_399_1 : expNegUpper (37225474532329112263 / 375152285744672000 : ℝ) ≤ (20153906011392361 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108553 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_399 : rowCell 2 399 ≤ (12497801085947033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (90772844195243739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20153906011392361 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_399_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_399_1
  · norm_num [gridPoint]

theorem exp_2_400_0 : expNegUpper (7782391697998357986589 / 78429679393778016000 : ℝ) ≤ (80615620723132909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108553 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_400_1 : expNegUpper (124667298947084363730197 / 1254874870300448256000 : ℝ) ≤ (2863527763846863 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (543269 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_400 : rowCell 2 400 ≤ (69367743263991 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (80615620723132909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2863527763846863 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_400_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_400_1
  · norm_num [gridPoint]

theorem exp_2_401_0 : expNegUpper (375305777919194772256439 / 3777749202661724672000 : ℝ) ≤ (71588191166267817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (543269 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_401_1 : expNegUpper (37575478737057226471539 / 377774920266172467200 : ℝ) ≤ (63565685620604783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1087547 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_401 : rowCell 2 401 ≤ (4927771061304963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (71588191166267817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (63565685620604783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_401_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_401_1
  · norm_num [gridPoint]

theorem exp_2_402_0 : expNegUpper (37706250000738466394019 / 379089663272785971200 : ℝ) ≤ (31782841518534687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1087547 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_402_1 : expNegUpper (377513426903587289933461 / 3790896632727859712000 : ℝ) ≤ (7054616860240857 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2177117 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_402 : rowCell 2 402 ≤ (4375349356752621 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31782841518534687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7054616860240857 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_402_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_402_1
  · norm_num [gridPoint]

theorem exp_2_403_0 : expNegUpper (126274992586943168378863 / 1268022300366583296000 : ℝ) ≤ (56436932603998409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2177117 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_403_1 : expNegUpper (31606485452719734464489 / 317005575091645824000 : ℝ) ≤ (25051496377266333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1089571 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_403 : rowCell 2 403 ≤ (1942246769152069 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (56436932603998409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25051496377266333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_403_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_403_1
  · norm_num [gridPoint]

theorem exp_2_404_0 : expNegUpper (543704601674097060821 / 5453228582539136000 : ℝ) ≤ (501029907462237 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1089571 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_404_1 : expNegUpper (2177417102571768470661 / 21812914330156544000 : ℝ) ≤ (22237896086616471 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (545293 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_404 : rowCell 2 404 ≤ (3448384911806029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (501029907462237 / 10000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22237896086616471 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_404_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_404_1
  · norm_num [gridPoint]

theorem exp_2_405_0 : expNegUpper (382367240232838622983587 / 3830475952760795648000 : ℝ) ≤ (55594738003467 / 1250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (545293 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_405_1 : expNegUpper (191411969724096971518973 / 1915237976380397824000 : ℝ) ≤ (9869239961237827 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (545801 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_405 : rowCell 2 405 ≤ (6121909974363151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (55594738003467 / 1250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9869239961237827 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_405_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_405_1
  · norm_num [gridPoint]

theorem exp_2_406_0 : expNegUpper (64024507489346698848719 / 640619122674991872000 : ℝ) ≤ (39476958284297563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (545801 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_406_1 : expNegUpper (25640378327958589487983 / 256247649069996748800 : ℝ) ≤ (3503675673346931 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (54631 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_406 : rowCell 2 406 ≤ (5433607045011397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (39476958284297563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3503675673346931 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_406_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_406_1
  · norm_num [gridPoint]

theorem exp_2_407_0 : expNegUpper (77186529054786259925989 / 771395271528972390400 : ℝ) ≤ (35036755357868191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (54631 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_407_1 : expNegUpper (48299151169494103367517 / 482122044705607744000 : ℝ) ≤ (777328336900607 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27341 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_407 : rowCell 2 407 ≤ (4822250907339439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35036755357868191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (777328336900607 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_407_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_407_1
  · norm_num [gridPoint]

theorem exp_2_408_0 : expNegUpper (48465506404841323665693 / 483782602193190976000 : ℝ) ≤ (1554656613181479 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27341 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_408_1 : expNegUpper (388186552750254543628183 / 3870260817545527808000 : ℝ) ≤ (689772209130221 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2189323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_408 : rowCell 2 408 ≤ (2139645754089841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1554656613181479 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (689772209130221 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_408_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_408_1
  · norm_num [gridPoint]

theorem exp_2_409_0 : expNegUpper (5193616970970889452109 / 51780908210025984000 : ℝ) ≤ (27590887296741449 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2189323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_409_1 : expNegUpper (2599904767297484260753 / 25890454105012992000 : ℝ) ≤ (24480916848652207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2191369 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_409 : rowCell 2 409 ≤ (3797122741543643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27590887296741449 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24480916848652207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_409_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_409_1
  · norm_num [gridPoint]

theorem exp_2_410_0 : expNegUpper (195662160009264152553451 / 1948449126132062464000 : ℝ) ≤ (1224045795354997 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2191369 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_410_1 : expNegUpper (391790706381395760123501 / 3896898252264124928000 : ℝ) ≤ (21719542678633133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2193419 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_410 : rowCell 2 410 ≤ (3368978948296167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1224045795354997 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21719542678633133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_410_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_410_1
  · norm_num [gridPoint]

theorem exp_2_411_0 : expNegUpper (56161886116886289235827 / 558607318154579456000 : ℝ) ≤ (21719541848985463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2193419 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_411_1 : expNegUpper (562287909432732219127 / 5586073181545794560 : ℝ) ≤ (4816980474663799 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2195473 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_411 : rowCell 2 411 ≤ (1494421340576209 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21719541848985463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4816980474663799 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_411_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_411_1
  · norm_num [gridPoint]

theorem exp_2_412_0 : expNegUpper (1316493104047275047563 / 13078756800685808640 : ℝ) ≤ (9633960583834441 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2195473 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_412_1 : expNegUpper (131806071917170555212737 / 1307875680068580864000 : ℝ) ≤ (854575589858681 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2197529 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_412 : rowCell 2 412 ≤ (265136251847437 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9633960583834441 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (854575589858681 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_412_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_412_1
  · norm_num [gridPoint]

theorem exp_2_413_0 : expNegUpper (396768515198802420690299 / 3937025691635184128000 : ℝ) ≤ (5469283569013 / 320000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2197529 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_413_1 : expNegUpper (198620376909765871800249 / 1968512845817592064000 : ℝ) ≤ (15159597801811927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (219959 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_413 : rowCell 2 413 ≤ (470355968120533 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5469283569013 / 320000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15159597801811927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_413_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_413_1
  · norm_num [gridPoint]

theorem exp_2_414_0 : expNegUpper (7971899295288047812881 / 79008943627407616000 : ℝ) ≤ (15159597234476479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (219959 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_414_1 : expNegUpper (15962766431972457360193 / 158017887254815232000 : ℝ) ≤ (13444872041045569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2201653 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_414 : rowCell 2 414 ≤ (2085863598898933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15159597234476479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13444872041045569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_414_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_414_1
  · norm_num [gridPoint]

theorem exp_2_415_0 : expNegUpper (133475763301107023619739 / 1321297169803777536000 : ℝ) ≤ (420152235665393 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2201653 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_415_1 : expNegUpper (4176077569616556078961 / 41290536556368048000 : ℝ) ≤ (5961528986933371 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2203721 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_415 : rowCell 2 415 ≤ (115615763234037 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (420152235665393 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5961528986933371 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_415_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_415_1
  · norm_num [gridPoint]

theorem sum_2_384_2 : blockSum (rowCell 2) 384 2 ≤ (17311575828660231 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_384) (by simpa only [blockSum_one] using cell_2_385) (by norm_num)

theorem sum_2_386_2 : blockSum (rowCell 2) 386 2 ≤ (109524396463637273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_386) (by simpa only [blockSum_one] using cell_2_387) (by norm_num)

theorem sum_2_384_4 : blockSum (rowCell 2) 384 4 ≤ (248017003092919121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_384_2 sum_2_386_2 (by norm_num)

theorem sum_2_388_2 : blockSum (rowCell 2) 388 2 ≤ (86580305810880511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_388) (by simpa only [blockSum_one] using cell_2_389) (by norm_num)

theorem sum_2_390_2 : blockSum (rowCell 2) 390 2 ≤ (34207647206362497 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_390) (by simpa only [blockSum_one] using cell_2_391) (by norm_num)

theorem sum_2_388_4 : blockSum (rowCell 2) 388 4 ≤ (30999120044721101 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_388_2 sum_2_390_2 (by norm_num)

theorem sum_2_384_8 : blockSum (rowCell 2) 384 8 ≤ (201506301658262313 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_384_4 sum_2_388_4 (by norm_num)

theorem sum_2_392_2 : blockSum (rowCell 2) 392 2 ≤ (10807990708347633 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_392) (by simpa only [blockSum_one] using cell_2_393) (by norm_num)

theorem sum_2_394_2 : blockSum (rowCell 2) 394 2 ≤ (21334193914762259 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_394) (by simpa only [blockSum_one] using cell_2_395) (by norm_num)

theorem sum_2_392_4 : blockSum (rowCell 2) 392 4 ≤ (96708341371262683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_392_2 sum_2_394_2 (by norm_num)

theorem sum_2_396_2 : blockSum (rowCell 2) 396 2 ≤ (16838321520901869 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_396) (by simpa only [blockSum_one] using cell_2_397) (by norm_num)

theorem sum_2_398_2 : blockSum (rowCell 2) 398 2 ≤ (13284781567460123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_398) (by simpa only [blockSum_one] using cell_2_399) (by norm_num)

theorem sum_2_396_4 : blockSum (rowCell 2) 396 4 ≤ (3765387886045249 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_396_2 sum_2_398_2 (by norm_num)

theorem sum_2_392_8 : blockSum (rowCell 2) 392 8 ≤ (156954547547986667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_392_4 sum_2_396_4 (by norm_num)

theorem sum_2_384_16 : blockSum (rowCell 2) 384 16 ≤ (559967150864511293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_384_8 sum_2_392_8 (by norm_num)

theorem sum_2_400_2 : blockSum (rowCell 2) 400 2 ≤ (10477190522424243 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_400) (by simpa only [blockSum_one] using cell_2_401) (by norm_num)

theorem sum_2_402_2 : blockSum (rowCell 2) 402 2 ≤ (8259842895056759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_402) (by simpa only [blockSum_one] using cell_2_403) (by norm_num)

theorem sum_2_400_4 : blockSum (rowCell 2) 400 4 ≤ (9368516708740501 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_400_2 sum_2_402_2 (by norm_num)

theorem sum_2_404_2 : blockSum (rowCell 2) 404 2 ≤ (13018679797975209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_404) (by simpa only [blockSum_one] using cell_2_405) (by norm_num)

theorem sum_2_406_2 : blockSum (rowCell 2) 406 2 ≤ (2563964488087709 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_406) (by simpa only [blockSum_one] using cell_2_407) (by norm_num)

theorem sum_2_404_4 : blockSum (rowCell 2) 404 4 ≤ (4654907550065209 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_404_2 sum_2_406_2 (by norm_num)

theorem sum_2_400_8 : blockSum (rowCell 2) 400 8 ≤ (60748604585288049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_400_4 sum_2_404_4 (by norm_num)

theorem sum_2_408_2 : blockSum (rowCell 2) 408 2 ≤ (323056569988933 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_408) (by simpa only [blockSum_one] using cell_2_409) (by norm_num)

theorem sum_2_410_2 : blockSum (rowCell 2) 410 2 ≤ (1271564325889717 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_410) (by simpa only [blockSum_one] using cell_2_411) (by norm_num)

theorem sum_2_408_4 : blockSum (rowCell 2) 408 4 ≤ (1443423587917191 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_408_2 sum_2_410_2 (by norm_num)

theorem sum_2_412_2 : blockSum (rowCell 2) 412 2 ≤ (1000628471815407 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_412) (by simpa only [blockSum_one] using cell_2_413) (by norm_num)

theorem sum_2_414_2 : blockSum (rowCell 2) 414 2 ≤ (157428632425741 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_414) (by simpa only [blockSum_one] using cell_2_415) (by norm_num)

theorem sum_2_412_4 : blockSum (rowCell 2) 412 4 ≤ (111735727121507 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_412_2 sum_2_414_2 (by norm_num)

theorem sum_2_408_8 : blockSum (rowCell 2) 408 8 ≤ (2337309404889247 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_408_4 sum_2_412_4 (by norm_num)

theorem sum_2_400_16 : blockSum (rowCell 2) 400 16 ≤ (84121698634180519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_400_8 sum_2_408_8 (by norm_num)

theorem sum_2_384_32 : blockSum (rowCell 2) 384 32 ≤ (161022212374672953 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_384_16 sum_2_400_16 (by norm_num)

#print axioms sum_2_384_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
