import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_384_0 : expNegUpper (110341448541478577689 / 1111792860099364000 : ℝ) ≤ (4944774192937429 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2171379 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_384_1 : expNegUpper (14139896864299430966503 / 142309486092718592000 : ℝ) ≤ (70608016978715457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (217331 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_384 : rowCell 5 384 ≤ (10918038062491167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4944774192937429 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (70608016978715457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_384_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_384_1
  · norm_num [gridPoint]

theorem exp_5_385_0 : expNegUpper (7548195237516319747241 / 75968007046516224000 : ℝ) ≤ (8826001669778677 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (217331 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_385_1 : expNegUpper (3778423651697810167529 / 37984003523258112000 : ℝ) ≤ (63007434420862871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (543811 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_385 : rowCell 5 385 ≤ (4871679248590137 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8826001669778677 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (63007434420862871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_385_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_385_1
  · norm_num [gridPoint]

theorem exp_5_386_0 : expNegUpper (178221651394650281377207 / 1791639174180157696000 : ℝ) ≤ (1575185780328291 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (543811 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_386_1 : expNegUpper (2854814512303840330889 / 28666226786882523136 : ℝ) ≤ (28109303476284779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2177183 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_386 : rowCell 5 386 ≤ (2173517455046649 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1575185780328291 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28109303476284779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_386_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_386_1
  · norm_num [gridPoint]

theorem exp_5_387_0 : expNegUpper (2865016201625365593889 / 28768665630720987136 : ℝ) ≤ (28109302055412241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2177183 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_387_1 : expNegUpper (89634350983745519432959 / 899020800960030848000 : ℝ) ≤ (25077782702205103 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (17433 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_387 : rowCell 5 387 ≤ (3878450005796919 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28109302055412241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25077782702205103 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_387_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_387_1
  · norm_num [gridPoint]

theorem exp_5_388_0 : expNegUpper (89954088349304021073631 / 902227724406421632000 : ℝ) ≤ (50155562887147437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (17433 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_388_1 : expNegUpper (360228602942938911588923 / 3608910897625686528000 : ℝ) ≤ (22370681505714507 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (218107 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_388 : rowCell 5 388 ≤ (6919969095481057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (50155562887147437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22370681505714507 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_388_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_388_1
  · norm_num [gridPoint]

theorem exp_5_389_0 : expNegUpper (14460451894551014586347 / 144870457188680192000 : ℝ) ≤ (279633504886381 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (218107 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_389_1 : expNegUpper (7238508421083783793229 / 72435228594340096000 : ℝ) ≤ (1596285509948847 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2183019 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_389 : rowCell 5 389 ≤ (1543161141058133 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (279633504886381 / 6250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1596285509948847 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_389_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_389_1
  · norm_num [gridPoint]

theorem exp_5_390_0 : expNegUpper (181605933547593593528821 / 1817317400057039104000 : ℝ) ≤ (19953567887046627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2183019 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_390_1 : expNegUpper (363627868261071558678481 / 3634634800114078208000 : ℝ) ≤ (3559127108430619 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (546243 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_390 : rowCell 5 390 ≤ (6881764573393 / 1250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19953567887046627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3559127108430619 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_390_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_390_1
  · norm_num [gridPoint]

theorem exp_5_391_0 : expNegUpper (11771550728509361232919 / 117662290606996992000 : ℝ) ≤ (17795634667835853 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (546243 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_391_1 : expNegUpper (294625769803165052717 / 2941557265174924800 : ℝ) ≤ (991832292167193 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2186929 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_391 : rowCell 5 391 ≤ (122743924887531 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17795634667835853 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (991832292167193 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_391_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_391_1
  · norm_num [gridPoint]

theorem exp_5_392_0 : expNegUpper (9165748095548076121907 / 91511251395637260800 : ℝ) ≤ (31738631800996899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2186929 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_392_1 : expNegUpper (367049689931087156462311 / 3660450055825490432000 : ℝ) ≤ (28299906909260271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2188889 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_392 : rowCell 5 392 ≤ (273629011476661 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31738631800996899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28299906909260271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_392_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_392_1
  · norm_num [gridPoint]

theorem exp_5_393_0 : expNegUpper (368347430801924373754079 / 3673391941139829248000 : ℝ) ≤ (28299905538383031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2188889 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_393_1 : expNegUpper (184384542189448839343619 / 1836695970569914624000 : ℝ) ≤ (25230979205326139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2190853 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_393 : rowCell 5 393 ≤ (780704041933107 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28299905538383031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25230979205326139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_393_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_393_1
  · norm_num [gridPoint]

theorem exp_5_394_0 : expNegUpper (7401412070322656631659 / 73727133295198464000 : ℝ) ≤ (3153872248962543 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2190853 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_394_1 : expNegUpper (14819765915667795150917 / 147454266590396928000 : ℝ) ≤ (22492398534900511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (109641 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_394 : rowCell 5 394 ≤ (3480031492790833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3153872248962543 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22492398534900511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_394_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_394_1
  · norm_num [gridPoint]

theorem exp_5_395_0 : expNegUpper (371799451956887065091957 / 3699344226685772288000 : ℝ) ≤ (22492397460592073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (109641 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_395_1 : expNegUpper (93056222615454350862109 / 924836056671443072000 : ℝ) ≤ (20048886157164503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2194791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_395 : rowCell 5 395 ≤ (310214862209131 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22492397460592073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20048886157164503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_395_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_395_1
  · norm_num [gridPoint]

theorem exp_5_396_0 : expNegUpper (93383496529131430252541 / 928088656729344128000 : ℝ) ≤ (20048885206272133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2194791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_396_1 : expNegUpper (74792264416320779888567 / 742470925383475302400 : ℝ) ≤ (17868898959064157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1098383 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_396 : rowCell 5 396 ≤ (1382499444047767 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20048885206272133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17868898959064157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_396_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_396_1
  · norm_num [gridPoint]

theorem exp_5_397_0 : expNegUpper (75054843197477489213327 / 745077573090947174400 : ℝ) ≤ (2233612264686307 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1098383 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_397_1 : expNegUpper (187851726371696506742593 / 1862693932727367936000 : ℝ) ≤ (636969499961491 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (274843 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_397 : rowCell 5 397 ≤ (2464225810177483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2233612264686307 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (636969499961491 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_397_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_397_1
  · norm_num [gridPoint]

theorem exp_5_398_0 : expNegUpper (188510075780905443495217 / 1869221971148925184000 : ℝ) ≤ (15924236754285423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (274843 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_398_1 : expNegUpper (377451292439523392304553 / 3738443942297850368000 : ℝ) ≤ (14189694771004849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1100363 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_398 : rowCell 5 398 ≤ (1097967471154761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15924236754285423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14189694771004849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_398_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_398_1
  · norm_num [gridPoint]

theorem exp_5_399_0 : expNegUpper (606034884531415504817 / 6002436571914752000 : ℝ) ≤ (2837938822399609 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1100363 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_399_1 : expNegUpper (37920485116233368263 / 375152285744672000 : ℝ) ≤ (6321370751749353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (275339 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_399 : rowCell 5 399 ≤ (1956645312348397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2837938822399609 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6321370751749353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_399_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_399_1
  · norm_num [gridPoint]

theorem exp_5_400_0 : expNegUpper (23783073736918593959767 / 235289038181334048000 : ℝ) ≤ (12642740920419843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (275339 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_400_1 : expNegUpper (380964138904162531190591 / 3764624610901344768000 : ℝ) ≤ (11263244233903333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2204701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_400 : rowCell 5 400 ≤ (27238217429481 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12642740920419843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11263244233903333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_400_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_400_1
  · norm_num [gridPoint]

theorem exp_5_401_0 : expNegUpper (382292292429837972256439 / 3777749202661724672000 : ℝ) ≤ (11263243718052643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2204701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_401_1 : expNegUpper (38272916565734858471539 / 377774920266172467200 : ℝ) ≤ (627075798766933 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1103347 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_401 : rowCell 5 401 ≤ (1552956741392891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11263243718052643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (627075798766933 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_401_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_401_1
  · norm_num [gridPoint]

theorem exp_5_402_0 : expNegUpper (38406115074189474394019 / 379089663272785971200 : ℝ) ≤ (10033212323939613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1103347 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_402_1 : expNegUpper (384499941414230489933461 / 3790896632727859712000 : ℝ) ≤ (1787314815447593 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (220869 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_402 : rowCell 5 402 ≤ (1383293867541339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10033212323939613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1787314815447593 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_402_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_402_1
  · norm_num [gridPoint]

theorem exp_5_403_0 : expNegUpper (385835764719206465136589 / 3804066901099749888000 : ℝ) ≤ (1117071709199503 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (220869 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_403_1 : expNegUpper (96569119041786723393467 / 951016725274937472000 : ℝ) ≤ (124358900813001 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (221069 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_403 : rowCell 5 403 ≤ (1232038198894507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1117071709199503 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (124358900813001 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_403_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_403_1
  · norm_num [gridPoint]

theorem exp_5_404_0 : expNegUpper (3876161443541117825747 / 38172600077773952000 : ℝ) ≤ (7958969295028727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (221069 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_404_1 : expNegUpper (15522351196337457694627 / 152690400311095808000 : ℝ) ≤ (1417514858968487 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1106347 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_404 : rowCell 5 404 ≤ (274301869238103 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7958969295028727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1417514858968487 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_404_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_404_1
  · norm_num [gridPoint]

theorem exp_5_405_0 : expNegUpper (389402299638949342983587 / 3830475952760795648000 : ℝ) ≤ (708757397911781 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1106347 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_405_1 : expNegUpper (194923431315218891518973 / 1915237976380397824000 : ℝ) ≤ (6310933728033113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2214701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_405 : rowCell 5 405 ≤ (488515609863607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (708757397911781 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6310933728033113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_405_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_405_1
  · norm_num [gridPoint]

theorem exp_5_406_0 : expNegUpper (195597120283028896546157 / 1921857368024975616000 : ℝ) ≤ (6310933448839779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2214701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_406_1 : expNegUpper (78328146865097912463949 / 768742947209990246400 : ℝ) ≤ (5618819303600083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (277089 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_406 : rowCell 5 406 ≤ (434964144422577 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6310933448839779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5618819303600083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_406_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_406_1
  · norm_num [gridPoint]

theorem exp_5_407_0 : expNegUpper (78598395425555155925989 / 771395271528972390400 : ℝ) ≤ (702352382091691 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (277089 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_407_1 : expNegUpper (49180050623241303367517 / 482122044705607744000 : ℝ) ≤ (500209796043169 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1109363 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_407 : rowCell 5 407 ≤ (774486811121821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (702352382091691 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (500209796043169 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_407_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_407_1
  · norm_num [gridPoint]

theorem exp_5_408_0 : expNegUpper (49349439914555243665693 / 483782602193190976000 : ℝ) ≤ (5002097742168601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1109363 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_408_1 : expNegUpper (395245884604099023628183 / 3870260817545527808000 : ℝ) ≤ (4452615854599669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (277593 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_408 : rowCell 5 408 ≤ (68944620994559 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5002097742168601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4452615854599669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_408_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_408_1
  · norm_num [gridPoint]

theorem exp_5_409_0 : expNegUpper (15864195084975797956327 / 155342724630077952000 : ℝ) ≤ (4452615661643183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (277593 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_409_1 : expNegUpper (7941143663446679982259 / 77671362315038976000 : ℝ) ≤ (3963094239134981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1111383 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_409 : rowCell 5 409 ≤ (153420281738527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4452615661643183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3963094239134981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_409_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_409_1
  · norm_num [gridPoint]

theorem exp_5_410_0 : expNegUpper (199210030271986712553451 / 1948449126132062464000 : ℝ) ≤ (990773517141533 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1111383 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_410_1 : expNegUpper (398874310682974000123501 / 3896898252264124928000 : ℝ) ≤ (1763518158188029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2224791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_410 : rowCell 5 410 ≤ (546187037084003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (990773517141533 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1763518158188029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_410_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_410_1
  · norm_num [gridPoint]

theorem exp_5_411_0 : expNegUpper (400241079567516024650789 / 3910251227082056192000 : ℝ) ≤ (705407233122143 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2224791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_411_1 : expNegUpper (4006972771283576733889 / 39102512270820561920 : ℝ) ≤ (313864391768197 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2226819 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_411 : rowCell 5 411 ≤ (486067380370653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (705407233122143 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (313864391768197 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_411_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_411_1
  · norm_num [gridPoint]

theorem exp_5_412_0 : expNegUpper (4020679441873613942689 / 39236270402057425920 : ℝ) ≤ (196165236527041 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2226819 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_412_1 : expNegUpper (402526092500823665638211 / 3923627040205742592000 : ℝ) ≤ (1396371491789977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (557213 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_412 : rowCell 5 412 ≤ (432522052103779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (196165236527041 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1396371491789977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_412_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_412_1
  · norm_num [gridPoint]

theorem exp_5_413_0 : expNegUpper (403900664395848180690299 / 3937025691635184128000 : ℝ) ≤ (1396371432910991 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (557213 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_413_1 : expNegUpper (202180383396355311800249 / 1968512845817592064000 : ℝ) ≤ (124235846180863 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (278861 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_413 : rowCell 5 413 ≤ (38483710931369 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1396371432910991 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (124235846180863 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_413_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_413_1
  · norm_num [gridPoint]

theorem exp_5_414_0 : expNegUpper (8114785003706300612881 / 79008943627407616000 : ℝ) ≤ (2484716819558721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (278861 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_414_1 : expNegUpper (16248052399854287760193 / 158017887254815232000 : ℝ) ≤ (2210447030529167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2232927 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_414 : rowCell 5 414 ≤ (342375566259681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2484716819558721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2210447030529167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_414_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_414_1
  · norm_num [gridPoint]

theorem exp_5_415_0 : expNegUpper (407583711548100590859217 / 3963891509411332608000 : ℝ) ≤ (2210446938584317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2232927 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_415_1 : expNegUpper (12751491628253188236883 / 123871609669104144000 : ℝ) ≤ (983129604457259 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (223497 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_415 : rowCell 5 415 ≤ (60913832957009 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2210446938584317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (983129604457259 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_415_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_415_1
  · norm_num [gridPoint]

theorem sum_5_384_2 : blockSum (rowCell 5) 384 2 ≤ (20661396559671441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_384) (by simpa only [blockSum_one] using cell_5_385) (by norm_num)

theorem sum_5_386_2 : blockSum (rowCell 5) 386 2 ≤ (8225484915890217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_386) (by simpa only [blockSum_one] using cell_5_387) (by norm_num)

theorem sum_5_384_4 : blockSum (rowCell 5) 384 4 ≤ (59379786226323 / 1600000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_384_2 sum_5_386_2 (by norm_num)

theorem sum_5_388_2 : blockSum (rowCell 5) 388 2 ≤ (13092613659713589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_388) (by simpa only [blockSum_one] using cell_5_389) (by norm_num)

theorem sum_5_390_2 : blockSum (rowCell 5) 390 2 ≤ (260379216355391 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_390) (by simpa only [blockSum_one] using cell_5_391) (by norm_num)

theorem sum_5_388_4 : blockSum (rowCell 5) 388 4 ≤ (23507782313929229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_388_2 sum_5_390_2 (by norm_num)

theorem sum_5_384_8 : blockSum (rowCell 5) 384 8 ≤ (3788759294086319 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_384_4 sum_5_388_4 (by norm_num)

theorem sum_5_392_2 : blockSum (rowCell 5) 392 2 ≤ (8281584393292111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_392) (by simpa only [blockSum_one] using cell_5_393) (by norm_num)

theorem sum_5_394_2 : blockSum (rowCell 5) 394 2 ≤ (6582180114882143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_394) (by simpa only [blockSum_one] using cell_5_395) (by norm_num)

theorem sum_5_392_4 : blockSum (rowCell 5) 392 4 ≤ (7431882254087127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_392_2 sum_5_394_2 (by norm_num)

theorem sum_5_396_2 : blockSum (rowCell 5) 396 2 ≤ (5229224698273017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_396) (by simpa only [blockSum_one] using cell_5_397) (by norm_num)

theorem sum_5_398_2 : blockSum (rowCell 5) 398 2 ≤ (4152580254657919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_398) (by simpa only [blockSum_one] using cell_5_399) (by norm_num)

theorem sum_5_396_4 : blockSum (rowCell 5) 396 4 ≤ (1172725619116367 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_396_2 sum_5_398_2 (by norm_num)

theorem sum_5_392_8 : blockSum (rowCell 5) 392 8 ≤ (2424556946110519 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_392_4 sum_5_396_4 (by norm_num)

theorem sum_5_384_16 : blockSum (rowCell 5) 384 16 ≤ (42432859083243147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_384_8 sum_5_392_8 (by norm_num)

theorem sum_5_400_2 : blockSum (rowCell 5) 400 2 ≤ (131848106275187 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_400) (by simpa only [blockSum_one] using cell_5_401) (by norm_num)

theorem sum_5_402_2 : blockSum (rowCell 5) 402 2 ≤ (1307666033217923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_402) (by simpa only [blockSum_one] using cell_5_403) (by norm_num)

theorem sum_5_400_4 : blockSum (rowCell 5) 400 4 ≤ (5911534723315521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_400_2 sum_5_402_2 (by norm_num)

theorem sum_5_404_2 : blockSum (rowCell 5) 404 2 ≤ (1037119348339813 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_404) (by simpa only [blockSum_one] using cell_5_405) (by norm_num)

theorem sum_5_406_2 : blockSum (rowCell 5) 406 2 ≤ (65776603998679 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_406) (by simpa only [blockSum_one] using cell_5_407) (by norm_num)

theorem sum_5_404_4 : blockSum (rowCell 5) 404 4 ≤ (3718653796646601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_404_2 sum_5_406_2 (by norm_num)

theorem sum_5_400_8 : blockSum (rowCell 5) 400 8 ≤ (4815094259981061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_400_4 sum_5_404_4 (by norm_num)

theorem sum_5_408_2 : blockSum (rowCell 5) 408 2 ≤ (651563668449849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_408) (by simpa only [blockSum_one] using cell_5_409) (by norm_num)

theorem sum_5_410_2 : blockSum (rowCell 5) 410 2 ≤ (16128975272729 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_410) (by simpa only [blockSum_one] using cell_5_411) (by norm_num)

theorem sum_5_408_4 : blockSum (rowCell 5) 408 4 ≤ (1167690877177177 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_408_2 sum_5_410_2 (by norm_num)

theorem sum_5_412_2 : blockSum (rowCell 5) 412 2 ≤ (817359161417469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_412) (by simpa only [blockSum_one] using cell_5_413) (by norm_num)

theorem sum_5_414_2 : blockSum (rowCell 5) 414 2 ≤ (323472365522363 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_414) (by simpa only [blockSum_one] using cell_5_415) (by norm_num)

theorem sum_5_412_4 : blockSum (rowCell 5) 412 4 ≤ (292860778492439 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_412_2 sum_5_414_2 (by norm_num)

theorem sum_5_408_8 : blockSum (rowCell 5) 408 8 ≤ (3799685646816549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_408_4 sum_5_412_4 (by norm_num)

theorem sum_5_400_16 : blockSum (rowCell 5) 400 16 ≤ (13429874166778671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_400_8 sum_5_408_8 (by norm_num)

theorem sum_5_384_32 : blockSum (rowCell 5) 384 32 ≤ (19659118466652993 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_384_16 sum_5_400_16 (by norm_num)

#print axioms sum_5_384_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
