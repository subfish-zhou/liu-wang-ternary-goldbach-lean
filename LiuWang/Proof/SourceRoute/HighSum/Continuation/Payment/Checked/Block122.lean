import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_320_0 : (58912897409966248199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2018100925544510597651 / 21786332233823232000 : ℝ) := by
  apply lower_of_taylor (t := (32219 / 15625 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_320 : (859196281738201117 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 320 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (58912897409966248199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_320_0
  · norm_num [gridPoint]

theorem exp_7_321_0 : (5307677669181966801 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (12982775882903054899561 / 139997402661467136000 : ℝ) := by
  apply lower_of_taylor (t := (2063697 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_321 : (120950195079189039 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 321 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5307677669181966801 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_321_0
  · norm_num [gridPoint]

theorem exp_7_322_0 : (1912432009386094737 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (13049953239881958919821 / 140563420941753344000 : ℝ) := by
  apply lower_of_taylor (t := (1032691 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_322 : (1743203254063343263 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 322 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1912432009386094737 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_322_0
  · norm_num [gridPoint]

theorem exp_7_323_0 : (4306012015686509557 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (32793446235096280555499 / 352826452843318272000 : ℝ) := by
  apply lower_of_taylor (t := (2067071 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_323 : (1569991324332653101 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 323 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (4306012015686509557 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_323_0
  · norm_num [gridPoint]

theorem exp_7_324_0 : (7755015053348368857 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (263701042899792942863 / 2833977664963780608 : ℝ) := by
  apply lower_of_taylor (t := (413753 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_324 : (5655026650865000497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 324 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (7755015053348368857 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_324_0
  · norm_num [gridPoint]

theorem exp_7_325_0 : (17455354974339652613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (66264873461761480095627 / 711341636371692544000 : ℝ) := by
  apply lower_of_taylor (t := (1035231 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_325 : (5091440669097328907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 325 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (17455354974339652613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_325_0
  · norm_num [gridPoint]

theorem exp_7_326_0 : (3928292088548749817 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (13321146635743391186579 / 142838913215775744000 : ℝ) := by
  apply lower_of_taylor (t := (518041 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_326 : (2291636707375185137 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 326 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3928292088548749817 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_326_0
  · norm_num [gridPoint]

theorem exp_7_327_0 : (28285138514449908337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3347392118694966245491 / 35852660268125184000 : ℝ) := by
  apply lower_of_taylor (t := (2073869 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_327 : (128911107056426337 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 327 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (28285138514449908337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_327_0
  · norm_num [gridPoint]

theorem exp_7_328_0 : (2545380740523624311 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (16822800886348312177167 / 179979388555641856000 : ℝ) := by
  apply lower_of_taylor (t := (2075579 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_328 : (3712229009289834979 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 328 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2545380740523624311 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_328_0
  · norm_num [gridPoint]

theorem exp_7_329_0 : (916088645380240579 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (13527163838256677802341 / 144557522531813990400 : ℝ) := by
  apply lower_of_taylor (t := (2077293 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_329 : (3340100353475973841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 329 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (916088645380240579 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_329_0
  · norm_num [gridPoint]

theorem exp_7_330_0 : (2575389988471998919 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (67981691809654407501197 / 725663380672011264000 : ℝ) := by
  apply lower_of_taylor (t := (207901 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_330 : (3004796028581134863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 330 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2575389988471998919 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_330_0
  · norm_num [gridPoint]

theorem exp_7_331_0 : (4632971379322895939 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6832882389859096585941 / 72854485826139136000 : ℝ) := by
  apply lower_of_taylor (t := (520183 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_331 : (1351361741661796729 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 331 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (4632971379322895939 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_331_0
  · norm_num [gridPoint]

theorem exp_7_332_0 : (16666245417577591639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6867721795617772576861 / 73143204542721024000 : ℝ) := by
  apply lower_of_taylor (t := (2082457 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_332 : (1215317589429625337 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 332 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (16666245417577591639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_332_0
  · norm_num [gridPoint]

theorem exp_7_333_0 : (14986074498068140119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (69026876480499348911063 / 734324942169467904000 : ℝ) := by
  apply lower_of_taylor (t := (2084187 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_333 : (2185596032900871271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 333 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (14986074498068140119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_333_0
  · norm_num [gridPoint]

theorem exp_7_334_0 : (3368296876426581049 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (13875560393928099393807 / 147444709697632870400 : ℝ) := by
  apply lower_of_taylor (t := (13037 / 6250 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_334 : (491238468866502409 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 334 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3368296876426581049 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_334_0
  · norm_num [gridPoint]

theorem exp_7_335_0 : (756947203134644887 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8716249615210728953099 / 92515983047912448000 : ℝ) := by
  apply lower_of_taylor (t := (1043829 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_335 : (883156321957297943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 335 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (756947203134644887 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_335_0
  · norm_num [gridPoint]

theorem exp_7_336_0 : (10885137888717223623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (350417319173600072803 / 3715189449274368000 : ℝ) := by
  apply lower_of_taylor (t := (2089399 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_336 : (1587508068922663681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 336 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (10885137888717223623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_336_0
  · norm_num [gridPoint]

theorem exp_7_337_0 : (9781733738509121343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2817528208273108298349 / 29838144996115456000 : ℝ) := by
  apply lower_of_taylor (t := (418229 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_337 : (35664640624424541 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 337 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (9781733738509121343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_337_0
  · norm_num [gridPoint]

theorem exp_7_338_0 : (8788842200930747969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (70794223536093572001433 / 748875069527337984000 : ℝ) := by
  apply lower_of_taylor (t := (1046447 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_338 : (1281780539034570081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 338 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (8788842200930747969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_338_0
  · norm_num [gridPoint]

theorem exp_7_339_0 : (7895539509247800399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7115152132060226987099 / 75180222372822835200 : ℝ) := by
  apply lower_of_taylor (t := (2094647 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_339 : (1151499669326254889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 339 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (7895539509247800399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_339_0
  · norm_num [gridPoint]

theorem exp_7_340_0 : (1418393224987268903 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (35755050529219231374831 / 377367543752778752000 : ℝ) := by
  apply lower_of_taylor (t := (419281 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_340 : (1034305083037347229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 340 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1418393224987268903 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_340_0
  · norm_num [gridPoint]

theorem exp_7_341_0 : (796153089174873309 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (14373993049537362463943 / 151534732171865088000 : ℝ) := by
  apply lower_of_taylor (t := (1049083 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_341 : (37155967076110603 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 341 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (796153089174873309 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_341_0
  · norm_num [gridPoint]

theorem exp_7_342_0 : (5719287725482498889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (14446223277286396052683 / 152123588757906432000 : ℝ) := by
  apply lower_of_taylor (t := (2099931 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_342 : (208527799682374841 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 342 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5719287725482498889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_342_0
  · norm_num [gridPoint]

theorem exp_7_343_0 : (5134913698708305769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (18148389243189657065757 / 190891984074044416000 : ℝ) := by
  apply lower_of_taylor (t := (21017 / 10000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_343 : (748885040617671679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 343 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5134913698708305769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_343_0
  · norm_num [gridPoint]

theorem exp_7_344_0 : (2304785735982063611 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (117673047588308738711 / 1236328448998809600 : ℝ) := by
  apply lower_of_taylor (t := (2103473 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_344 : (672268186294986999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 344 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2304785735982063611 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_344_0
  · norm_num [gridPoint]

theorem exp_7_345_0 : (8080803867664077 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2365236015499839069647 / 24822098388347904000 : ℝ) := by
  apply lower_of_taylor (t := (2105249 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_345 : (603401705602344293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 345 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (8080803867664077 / 1953125000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_345_0
  · norm_num [gridPoint]

theorem exp_7_346_0 : (1856502081229196601 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (14737728079614813884001 / 154490434254949376000 : ℝ) := by
  apply lower_of_taylor (t := (210703 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_346 : (270755599428643241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 346 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1856502081229196601 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_346_0
  · norm_num [gridPoint]

theorem exp_7_347_0 : (416460346988883539 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7405626375557325446593 / 77542500208714752000 : ℝ) := by
  apply lower_of_taylor (t := (421763 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_347 : (485898602656358167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 347 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (416460346988883539 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_347_0
  · norm_num [gridPoint]

theorem exp_7_348_0 : (2989093566256160949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (37212594525538613989549 / 389201771237993472000 : ℝ) := by
  apply lower_of_taylor (t := (2110603 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_348 : (435934776730300379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 348 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2989093566256160949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_348_0
  · norm_num [gridPoint]

theorem exp_7_349_0 : (2681349292065583959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2991816751306826065671 / 31255511697650606080 : ℝ) := by
  apply lower_of_taylor (t := (422479 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_349 : (48881599850544243 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 349 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2681349292065583959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_349_0
  · norm_num [gridPoint]

theorem exp_7_350_0 : (601236937244170271 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (75166955448438187136227 / 784377751982982144000 : ℝ) := by
  apply lower_of_taylor (t := (2114191 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_350 : (350741901101245611 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 350 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (601236937244170271 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_350_0
  · norm_num [gridPoint]

theorem exp_7_351_0 : (2156734180138147009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (944247519330806201809 / 9842167763764224000 : ℝ) := by
  apply lower_of_taylor (t := (264499 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_351 : (62908397642615459 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 351 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2156734180138147009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_351_0
  · norm_num [gridPoint]

theorem sum_7_320_2 : (8166387651225054833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 320 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_320) (by simpa only [blockSum_one] using cell_7_321) (by norm_num)

theorem sum_7_322_2 : (828298644598999091 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 322 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_322) (by simpa only [blockSum_one] using cell_7_323) (by norm_num)

theorem sum_7_320_4 : (14792776808017047561 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 320 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_320_2 sum_7_322_2 (by norm_num)

theorem sum_7_324_2 : (2686616829990582351 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 324 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_324) (by simpa only [blockSum_one] using cell_7_325) (by norm_num)

theorem sum_7_326_2 : (4354214420278006529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 326 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_326) (by simpa only [blockSum_one] using cell_7_327) (by norm_num)

theorem sum_7_324_4 : (9727448080259171231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 324 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_324_2 sum_7_326_2 (by norm_num)

theorem sum_7_320_8 : (3065028111034527349 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 320 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_320_4 sum_7_324_4 (by norm_num)

theorem sum_7_328_2 : (352616468138290441 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 328 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_328) (by simpa only [blockSum_one] using cell_7_329) (by norm_num)

theorem sum_7_330_2 : (5707519511904728321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 330 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_330) (by simpa only [blockSum_one] using cell_7_331) (by norm_num)

theorem sum_7_328_4 : (12759848874670537141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 328 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_328_2 sum_7_330_2 (by norm_num)

theorem sum_7_332_2 : (923246242352024389 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 332 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_332) (by simpa only [blockSum_one] using cell_7_333) (by norm_num)

theorem sum_7_334_2 : (1865633259690302761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 334 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_334) (by simpa only [blockSum_one] using cell_7_335) (by norm_num)

theorem sum_7_332_4 : (8347497731140727467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 332 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_332_2 sum_7_334_2 (by norm_num)

theorem sum_7_328_8 : (659604581431602019 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 328 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_328_4 sum_7_332_4 (by norm_num)

theorem sum_7_320_16 : (4384237273897731387 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 320 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_320_8 sum_7_328_8 (by norm_num)

theorem sum_7_336_2 : (3014093693899645321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 336 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_336) (by simpa only [blockSum_one] using cell_7_337) (by norm_num)

theorem sum_7_338_2 : (243328020836082497 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 338 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_338) (by simpa only [blockSum_one] using cell_7_339) (by norm_num)

theorem sum_7_336_4 : (5447373902260470291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 336 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_336_2 sum_7_338_2 (by norm_num)

theorem sum_7_340_2 : (122700266246257019 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 340 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_340) (by simpa only [blockSum_one] using cell_7_341) (by norm_num)

theorem sum_7_342_2 : (1582996239347171043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 342 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_342) (by simpa only [blockSum_one] using cell_7_343) (by norm_num)

theorem sum_7_340_4 : (3546200499287283347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 340 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_340_2 sum_7_342_2 (by norm_num)

theorem sum_7_336_8 : (4496787200773876819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 336 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_336_4 sum_7_340_4 (by norm_num)

theorem sum_7_344_2 : (318917472974332823 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 344 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_344) (by simpa only [blockSum_one] using cell_7_345) (by norm_num)

theorem sum_7_346_2 : (1027409801513644649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 346 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_346) (by simpa only [blockSum_one] using cell_7_347) (by norm_num)

theorem sum_7_344_4 : (2303079693410975941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 344 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_344_2 sum_7_346_2 (by norm_num)

theorem sum_7_348_2 : (826987575534654323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 348 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_348) (by simpa only [blockSum_one] using cell_7_349) (by norm_num)

theorem sum_7_350_2 : (332641944657161453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 350 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_350) (by simpa only [blockSum_one] using cell_7_351) (by norm_num)

theorem sum_7_348_4 : (1492271464848977229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 348 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_348_2 sum_7_350_2 (by norm_num)

theorem sum_7_344_8 : (379535115825995317 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 344 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_344_4 sum_7_348_4 (by norm_num)

theorem sum_7_336_16 : (1598615694975963351 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 336 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_336_8 sum_7_344_8 (by norm_num)

theorem sum_7_320_32 : (82936721942171409 / 1000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 320 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_320_16 sum_7_336_16 (by norm_num)

#print axioms sum_7_320_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
