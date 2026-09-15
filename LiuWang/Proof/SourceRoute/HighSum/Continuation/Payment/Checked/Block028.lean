import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_384_0 : expNegUpper (106951349189025457689 / 1111792860099364000 : ℝ) ≤ (834632357724465337 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2120263 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_384_1 : expNegUpper (13706740865512911926503 / 142309486092718592000 : ℝ) ≤ (1481639074697673439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2122239 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_384 : rowCell 1 384 ≤ (57441683816903583 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (834632357724465337 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1481639074697673439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_384_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_384_1
  · norm_num [gridPoint]

theorem exp_1_385_0 : expNegUpper (114632480092410012040109 / 1190165443728754176000 : ℝ) ≤ (46301219114275839 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2122239 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_385_1 : expNegUpper (57387250888624028624621 / 595082721864377088000 : ℝ) ≤ (1314977495563475353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2124219 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_385 : rowCell 1 385 ≤ (203931788291647643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (46301219114275839 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1314977495563475353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_385_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_385_1
  · norm_num [gridPoint]

theorem exp_1_386_0 : expNegUpper (172778074472538281377207 / 1791639174180157696000 : ℝ) ≤ (1314977440012556373 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2124219 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_386_1 : expNegUpper (2767872625215544394889 / 28666226786882523136 : ℝ) ≤ (46678096406689939 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1063101 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_386 : rowCell 1 386 ≤ (180984554533961141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1314977440012556373 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (46678096406689939 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_386_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_386_1
  · norm_num [gridPoint]

theorem exp_1_387_0 : expNegUpper (2777763627206077529889 / 28768665630720987136 : ℝ) ≤ (583476180610188833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1063101 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_387_1 : expNegUpper (86912562522689519432959 / 899020800960030848000 : ℝ) ≤ (517746440033384391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (532047 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_387 : rowCell 1 387 ≤ (40151071438513797 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (583476180610188833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (517746440033384391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_387_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_387_1
  · norm_num [gridPoint]

theorem exp_1_388_0 : expNegUpper (29074196969718172357877 / 300742574802140544000 : ℝ) ≤ (103549283694234651 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (532047 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_388_1 : expNegUpper (116440677046842634529641 / 1202970299208562176000 : ℝ) ≤ (918756561080250989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2130177 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_388 : rowCell 1 388 ≤ (71252810937375673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (103549283694234651 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (918756561080250989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_388_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_388_1
  · norm_num [gridPoint]

theorem exp_1_389_0 : expNegUpper (14022635585799613626347 / 144870457188680192000 : ℝ) ≤ (918756523088744183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2130177 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_389_1 : expNegUpper (7019988625871823473229 / 72435228594340096000 : ℝ) ≤ (815104650343376549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2132171 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_389 : rowCell 1 389 ≤ (505738858130273 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (918756523088744183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (815104650343376549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_389_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_389_1
  · norm_num [gridPoint]

theorem exp_1_390_0 : expNegUpper (176123520709107577528821 / 1817317400057039104000 : ℝ) ≤ (815104616876528231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2132171 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_390_1 : expNegUpper (352682460542286534678481 / 3634634800114078208000 : ℝ) ≤ (14461591161888879 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2134167 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_390 : rowCell 1 390 ≤ (14020721500153499 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (815104616876528231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14461591161888879 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_390_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_390_1
  · norm_num [gridPoint]

theorem exp_1_391_0 : expNegUpper (3805740096221840410973 / 39220763535665664000 : ℝ) ≤ (723079528615740707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2134167 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_391_1 : expNegUpper (95261056150256084239 / 980519088391641600 : ℝ) ≤ (25655400411353397 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2136167 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_391 : rowCell 1 391 ≤ (99497980062666223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (723079528615740707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25655400411353397 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_391_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_391_1
  · norm_num [gridPoint]

theorem exp_1_392_0 : expNegUpper (8890656555714424921907 / 91511251395637260800 : ℝ) ≤ (320692492160043261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2136167 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_392_1 : expNegUpper (356065446295928116462311 / 3660450055825490432000 : ℝ) ≤ (568868319524737583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (213817 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_392 : rowCell 1 392 ≤ (88252758253317247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (320692492160043261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (568868319524737583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_392_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_392_1
  · norm_num [gridPoint]

theorem exp_1_393_0 : expNegUpper (357324351250391317754079 / 3673391941139829248000 : ℝ) ≤ (568868296658639691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (213817 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_393_1 : expNegUpper (178882711392775815343619 / 1836695970569914624000 : ℝ) ≤ (252252294998009313 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2140177 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_393 : rowCell 1 393 ≤ (78271315253310539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (568868296658639691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (252252294998009313 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_393_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_393_1
  · norm_num [gridPoint]

theorem exp_1_394_0 : expNegUpper (2393520706709418450553 / 24575711098399488000 : ℝ) ≤ (504504569859584513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2140177 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_394_1 : expNegUpper (4792947577868824303639 / 49151422196798976000 : ℝ) ≤ (44738264702383033 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2142187 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_394 : rowCell 1 394 ≤ (6941247106631003 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (504504569859584513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44738264702383033 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_394_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_394_1
  · norm_num [gridPoint]

theorem exp_1_395_0 : expNegUpper (27749041268383076391689 / 284564940514290176000 : ℝ) ≤ (111845657323147639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2142187 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_395_1 : expNegUpper (6945815249078794989393 / 71141235128572544000 : ℝ) ≤ (19834625225920909 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (10721 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_395 : rowCell 1 395 ≤ (61550717106251791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (111845657323147639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19834625225920909 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_395_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_395_1
  · norm_num [gridPoint]

theorem exp_1_396_0 : expNegUpper (90613163172607910252541 / 928088656729344128000 : ℝ) ≤ (15867699556251959 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (10721 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_396_1 : expNegUpper (72579881322739365488567 / 742470925383475302400 : ℝ) ≤ (351714203506701537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2146217 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_396 : rowCell 1 396 ≤ (54574488407393713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15867699556251959 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (351714203506701537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_396_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_396_1
  · norm_num [gridPoint]

theorem exp_1_397_0 : expNegUpper (24278230973540423871109 / 248359191030315724800 : ℝ) ≤ (351714189761502907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2146217 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_397_1 : expNegUpper (60770353219549822247531 / 620897977575789312000 : ℝ) ≤ (311807872930486893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1074119 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_397 : rowCell 1 397 ≤ (48384624944603097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (351714189761502907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (311807872930486893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_397_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_397_1
  · norm_num [gridPoint]

theorem exp_1_398_0 : expNegUpper (182949991109671395495217 / 1869221971148925184000 : ℝ) ≤ (155903930414945287 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1074119 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_398_1 : expNegUpper (366350541055242304304553 / 3738443942297850368000 : ℝ) ≤ (276404879899492191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2150261 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_398 : rowCell 1 398 ≤ (42893001526370841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (155903930414945287 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (276404879899492191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_398_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_398_1
  · norm_num [gridPoint]

theorem exp_1_399_0 : expNegUpper (588211544850367338417 / 6002436571914752000 : ℝ) ≤ (69101217311884431 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2150261 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_399_1 : expNegUpper (36808468181986558663 / 375152285744672000 : ℝ) ≤ (244999950899142391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (67259 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_399 : rowCell 1 399 ≤ (7604261586947803 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (69101217311884431 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (244999950899142391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_399_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_399_1
  · norm_num [gridPoint]

theorem exp_1_400_0 : expNegUpper (7695211969413653986589 / 78429679393778016000 : ℝ) ≤ (244999941523116709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (67259 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_400_1 : expNegUpper (123274850534502475730197 / 1254874870300448256000 : ℝ) ≤ (27143019779470011 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2154319 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_400 : rowCell 1 400 ≤ (8424990740501731 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (244999941523116709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27143019779470011 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_400_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_400_1
  · norm_num [gridPoint]

theorem exp_1_401_0 : expNegUpper (371113869212808852256439 / 3777749202661724672000 : ℝ) ≤ (10857207499172617 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2154319 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_401_1 : expNegUpper (37157016039850647271539 / 377774920266172467200 : ℝ) ≤ (96219338708947201 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (33693 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_401 : rowCell 1 401 ≤ (14933573879338849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10857207499172617 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (96219338708947201 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_401_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_401_1
  · norm_num [gridPoint]

theorem exp_1_402_0 : expNegUpper (37286330956667861594019 / 379089663272785971200 : ℝ) ≤ (96219335077586681 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (33693 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_402_1 : expNegUpper (373321518197201369933461 / 3790896632727859712000 : ℝ) ≤ (170529231366779447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (215839 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_402 : rowCell 1 402 ≤ (26467945482954823 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (96219335077586681 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (170529231366779447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_402_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_402_1
  · norm_num [gridPoint]

theorem exp_1_403_0 : expNegUpper (124872835195267776378863 / 1268022300366583296000 : ℝ) ≤ (42632306243863947 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (215839 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_403_1 : expNegUpper (31256552915994230464489 / 317005575091645824000 : ℝ) ≤ (37775286612702413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (216043 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_403 : rowCell 1 403 ≤ (4690715129838021 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42632306243863947 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37775286612702413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_403_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_403_1
  · norm_num [gridPoint]

theorem exp_1_404_0 : expNegUpper (3763794672625216385747 / 38172600077773952000 : ℝ) ≤ (15110114082674977 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (216043 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_404_1 : expNegUpper (15073660831001332254627 / 152690400311095808000 : ℝ) ≤ (133874953464397369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1081237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_404 : rowCell 1 404 ≤ (4156142565784033 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15110114082674977 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (133874953464397369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_404_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_404_1
  · norm_num [gridPoint]

theorem exp_1_405_0 : expNegUpper (378146204589172190983587 / 3830475952760795648000 : ℝ) ≤ (66937474257929651 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1081237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_405_1 : expNegUpper (189305092769423819518973 / 1915237976380397824000 : ℝ) ≤ (11860247392439621 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1082261 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_405 : rowCell 1 405 ≤ (2301360059940957 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (66937474257929651 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11860247392439621 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_405_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_405_1
  · norm_num [gridPoint]

theorem exp_1_406_0 : expNegUpper (63319787926348938848719 / 640619122674991872000 : ℝ) ≤ (118602469570561631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1082261 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_406_1 : expNegUpper (25358975951714160687983 / 256247649069996748800 : ℝ) ≤ (105063338530277083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (541643 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_406 : rowCell 1 406 ≤ (130479293411701 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (118602469570561631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (105063338530277083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_406_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_406_1
  · norm_num [gridPoint]

theorem exp_1_407_0 : expNegUpper (76339409232324922325989 / 771395271528972390400 : ℝ) ≤ (10506333469995639 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (541643 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_407_1 : expNegUpper (47770611497245783367517 / 482122044705607744000 : ℝ) ≤ (9306189041050093 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2168627 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_407 : rowCell 1 407 ≤ (14447469418186483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10506333469995639 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9306189041050093 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_407_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_407_1
  · norm_num [gridPoint]

theorem exp_1_408_0 : expNegUpper (3687318946077920897361 / 37214046322553152000 : ℝ) ≤ (23265471760247779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2168627 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_408_1 : expNegUpper (29534688741380604279091 / 297712370580425216000 : ℝ) ≤ (82424430931351313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (542671 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_408 : rowCell 1 408 ≤ (6398309985016007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23265471760247779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (82424430931351313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_408_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_408_1
  · norm_num [gridPoint]

theorem exp_1_409_0 : expNegUpper (5136948136558263532109 / 51780908210025984000 : ℝ) ≤ (20606106991857171 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (542671 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_409_1 : expNegUpper (2571618894986638820753 / 25890454105012992000 : ℝ) ≤ (364983852211671 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (434549 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_409 : rowCell 1 409 ≤ (1416681678034107 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20606106991857171 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (364983852211671 / 5000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_409_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_409_1
  · norm_num [gridPoint]

theorem exp_1_410_0 : expNegUpper (193533437851630616553451 / 1948449126132062464000 : ℝ) ≤ (18249191958841523 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (434549 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_410_1 : expNegUpper (387540543800448816123501 / 3896898252264124928000 : ℝ) ≤ (32321025216778757 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2174809 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_410 : rowCell 1 410 ≤ (5018373144022849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18249191958841523 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32321025216778757 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_410_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_410_1
  · norm_num [gridPoint]

theorem exp_1_411_0 : expNegUpper (388868476768616824650789 / 3910251227082056192000 : ℝ) ≤ (32321024070359517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2174809 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_411_1 : expNegUpper (3893440922876454813889 / 39102512270820561920 : ℝ) ≤ (57238807238413989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2176877 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_411 : rowCell 1 411 ≤ (1777532295315477 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32321024070359517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (57238807238413989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_411_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_411_1
  · norm_num [gridPoint]

theorem exp_1_412_0 : expNegUpper (1302253078100917287563 / 13078756800685808640 : ℝ) ≤ (14309701305499351 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2176877 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_412_1 : expNegUpper (130384496567308155212737 / 1307875680068580864000 : ℝ) ≤ (12669812669229739 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (544737 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_412 : rowCell 1 412 ≤ (491842599611083 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14309701305499351 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12669812669229739 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_412_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_412_1
  · norm_num [gridPoint]

theorem exp_1_413_0 : expNegUpper (392489225680574964690299 / 3937025691635184128000 : ℝ) ≤ (25339624451862417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (544737 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_413_1 : expNegUpper (196484373017812207800249 / 1968512845817592064000 : ℝ) ≤ (44867733943669543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1090511 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_413 : rowCell 1 413 ≤ (17418429580561 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25339624451862417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44867733943669543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_413_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_413_1
  · norm_num [gridPoint]

theorem exp_1_414_0 : expNegUpper (7886167870237096132881 / 79008943627407616000 : ℝ) ≤ (44867732384470021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1090511 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_414_1 : expNegUpper (15791594851243359120193 / 158017887254815232000 : ℝ) ≤ (7943878727510013 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (21831 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_414 : rowCell 1 414 ≤ (6168169225771741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (44867732384470021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7943878727510013 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_414_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_414_1
  · norm_num [gridPoint]

theorem exp_1_415_0 : expNegUpper (132044478972151119619739 / 1321297169803777536000 : ℝ) ≤ (992984806665393 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (21831 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_415_1 : expNegUpper (4131425785735852078961 / 41290536556368048000 : ℝ) ≤ (17579470570964409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2185181 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_415 : rowCell 1 415 ≤ (273009767282687 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (992984806665393 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17579470570964409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_415_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_415_1
  · norm_num [gridPoint]

theorem sum_1_384_2 : blockSum (rowCell 1) 384 2 ≤ (17347940942370479 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_384) (by simpa only [blockSum_one] using cell_1_385) (by norm_num)

theorem sum_1_386_2 : blockSum (rowCell 1) 386 2 ≤ (341588840288016329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_386) (by simpa only [blockSum_one] using cell_1_387) (by norm_num)

theorem sum_1_384_4 : blockSum (rowCell 1) 384 4 ≤ (24227730120227447 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_384_2 sum_1_386_2 (by norm_num)

theorem sum_1_388_2 : blockSum (rowCell 1) 388 2 ≤ (67235084101829899 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_388) (by simpa only [blockSum_one] using cell_1_389) (by norm_num)

theorem sum_1_390_2 : blockSum (rowCell 1) 390 2 ≤ (42332750412778843 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_390) (by simpa only [blockSum_one] using cell_1_391) (by norm_num)

theorem sum_1_388_4 : blockSum (rowCell 1) 388 4 ≤ (480604088471213811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_388_2 sum_1_390_2 (by norm_num)

theorem sum_1_384_8 : blockSum (rowCell 1) 384 8 ≤ (251178290463698423 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_384_4 sum_1_388_4 (by norm_num)

theorem sum_1_392_2 : blockSum (rowCell 1) 392 2 ≤ (83262036753313893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_392) (by simpa only [blockSum_one] using cell_1_393) (by norm_num)

theorem sum_1_394_2 : blockSum (rowCell 1) 394 2 ≤ (130963188172561821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_394) (by simpa only [blockSum_one] using cell_1_395) (by norm_num)

theorem sum_1_392_4 : blockSum (rowCell 1) 392 4 ≤ (297487261679189607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_392_2 sum_1_394_2 (by norm_num)

theorem sum_1_396_2 : blockSum (rowCell 1) 396 2 ≤ (10295911335199681 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_396) (by simpa only [blockSum_one] using cell_1_397) (by norm_num)

theorem sum_1_398_2 : blockSum (rowCell 1) 398 2 ≤ (2528572170659683 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_398) (by simpa only [blockSum_one] using cell_1_399) (by norm_num)

theorem sum_1_396_4 : blockSum (rowCell 1) 396 4 ≤ (91936711406553333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_396_2 sum_1_398_2 (by norm_num)

theorem sum_1_392_8 : blockSum (rowCell 1) 392 8 ≤ (481360684492296273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_392_4 sum_1_396_4 (by norm_num)

theorem sum_1_384_16 : blockSum (rowCell 1) 384 16 ≤ (434313034202697097 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_384_8 sum_1_392_8 (by norm_num)

theorem sum_1_400_2 : blockSum (rowCell 1) 400 2 ≤ (31783555360342311 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_400) (by simpa only [blockSum_one] using cell_1_401) (by norm_num)

theorem sum_1_402_2 : blockSum (rowCell 1) 402 2 ≤ (1560047535379529 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_402) (by simpa only [blockSum_one] using cell_1_403) (by norm_num)

theorem sum_1_400_4 : blockSum (rowCell 1) 400 4 ≤ (2269772637056591 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_400_2 sum_1_402_2 (by norm_num)

theorem sum_1_404_2 : blockSum (rowCell 1) 404 2 ≤ (39191593308447821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_404) (by simpa only [blockSum_one] using cell_1_405) (by norm_num)

theorem sum_1_406_2 : blockSum (rowCell 1) 406 2 ≤ (7689345273662277 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_406) (by simpa only [blockSum_one] using cell_1_407) (by norm_num)

theorem sum_1_404_4 : blockSum (rowCell 1) 404 4 ≤ (69948974403096929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_404_2 sum_1_406_2 (by norm_num)

theorem sum_1_400_8 : blockSum (rowCell 1) 400 8 ≤ (183437606255926479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_400_4 sum_1_404_4 (by norm_num)

theorem sum_1_408_2 : blockSum (rowCell 1) 408 2 ≤ (2413007339430487 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_408) (by simpa only [blockSum_one] using cell_1_409) (by norm_num)

theorem sum_1_410_2 : blockSum (rowCell 1) 410 2 ≤ (18924407764623083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_410) (by simpa only [blockSum_one] using cell_1_411) (by norm_num)

theorem sum_1_408_4 : blockSum (rowCell 1) 408 4 ≤ (43054481158927953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_408_2 sum_1_410_2 (by norm_num)

theorem sum_1_412_2 : blockSum (rowCell 1) 412 2 ≤ (231825834781277 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_412) (by simpa only [blockSum_one] using cell_1_413) (by norm_num)

theorem sum_1_414_2 : blockSum (rowCell 1) 414 2 ≤ (11628364571425481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_414) (by simpa only [blockSum_one] using cell_1_415) (by norm_num)

theorem sum_1_412_4 : blockSum (rowCell 1) 412 4 ≤ (26465217997427209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_412_2 sum_1_414_2 (by norm_num)

theorem sum_1_408_8 : blockSum (rowCell 1) 408 8 ≤ (34759849578177581 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_408_4 sum_1_412_4 (by norm_num)

theorem sum_1_400_16 : blockSum (rowCell 1) 400 16 ≤ (252957305412281641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_400_8 sum_1_408_8 (by norm_num)

theorem sum_1_384_32 : blockSum (rowCell 1) 384 32 ≤ (1990209442223070029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_384_16 sum_1_400_16 (by norm_num)

#print axioms sum_1_384_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
