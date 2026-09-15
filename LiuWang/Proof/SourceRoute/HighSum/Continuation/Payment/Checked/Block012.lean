import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_384_0 : expNegUpper (105680061931855537689 / 1111792860099364000 : ℝ) ≤ (654684809225880381 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2101407 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_384_1 : expNegUpper (13544307365967967286503 / 142309486092718592000 : ℝ) ≤ (579909988423852601 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2103399 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_384 : rowCell 0 384 ≤ (36011104740352817 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (654684809225880381 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (579909988423852601 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_384_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_384_1
  · norm_num [gridPoint]

theorem exp_0_385_0 : expNegUpper (37758004368885129346703 / 396721814576251392000 : ℝ) ≤ (4639279725182550931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2103399 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_385_1 : expNegUpper (18903077006044468208207 / 198360907288125696000 : ℝ) ≤ (4109043766057056177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1052697 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_385 : rowCell 0 385 ≤ (637935608803078811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4639279725182550931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4109043766057056177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_385_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_385_1
  · norm_num [gridPoint]

theorem exp_0_386_0 : expNegUpper (170736733126746281377207 / 1791639174180157696000 : ℝ) ≤ (410904360582419453 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1052697 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_386_1 : expNegUpper (2735269417557433418889 / 28666226786882523136 : ℝ) ≤ (181954604055769861 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2107393 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_386 : rowCell 0 386 ≤ (282500507753645633 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (410904360582419453 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (181954604055769861 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_386_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_386_1
  · norm_num [gridPoint]

theorem exp_0_387_0 : expNegUpper (2745043911798844505889 / 28768665630720987136 : ℝ) ≤ (3639091940218079209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2107393 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_387_1 : expNegUpper (85891891849793519432959 / 899020800960030848000 : ℝ) ≤ (805652243267717861 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421879 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_387 : rowCell 0 387 ≤ (100072279081288913 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3639091940218079209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (805652243267717861 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_387_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_387_1
  · norm_num [gridPoint]

theorem exp_0_388_0 : expNegUpper (9577586596566494785959 / 100247524934046848000 : ℝ) ≤ (3222608849185028743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421879 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_388_1 : expNegUpper (38359118523847086176547 / 400990099736187392000 : ℝ) ≤ (57070892637765839 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (10557 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_388 : rowCell 0 388 ≤ (443078570884009697 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3222608849185028743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (57070892637765839 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_388_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_388_1
  · norm_num [gridPoint]

theorem exp_0_389_0 : expNegUpper (13858454470017838266347 / 144870457188680192000 : ℝ) ≤ (1426772261484020997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (10557 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_389_1 : expNegUpper (6938043702667338353229 / 72435228594340096000 : ℝ) ≤ (126326487789034009 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2113409 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_389 : rowCell 0 389 ≤ (78463970013368327 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1426772261484020997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (126326487789034009 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_389_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_389_1
  · norm_num [gridPoint]

theorem exp_0_390_0 : expNegUpper (174067615894675321528821 / 1817317400057039104000 : ℝ) ≤ (2526529660025174011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2113409 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_390_1 : expNegUpper (348577932647742150678481 / 3634634800114078208000 : ℝ) ≤ (447359896418407783 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2115421 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_390 : rowCell 0 390 ≤ (43418280074589161 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2526529660025174011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (447359896418407783 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_390_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_390_1
  · norm_num [gridPoint]

theorem exp_0_391_0 : expNegUpper (1253816263747120136991 / 13073587845221888000 : ℝ) ≤ (447359879583248303 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2115421 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_391_1 : expNegUpper (31385243660402161413 / 326839696130547200 : ℝ) ≤ (1980125764796322239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (529359 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_391 : rowCell 0 391 ≤ (9609436609646907 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (447359879583248303 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1980125764796322239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_391_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_391_1
  · norm_num [gridPoint]

theorem exp_0_392_0 : expNegUpper (8787497228276805721907 / 91511251395637260800 : ℝ) ≤ (990062845402630591 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (529359 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_392_1 : expNegUpper (351946354932743476462311 / 3660450055825490432000 : ℝ) ≤ (438189316849032449 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (423891 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_392 : rowCell 0 392 ≤ (27220517907407819 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (990062845402630591 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (438189316849032449 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_392_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_392_1
  · norm_num [gridPoint]

theorem exp_0_393_0 : expNegUpper (353190696418566421754079 / 3673391941139829248000 : ℝ) ≤ (87637860118110127 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (423891 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_393_1 : expNegUpper (176819524844023431343619 / 1836695970569914624000 : ℝ) ≤ (1551365941882583639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2121477 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_393 : rowCell 0 393 ≤ (15058726764154201 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (87637860118110127 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1551365941882583639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_393_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_393_1
  · norm_num [gridPoint]

theorem exp_0_394_0 : expNegUpper (788638154311706096851 / 8191903699466496000 : ℝ) ≤ (1551365884725561927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2121477 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_394_1 : expNegUpper (1579277393370386341213 / 16383807398932992000 : ℝ) ≤ (686499777621033131 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1061751 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_394 : rowCell 0 394 ≤ (213247355242014419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1551365884725561927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (686499777621033131 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_394_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_394_1
  · norm_num [gridPoint]

theorem exp_0_395_0 : expNegUpper (356589318188514841091957 / 3699344226685772288000 : ℝ) ≤ (343249876252869657 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1061751 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_395_1 : expNegUpper (89260364096488078862109 / 924836056671443072000 : ℝ) ≤ (60751975297730143 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2125531 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_395 : rowCell 0 395 ≤ (188722129870945577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (343249876252869657 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (60751975297730143 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_395_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_395_1
  · norm_num [gridPoint]

theorem exp_0_396_0 : expNegUpper (89574288163911590252541 / 928088656729344128000 : ℝ) ≤ (1215039461814213747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2125531 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_396_1 : expNegUpper (71750237662646335088567 / 742470925383475302400 : ℝ) ≤ (134395418135586281 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2127563 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_396 : rowCell 0 396 ≤ (167003646283152403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1215039461814213747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (134395418135586281 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_396_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_396_1
  · norm_num [gridPoint]

theorem exp_0_397_0 : expNegUpper (8000237396311132223703 / 82786397010105241600 : ℝ) ≤ (1075163306298827409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2127563 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_397_1 : expNegUpper (20025923293472980749177 / 206965992525263104000 : ℝ) ≤ (190262296173421809 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1064799 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_397 : rowCell 0 397 ≤ (147772362141081681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1075163306298827409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (190262296173421809 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_397_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_397_1
  · norm_num [gridPoint]

theorem exp_0_398_0 : expNegUpper (180864959357958627495217 / 1869221971148925184000 : ℝ) ≤ (475655723394310087 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1064799 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_398_1 : expNegUpper (362187759286136896304553 / 3738443942297850368000 : ℝ) ≤ (841657602985218763 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2131637 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_398 : rowCell 0 398 ≤ (8171557123758687 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (475655723394310087 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (841657602985218763 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_398_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_398_1
  · norm_num [gridPoint]

theorem exp_0_399_0 : expNegUpper (581527792469974276017 / 6002436571914752000 : ℝ) ≤ (841657573044864107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2131637 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_399_1 : expNegUpper (36391461831644005063 / 375152285744672000 : ℝ) ≤ (744582413784354953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1066839 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_399 : rowCell 0 399 ≤ (115670044977074821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (841657573044864107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (744582413784354953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_399_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_399_1
  · norm_num [gridPoint]

theorem exp_0_400_0 : expNegUpper (2536010746942983328863 / 26143226464592672000 : ℝ) ≤ (148916477496293099 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1066839 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_400_1 : expNegUpper (40627467373973529243399 / 418291623433482752000 : ℝ) ≤ (164662574783536861 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (533931 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_400 : rowCell 0 400 ≤ (102324988224877377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (148916477496293099 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (164662574783536861 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_400_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_400_1
  · norm_num [gridPoint]

theorem exp_0_401_0 : expNegUpper (366921960506422932256439 / 3777749202661724672000 : ℝ) ≤ (658650276028398347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (533931 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_401_1 : expNegUpper (36738553342644068071539 / 377774920266172467200 : ℝ) ≤ (582588612154358787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (534443 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_401 : rowCell 0 401 ≤ (22628063725462563 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (658650276028398347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (582588612154358787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_401_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_401_1
  · norm_num [gridPoint]

theorem exp_0_402_0 : expNegUpper (36866411912597256794019 / 379089663272785971200 : ℝ) ≤ (582588591858525567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (534443 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_402_1 : expNegUpper (369129609490815449933461 / 3790896632727859712000 : ℝ) ≤ (20610771163518401 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (133739 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_402 : rowCell 0 402 ≤ (40028391153049329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (582588591858525567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20610771163518401 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_402_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_402_1
  · norm_num [gridPoint]

theorem exp_0_403_0 : expNegUpper (41156892601197461459621 / 422674100122194432000 : ℝ) ≤ (515269261261540587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (133739 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_403_1 : expNegUpper (10302206793089575488163 / 105668525030548608000 : ℝ) ≤ (455692468723508027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2141879 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_403 : rowCell 0 403 ≤ (70803401698939029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (515269261261540587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (455692468723508027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_403_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_403_1
  · norm_num [gridPoint]

theorem exp_0_404_0 : expNegUpper (3721657133531753345747 / 38172600077773952000 : ℝ) ≤ (227846226533553769 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2141879 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_404_1 : expNegUpper (14905401944000285214627 / 152690400311095808000 : ℝ) ≤ (2014860476828217 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2143937 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_404 : rowCell 0 404 ≤ (62614590328146431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (227846226533553769 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2014860476828217 / 5000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_404_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_404_1
  · norm_num [gridPoint]

theorem exp_0_405_0 : expNegUpper (373925168945505758983587 / 3830475952760795648000 : ℝ) ≤ (402972081616031163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2143937 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_405_1 : expNegUpper (187198215814750667518973 / 1915237976380397824000 : ℝ) ≤ (89080737702665621 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2145999 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_405 : rowCell 0 405 ≤ (55368475943685197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (402972081616031163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (89080737702665621 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_405_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_405_1
  · norm_num [gridPoint]

theorem exp_0_406_0 : expNegUpper (20871689454450392949573 / 213539707558330624000 : ℝ) ≤ (17816146936821037 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2145999 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_406_1 : expNegUpper (8359191191823243962661 / 85415883023332249600 : ℝ) ≤ (315049283445323097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (67127 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_406 : rowCell 0 406 ≤ (12239266406868407 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17816146936821037 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (315049283445323097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_406_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_406_1
  · norm_num [gridPoint]

theorem exp_0_407_0 : expNegUpper (75492289409863584725989 / 771395271528972390400 : ℝ) ≤ (315049272843017199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (67127 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_407_1 : expNegUpper (47242071824997463367517 / 482122044705607744000 : ℝ) ≤ (278534662756140487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (537533 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_407 : rowCell 0 407 ≤ (43284673881957719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (315049272843017199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (278534662756140487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_407_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_407_1
  · norm_num [gridPoint]

theorem exp_0_408_0 : expNegUpper (47404786193184619665693 / 483782602193190976000 : ℝ) ≤ (278534653446948239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (537533 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_408_1 : expNegUpper (379715354525641167628183 / 3870260817545527808000 : ℝ) ≤ (246232985485303713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (538051 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_408 : rowCell 0 408 ≤ (4783315962733177 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (278534653446948239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (246232985485303713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_408_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_408_1
  · norm_num [gridPoint]

theorem exp_0_409_0 : expNegUpper (1693426434048545870703 / 17260302736675328000 : ℝ) ≤ (123116488656024529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (538051 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_409_1 : expNegUpper (847777674225264460251 / 8630151368337664000 : ℝ) ≤ (217660495640472601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2154279 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_409 : rowCell 0 409 ≤ (16913764413494993 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (123116488656024529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (217660495640472601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_409_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_409_1
  · norm_num [gridPoint]

theorem exp_0_410_0 : expNegUpper (191404715693997080553451 / 1948449126132062464000 : ℝ) ≤ (21766048846501537 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2154279 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_410_1 : expNegUpper (383290381219501872123501 / 3896898252264124928000 : ℝ) ≤ (19238870477532371 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2156357 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_410 : rowCell 0 410 ≤ (14950577787328789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21766048846501537 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19238870477532371 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_410_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_410_1
  · norm_num [gridPoint]

theorem exp_0_411_0 : expNegUpper (384603750719029624650789 / 3910251227082056192000 : ℝ) ≤ (192388698476262869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2156357 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_411_1 : expNegUpper (3850866479723784093889 / 39102512270820561920 : ℝ) ≤ (42509527899645753 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1079219 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_411 : rowCell 0 411 ≤ (26428488608494939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (192388698476262869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42509527899645753 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_411_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_411_1
  · norm_num [gridPoint]

theorem exp_0_412_0 : expNegUpper (429337684051519842521 / 4359585600228602880 : ℝ) ≤ (170038106069235913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1079219 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_412_1 : expNegUpper (42987640405815251737579 / 435958560022860288000 : ℝ) ≤ (37568157803318457 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2160523 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_412 : rowCell 0 412 ≤ (11678673370909319 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (170038106069235913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37568157803318457 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_412_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_412_1
  · norm_num [gridPoint]

theorem exp_0_413_0 : expNegUpper (388209936162347508690299 / 3937025691635184128000 : ℝ) ≤ (30054525271979689 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2160523 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_413_1 : expNegUpper (194348369125858543800249 / 1968512845817592064000 : ℝ) ≤ (16599331786026193 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2162611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_413 : rowCell 0 413 ≤ (2580190052889999 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30054525271979689 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16599331786026193 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_413_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_413_1
  · norm_num [gridPoint]

theorem exp_0_414_0 : expNegUpper (7800436445186144452881 / 79008943627407616000 : ℝ) ≤ (33198662507110147 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2162611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_414_1 : expNegUpper (15620423270514260880193 / 158017887254815232000 : ℝ) ≤ (117340665356898777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2164703 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_414 : rowCell 0 414 ≤ (4560022982211591 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33198662507110147 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (117340665356898777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_414_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_414_1
  · norm_num [gridPoint]

theorem exp_0_415_0 : expNegUpper (43537731547731738539913 / 440432389934592512000 : ℝ) ≤ (117340661618372069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2164703 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_415_1 : expNegUpper (1362258000618382692987 / 13763512185456016000 : ℝ) ≤ (51838678673333721 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2166797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_415 : rowCell 0 415 ≤ (2014604064225887 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (117340661618372069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51838678673333721 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_415_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_415_1
  · norm_num [gridPoint]

theorem sum_0_384_2 : blockSum (rowCell 0) 384 2 ≤ (1358157703610135151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_384) (by simpa only [blockSum_one] using cell_0_385) (by norm_num)

theorem sum_0_386_2 : blockSum (rowCell 0) 386 2 ≤ (1065362410913735831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_386) (by simpa only [blockSum_one] using cell_0_387) (by norm_num)

theorem sum_0_384_4 : blockSum (rowCell 0) 384 4 ≤ (1211760057261935491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_384_2 sum_0_386_2 (by norm_num)

theorem sum_0_388_2 : blockSum (rowCell 0) 388 2 ≤ (208849605237712833 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_388) (by simpa only [blockSum_one] using cell_0_389) (by norm_num)

theorem sum_0_390_2 : blockSum (rowCell 0) 390 2 ≤ (81856026513176789 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_390) (by simpa only [blockSum_one] using cell_0_391) (by norm_num)

theorem sum_0_388_4 : blockSum (rowCell 0) 388 4 ≤ (372561658264066411 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_388_2 sum_0_390_2 (by norm_num)

theorem sum_0_384_8 : blockSum (rowCell 0) 384 8 ≤ (1956883373790068313 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_384_4 sum_0_388_4 (by norm_num)

theorem sum_0_392_2 : blockSum (rowCell 0) 392 2 ≤ (256572403650272703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_392) (by simpa only [blockSum_one] using cell_0_393) (by norm_num)

theorem sum_0_394_2 : blockSum (rowCell 0) 394 2 ≤ (100492371278239999 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_394) (by simpa only [blockSum_one] using cell_0_395) (by norm_num)

theorem sum_0_392_4 : blockSum (rowCell 0) 392 4 ≤ (457557146206752701 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_392_2 sum_0_394_2 (by norm_num)

theorem sum_0_396_2 : blockSum (rowCell 0) 396 2 ≤ (78694002106058521 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_396) (by simpa only [blockSum_one] using cell_0_397) (by norm_num)

theorem sum_0_398_2 : blockSum (rowCell 0) 398 2 ≤ (246414958957213813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_398) (by simpa only [blockSum_one] using cell_0_399) (by norm_num)

theorem sum_0_396_4 : blockSum (rowCell 0) 396 4 ≤ (561190967381447897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_396_2 sum_0_398_2 (by norm_num)

theorem sum_0_392_8 : blockSum (rowCell 0) 392 8 ≤ (1476305259794953299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_392_4 sum_0_396_4 (by norm_num)

theorem sum_0_384_16 : blockSum (rowCell 0) 384 16 ≤ (215602880295003597 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_384_8 sum_0_392_8 (by norm_num)

theorem sum_0_400_2 : blockSum (rowCell 0) 400 2 ≤ (192837243126727629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_400) (by simpa only [blockSum_one] using cell_0_401) (by norm_num)

theorem sum_0_402_2 : blockSum (rowCell 0) 402 2 ≤ (150860184005037687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_402) (by simpa only [blockSum_one] using cell_0_403) (by norm_num)

theorem sum_0_400_4 : blockSum (rowCell 0) 400 4 ≤ (85924356782941329 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_400_2 sum_0_402_2 (by norm_num)

theorem sum_0_404_2 : blockSum (rowCell 0) 404 2 ≤ (29495766567957907 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_404) (by simpa only [blockSum_one] using cell_0_405) (by norm_num)

theorem sum_0_406_2 : blockSum (rowCell 0) 406 2 ≤ (92241739509431347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_406) (by simpa only [blockSum_one] using cell_0_407) (by norm_num)

theorem sum_0_404_4 : blockSum (rowCell 0) 404 4 ≤ (8408992231250519 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_404_2 sum_0_406_2 (by norm_num)

theorem sum_0_400_8 : blockSum (rowCell 0) 400 8 ≤ (553922232913028291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_400_4 sum_0_404_4 (by norm_num)

theorem sum_0_408_2 : blockSum (rowCell 0) 408 2 ≤ (36047028264427701 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_408) (by simpa only [blockSum_one] using cell_0_409) (by norm_num)

theorem sum_0_410_2 : blockSum (rowCell 0) 410 2 ≤ (56329644183152517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_410) (by simpa only [blockSum_one] using cell_0_411) (by norm_num)

theorem sum_0_408_4 : blockSum (rowCell 0) 408 4 ≤ (128423700712007919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_408_2 sum_0_410_2 (by norm_num)

theorem sum_0_412_2 : blockSum (rowCell 0) 412 2 ≤ (4399886716493863 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_412) (by simpa only [blockSum_one] using cell_0_413) (by norm_num)

theorem sum_0_414_2 : blockSum (rowCell 0) 414 2 ≤ (1717846222132673 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_414) (by simpa only [blockSum_one] using cell_0_415) (by norm_num)

theorem sum_0_412_4 : blockSum (rowCell 0) 412 4 ≤ (7835579160759209 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_412_2 sum_0_414_2 (by norm_num)

theorem sum_0_408_8 : blockSum (rowCell 0) 408 8 ≤ (206779492319600009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_408_4 sum_0_412_4 (by norm_num)

theorem sum_0_400_16 : blockSum (rowCell 0) 400 16 ≤ (7607017252326283 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_400_8 sum_0_408_8 (by norm_num)

theorem sum_0_384_32 : blockSum (rowCell 0) 384 32 ≤ (246030949304308729 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_384_16 sum_0_400_16 (by norm_num)

#print axioms sum_0_384_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
