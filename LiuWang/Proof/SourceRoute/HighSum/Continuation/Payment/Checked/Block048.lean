import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_0_0 : expNegUpper (54401311635381940881 / 676601617795489000 : ℝ) ≤ (12064973229033056527344737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (468537 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_0_1 : expNegUpper (27794768061916040690191 / 346420028311290368000 : ℝ) ≤ (2858583251370692506282157 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (467917 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_0 : rowCell 3 0 ≤ (12012756138919874662087 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12064973229033056527344737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2858583251370692506282157 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_0_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_0_1
  · norm_num [gridPoint]

theorem exp_3_1_0 : expNegUpper (3123871788872869792271 / 38934366418846208000 : ℝ) ≤ (14292842827264115969067757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (467917 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_1_1 : expNegUpper (311741382296470398211 / 3893436641884620800 : ℝ) ≤ (16871518783148169352313557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (373849 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_1 : rowCell 3 1 ≤ (2272533247862398200422719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14292842827264115969067757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16871518783148169352313557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_1_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_1_1
  · norm_num [gridPoint]

theorem exp_3_2_0 : expNegUpper (2837796937985371368779 / 35442140553369651200 : ℝ) ≤ (8435717031422174449578761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (373849 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_2_1 : expNegUpper (28320432819685791055461 / 354421405533696512000 : ℝ) ≤ (19845182944133468510498487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2987 / 1600 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_2 : rowCell 3 2 ≤ (1338704349867207326072473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8435717031422174449578761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19845182944133468510498487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_2_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_2_1
  · norm_num [gridPoint]

theorem exp_3_3_0 : expNegUpper (28642851389647857132189 / 358456351603532288000 : ℝ) ≤ (396901710573866372857459 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466719 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_3_1 : expNegUpper (7146475823316263267167 / 89614087900883072000 : ℝ) ≤ (11631065680458476369945577 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (23307 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_3 : rowCell 3 3 ≤ (1571708492365277624229677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (396901710573866372857459 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11631065680458476369945577 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_3_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_3_1
  · norm_num [gridPoint]

theorem exp_3_4_0 : expNegUpper (32121669023974339103 / 402793484421248000 : ℝ) ≤ (22716816134363810705737 / 976562500000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (23307 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_4_1 : expNegUpper (128236203643372304923 / 1611173937684992000 : ℝ) ≤ (13587284512490137412321409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1862297 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_4 : rowCell 3 4 ≤ (735576273104500026027341 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22716816134363810705737 / 976562500000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13587284512490137412321409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_4_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_4_1
  · norm_num [gridPoint]

theorem exp_3_5_0 : expNegUpper (29177931567979504598387 / 366594758660469248000 : ℝ) ≤ (6793610376089125319174237 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1862297 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_5_1 : expNegUpper (14561085195752792200773 / 183297379330234624000 : ℝ) ≤ (3954843795598352969853843 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (372017 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_5 : rowCell 3 5 ≤ (2144355395537500597523383 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6793610376089125319174237 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3954843795598352969853843 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_5_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_5_1
  · norm_num [gridPoint]

theorem exp_3_6_0 : expNegUpper (14724074860597151039157 / 185349109823785216000 : ℝ) ≤ (7909651293291484163116609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (372017 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_6_1 : expNegUpper (5878597400168829435869 / 74139643929514086400 : ℝ) ≤ (36715010581656744979430893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (464481 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_6 : rowCell 3 6 ≤ (2492203536146662334050491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7909651293291484163116609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36715010581656744979430893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_6_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_6_1
  · norm_num [gridPoint]

theorem exp_3_7_0 : expNegUpper (660448146079109874701 / 8329433754231705600 : ℝ) ≤ (18357422897096314858222741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (464481 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_7_1 : expNegUpper (412022300557126439863 / 5205896096394816000 : ℝ) ≤ (10616939257803223231403731 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (463953 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_7 : rowCell 3 7 ≤ (2887033269324148330666647 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18357422897096314858222741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10616939257803223231403731 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_7_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_7_1
  · norm_num [gridPoint]

theorem exp_3_8_0 : expNegUpper (3749249014676884772143 / 47371707067379776000 : ℝ) ≤ (42467570585957404468565337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (463953 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_8_1 : expNegUpper (29940036301651100602983 / 378973656539038208000 : ℝ) ≤ (24482708310500646118502039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1853749 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_8 : rowCell 3 8 ≤ (3333687786977935957862097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42467570585957404468565337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24482708310500646118502039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_8_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_8_1
  · norm_num [gridPoint]

theorem exp_3_9_0 : expNegUpper (1210785453803934010167 / 15325825297736192000 : ℝ) ≤ (48965206317937376674709659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1853749 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_9_1 : expNegUpper (604325779555935694139 / 7662912648868096000 : ℝ) ≤ (56280335473956099379628393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (925867 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_9 : rowCell 3 9 ≤ (959324933000790741022153 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (48965206317937376674709659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (56280335473956099379628393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_9_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_9_1
  · norm_num [gridPoint]

theorem exp_3_10_0 : expNegUpper (1697061624941578184539 / 21518913702973696000 : ℝ) ≤ (7035012371889395217233011 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (925867 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_10_1 : expNegUpper (3388263740098755856789 / 43037827405947392000 : ℝ) ≤ (64488627472073849064337773 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (924883 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_10 : rowCell 3 10 ≤ (8806564035681690064073453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7035012371889395217233011 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64488627472073849064337773 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_10_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_10_1
  · norm_num [gridPoint]

theorem exp_3_11_0 : expNegUpper (30826420821303896108789 / 391558099169403392000 : ℝ) ≤ (32244181151411903077617379 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (924883 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_11_1 : expNegUpper (61548600686531602689 / 783116198338806784 : ℝ) ≤ (36834984372050150550633123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1847843 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_11 : rowCell 3 11 ≤ (10074629626567255872021667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32244181151411903077617379 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36834984372050150550633123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_11_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_11_1
  · norm_num [gridPoint]

theorem exp_3_12_0 : expNegUpper (62215162109006926689 / 791597179982070784 : ℝ) ≤ (14733934459136405112819163 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1847843 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_12_1 : expNegUpper (31056079017266427336211 / 395798589991035392000 : ℝ) ≤ (83907335692515743222061589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (922983 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_12 : rowCell 3 12 ≤ (2872664248898123924079873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14733934459136405112819163 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (83907335692515743222061589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_12_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_12_1
  · norm_num [gridPoint]

theorem exp_3_13_0 : expNegUpper (3487844437876195084211 / 44451324346491392000 : ℝ) ≤ (83907005225895218590574857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (922983 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_13_1 : expNegUpper (1741095537512740411961 / 22225662173245696000 : ℝ) ≤ (23821671191022601583024419 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (461033 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_13 : rowCell 3 13 ≤ (13066964868400602147071173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (83907005225895218590574857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23821671191022601583024419 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_13_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_13_1
  · norm_num [gridPoint]

theorem exp_3_14_0 : expNegUpper (633509749455788401561 / 8086961731031296000 : ℝ) ≤ (47643158707590983020313649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (461033 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_14_1 : expNegUpper (1265009292379725932433 / 16173923462062592000 : ℝ) ≤ (21579314569681511626364107 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842343 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_14 : rowCell 3 14 ≤ (740813945257445964818401 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47643158707590983020313649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21579314569681511626364107 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_14_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_14_1
  · norm_num [gridPoint]

theorem exp_3_15_0 : expNegUpper (31962253642553103034017 / 408657092290462208000 : ℝ) ≤ (26974041408677549886599559 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842343 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_15_1 : expNegUpper (1994539182024783546991 / 25541068268153888000 : ℝ) ≤ (60913858965948082719232277 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (460149 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_15 : rowCell 3 15 ≤ (4187917995557144501900559 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26974041408677549886599559 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (60913858965948082719232277 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_15_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_15_1
  · norm_num [gridPoint]

theorem exp_3_16_0 : expNegUpper (223964641961912856631 / 2867978724549408000 : ℝ) ≤ (24365453552114053981610663 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (460149 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_16_1 : expNegUpper (715598077250625321499 / 9177531918558105600 : ℝ) ≤ (137172500431306067252609541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1838891 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_16 : rowCell 3 16 ≤ (4721623947913964348663051 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24365453552114053981610663 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (137172500431306067252609541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_16_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_16_1
  · norm_num [gridPoint]

theorem exp_3_17_0 : expNegUpper (6508292373003022353931 / 83468723737104486400 : ℝ) ≤ (68586002054351051984135227 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1838891 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_17_1 : expNegUpper (16246550996738301593343 / 208671809342761216000 : ℝ) ≤ (154024406468926088614257981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1837227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_17 : rowCell 3 17 ≤ (21234303881095776140947247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (68586002054351051984135227 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (154024406468926088614257981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_17_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_17_1
  · norm_num [gridPoint]

theorem exp_3_18_0 : expNegUpper (16416961951195365503727 / 210860569670842624000 : ℝ) ≤ (38505965177890061075794089 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1837227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_18_1 : expNegUpper (32786202456330574638613 / 421721139341685248000 : ℝ) ≤ (172477415219611726566114107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835603 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_18 : rowCell 3 18 ≤ (23808766381891154528106239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38505965177890061075794089 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (172477415219611726566114107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_18_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_18_1
  · norm_num [gridPoint]

theorem exp_3_19_0 : expNegUpper (4749577712828810867 / 61092687928832000 : ℝ) ≤ (172476816666566117008974563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835603 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_19_1 : expNegUpper (1185706984128268837 / 15273171982208000 : ℝ) ≤ (192625333343195555363146577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91701 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_19 : rowCell 3 19 ≤ (6655894200043680136156899 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (172476816666566117008974563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (192625333343195555363146577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_19_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_19_1
  · norm_num [gridPoint]

theorem exp_3_20_0 : expNegUpper (8356153447781108217083 / 107636173892819072000 : ℝ) ≤ (38524935713980597636492079 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91701 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_20_1 : expNegUpper (33378179188359627656811 / 430544695571276288000 : ℝ) ≤ (107280540200309194604166773 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (73299 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_20 : rowCell 3 20 ≤ (14846175687542871958568347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38524935713980597636492079 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (107280540200309194604166773 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_20_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_20_1
  · norm_num [gridPoint]

theorem exp_3_21_0 : expNegUpper (33722861627159808949539 / 434990731144704512000 : ℝ) ≤ (26820045741746727872107333 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (73299 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_21_1 : expNegUpper (3367707544221200268121 / 43499073114470451200 : ℝ) ≤ (238375930023118480550389067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1830969 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_21 : rowCell 3 21 ≤ (6605704327228913944664671 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26820045741746727872107333 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (238375930023118480550389067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_21_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_21_1
  · norm_num [gridPoint]

theorem exp_3_22_0 : expNegUpper (378033978304730341889 / 4882884500265420800 : ℝ) ≤ (238375152357841633593316619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1830969 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_22_1 : expNegUpper (3775324845674941372729 / 48828845002654208000 : ℝ) ≤ (10566348497831301599986861 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (3659 / 2000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_22 : rowCell 3 22 ≤ (18322610458374717122247079 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (238375152357841633593316619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10566348497831301599986861 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_22_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_22_1
  · norm_num [gridPoint]

theorem exp_3_23_0 : expNegUpper (34325213044260845058809 / 443951317208826368000 : ℝ) ≤ (26415786806193881670544211 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (3659 / 2000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_23_1 : expNegUpper (4285091710910710425741 / 55493914651103296000 : ℝ) ≤ (291994984814495405622045299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828069 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_23 : rowCell 3 23 ≤ (8111033140065667932698401 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26415786806193881670544211 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (291994984814495405622045299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_23_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_23_1
  · norm_num [gridPoint]

theorem exp_3_24_0 : expNegUpper (6925867322000759709 / 89693173539904000 : ℝ) ≤ (291994070196065699649710119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828069 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_24_1 : expNegUpper (55336825061094852103 / 717545388319232000 : ℝ) ≤ (12878647056560106271688299 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (913337 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_24 : rowCell 3 24 ≤ (22385266393857624142516811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (291994070196065699649710119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12878647056560106271688299 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_24_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_24_1
  · norm_num [gridPoint]

theorem exp_3_25_0 : expNegUpper (3881715415221470884183 / 50333695166218752000 : ℝ) ≤ (321965188068376922763978023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (913337 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_25_1 : expNegUpper (1938459973950495364387 / 25166847583109376000 : ℝ) ≤ (177074358315143251246715181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (365063 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_25 : rowCell 3 25 ≤ (986056667534255793503827 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (321965188068376922763978023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (177074358315143251246715181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_25_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_25_1
  · norm_num [gridPoint]

theorem exp_3_26_0 : expNegUpper (17621764708783905012907 / 228781741799086336000 : ℝ) ≤ (354147651108541511591816917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (365063 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_26_1 : expNegUpper (7040207056679646423753 / 91512696719634534400 : ℝ) ≤ (388613154039595848700970899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823991 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_26 : rowCell 3 26 ≤ (27081392617781525796104863 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (354147651108541511591816917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (388613154039595848700970899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_26_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_26_1
  · norm_num [gridPoint]

theorem exp_3_27_0 : expNegUpper (7110723728813232295713 / 92429309801226342400 : ℝ) ≤ (194306003978702246431196351 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823991 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_27_1 : expNegUpper (8877948228097718993209 / 115536637251532928000 : ℝ) ≤ (212711637748685441772833391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911351 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_27 : rowCell 3 27 ≤ (2968009211467359967371397 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (194306003978702246431196351 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (212711637748685441772833391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_27_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_27_1
  · norm_num [gridPoint]

theorem exp_3_28_0 : expNegUpper (996269900245192751249 / 12965345908884608000 : ℝ) ≤ (17016881822255159198335637 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911351 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_28_1 : expNegUpper (3980506934491721650027 / 51861383635538432000 : ℝ) ≤ (464635234472574447125197039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821447 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_28 : rowCell 3 28 ≤ (1622594413013720247894497 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17016881822255159198335637 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (464635234472574447125197039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_28_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_28_1
  · norm_num [gridPoint]

theorem exp_3_29_0 : expNegUpper (1447193308167551578163 / 18855247789572608000 : ℝ) ≤ (18585356699282856257563367 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821447 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_29_1 : expNegUpper (722787075396814709601 / 9427623894786304000 : ℝ) ≤ (506296698127929479981923263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72809 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_29 : rowCell 3 29 ≤ (70801132810756226747991257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18585356699282856257563367 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (506296698127929479981923263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_29_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_29_1
  · norm_num [gridPoint]

theorem exp_3_30_0 : expNegUpper (18247988761245179717481 / 238016387532269824000 : ℝ) ≤ (506295291026631596291580303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72809 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_30_1 : expNegUpper (36456176982975244591321 / 476032775064539648000 : ℝ) ≤ (55044602277751897032731209 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1819037 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_30 : rowCell 3 30 ≤ (7705852601862278023437433 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (506295291026631596291580303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (55044602277751897032731209 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_30_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_30_1
  · norm_num [gridPoint]

theorem exp_3_31_0 : expNegUpper (4090462317341143968521 / 53411910410613248000 : ℝ) ≤ (137611130663819648874572829 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1819037 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_31_1 : expNegUpper (25538223640394214523 / 333824440066332800 : ℝ) ≤ (29855573367772134342186029 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817881 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_31 : rowCell 3 31 ≤ (20920203449729142791445403 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (137611130663819648874572829 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29855573367772134342186029 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_31_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_31_1
  · norm_num [gridPoint]

theorem sum_3_0_2 : blockSum (rowCell 3) 0 2 ≤ (4194574230089578146356639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_0) (by simpa only [blockSum_one] using cell_3_1) (by norm_num)

theorem sum_3_2_2 : blockSum (rowCell 3) 2 2 ≤ (58208256844649699006043 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_2) (by simpa only [blockSum_one] using cell_3_3) (by norm_num)

theorem sum_3_0_4 : blockSum (rowCell 3) 0 4 ≤ (10015399914554548046960939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_0_2 sum_3_2_2 (by norm_num)

theorem sum_3_4_2 : blockSum (rowCell 3) 4 2 ≤ (7966592156597501325183471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_4) (by simpa only [blockSum_one] using cell_3_5) (by norm_num)

theorem sum_3_6_2 : blockSum (rowCell 3) 6 2 ≤ (2689618402735405332358569 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_6) (by simpa only [blockSum_one] using cell_3_7) (by norm_num)

theorem sum_3_4_4 : blockSum (rowCell 3) 4 4 ≤ (18725065767539122654617747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_4_2 sum_3_6_2 (by norm_num)

theorem sum_3_0_8 : blockSum (rowCell 3) 0 8 ≤ (14370232841046835350789343 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_0_4 sum_3_4_4 (by norm_num)

theorem sum_3_8_2 : blockSum (rowCell 3) 8 2 ≤ (7170987518981098921950709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_8) (by simpa only [blockSum_one] using cell_3_9) (by norm_num)

theorem sum_3_10_2 : blockSum (rowCell 3) 10 2 ≤ (236014920778111824201189 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_10) (by simpa only [blockSum_one] using cell_3_11) (by norm_num)

theorem sum_3_8_4 : blockSum (rowCell 3) 8 4 ≤ (16611584350105571889998269 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_8_2 sum_3_10_2 (by norm_num)

theorem sum_3_12_2 : blockSum (rowCell 3) 12 2 ≤ (4911524372798619568678133 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_12) (by simpa only [blockSum_one] using cell_3_13) (by norm_num)

theorem sum_3_14_2 : blockSum (rowCell 3) 14 2 ≤ (1972996930461093581498141 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_14) (by simpa only [blockSum_one] using cell_3_15) (by norm_num)

theorem sum_3_12_4 : blockSum (rowCell 3) 12 4 ≤ (56125572751370595147360921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_12_2 sum_3_14_2 (by norm_num)

theorem sum_3_8_8 : blockSum (rowCell 3) 8 8 ≤ (89348741451581738927357459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_8_4 sum_3_12_4 (by norm_num)

theorem sum_3_0_16 : blockSum (rowCell 3) 0 16 ≤ (23617841426735081925787229 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_0_8 sum_3_8_8 (by norm_num)

theorem sum_3_16_2 : blockSum (rowCell 3) 16 2 ≤ (40120799672751633535599451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_16) (by simpa only [blockSum_one] using cell_3_17) (by norm_num)

theorem sum_3_18_2 : blockSum (rowCell 3) 18 2 ≤ (10086468636413175014546767 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_18) (by simpa only [blockSum_one] using cell_3_19) (by norm_num)

theorem sum_3_16_4 : blockSum (rowCell 3) 16 4 ≤ (45276571427408754304166643 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_16_2 sum_3_18_2 (by norm_num)

theorem sum_3_20_2 : blockSum (rowCell 3) 20 2 ≤ (62720873011230313640460049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_20) (by simpa only [blockSum_one] using cell_3_21) (by norm_num)

theorem sum_3_22_2 : blockSum (rowCell 3) 22 2 ≤ (77200386617077773907986163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_22) (by simpa only [blockSum_one] using cell_3_23) (by norm_num)

theorem sum_3_20_4 : blockSum (rowCell 3) 20 4 ≤ (34980314907077021887111553 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_20_2 sum_3_22_2 (by norm_num)

theorem sum_3_16_8 : blockSum (rowCell 3) 16 8 ≤ (115237201241562798078389749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_16_4 sum_3_20_4 (by norm_num)

theorem sum_3_24_2 : blockSum (rowCell 3) 24 2 ≤ (23518341541107009490056243 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_24) (by simpa only [blockSum_one] using cell_3_25) (by norm_num)

theorem sum_3_26_2 : blockSum (rowCell 3) 26 2 ≤ (56761484732455125469818833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_26) (by simpa only [blockSum_one] using cell_3_27) (by norm_num)

theorem sum_3_24_4 : blockSum (rowCell 3) 24 4 ≤ (103798167814669144449931319 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_24_2 sum_3_26_2 (by norm_num)

theorem sum_3_28_2 : blockSum (rowCell 3) 28 2 ≤ (135704909331305036663771137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_28) (by simpa only [blockSum_one] using cell_3_29) (by norm_num)

theorem sum_3_30_2 : blockSum (rowCell 3) 30 2 ≤ (80369669908769675700077971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_30) (by simpa only [blockSum_one] using cell_3_31) (by norm_num)

theorem sum_3_28_4 : blockSum (rowCell 3) 28 4 ≤ (296444249148844388063927079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_28_2 sum_3_30_2 (by norm_num)

theorem sum_3_24_8 : blockSum (rowCell 3) 24 8 ≤ (504040584778182676963789717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_24_4 sum_3_28_4 (by norm_num)

theorem sum_3_16_16 : blockSum (rowCell 3) 16 16 ≤ (146902997452261654624113843 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_16_8 sum_3_24_8 (by norm_num)

theorem sum_3_0_32 : blockSum (rowCell 3) 0 32 ≤ (10657552429937296034368817 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_0_16 sum_3_16_16 (by norm_num)

#print axioms sum_3_0_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
