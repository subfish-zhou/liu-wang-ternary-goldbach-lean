import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_288_0 : expNegUpper (6711573006734613731607 / 76224722892415504000 : ℝ) ≤ (230644877625108241949 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1989511 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_288_1 : expNegUpper (215016846218399441792623 / 2439191132557296128000 : ℝ) ≤ (5211863946757032291189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1991083 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_288 : rowCell 3 288 ≤ (800524593942290816973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (230644877625108241949 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5211863946757032291189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_288_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_288_1
  · norm_num [gridPoint]

theorem exp_3_289_0 : expNegUpper (959770268966364204743 / 10887812595880448000 : ℝ) ≤ (1042372680562644254091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1991083 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_289_1 : expNegUpper (480436359082355233751 / 5443906297940224000 : ℝ) ≤ (2354986340412807390551 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (996329 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_289 : rowCell 3 289 ≤ (723509201368550319147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1042372680562644254091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2354986340412807390551 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_289_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_289_1
  · norm_num [gridPoint]

theorem exp_3_290_0 : expNegUpper (108565455675172060925671 / 1230173686947330304000 : ℝ) ≤ (4709972193489315104363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (996329 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_290_1 : expNegUpper (217380506817487686621381 / 2460347373894660608000 : ℝ) ≤ (4255595722603385027779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (997119 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_290 : rowCell 3 290 ≤ (163444316860976077043 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4709972193489315104363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4255595722603385027779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_290_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_290_1
  · norm_num [gridPoint]

theorem exp_3_291_0 : expNegUpper (218318148706582813492989 / 2470959752021975552000 : ℝ) ≤ (425559528605918666483 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (997119 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_291_1 : expNegUpper (10928464595101079141099 / 123547987601098777600 : ℝ) ≤ (153772800988126474277 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (997911 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_291 : rowCell 3 291 ≤ (295326550864226233627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (425559528605918666483 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (153772800988126474277 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_291_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_291_1
  · norm_num [gridPoint]

theorem exp_3_292_0 : expNegUpper (1219500180991592598451 / 13786638713639142400 : ℝ) ≤ (3844319633724622082039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (997911 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_292_1 : expNegUpper (24418080759222243390979 / 275732774272782848000 : ℝ) ≤ (1736066813156047786001 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1997411 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_292 : rowCell 3 292 ≤ (133380586274463316393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3844319633724622082039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1736066813156047786001 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_292_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_292_1
  · norm_num [gridPoint]

theorem exp_3_293_0 : expNegUpper (220706572958394331264979 / 2492253023193870848000 : ℝ) ≤ (138885331048121164153 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1997411 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_293_1 : expNegUpper (110480410801381078220469 / 1246126511596935424000 : ℝ) ≤ (156769504877845951581 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1999003 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_293 : rowCell 3 293 ≤ (481826540861356530491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (138885331048121164153 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (156769504877845951581 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_293_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_293_1
  · norm_num [gridPoint]

theorem exp_3_294_0 : expNegUpper (4438155596772889017069 / 50058678324769024000 : ℝ) ≤ (783847446024609300517 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1999003 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_294_1 : expNegUpper (8886543448145845092697 / 100117356649538048000 : ℝ) ≤ (2830776045118998620063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (10003 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_294 : rowCell 3 294 ≤ (43505817249364760769 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (783847446024609300517 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2830776045118998620063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_294_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_294_1
  · norm_num [gridPoint]

theorem exp_3_295_0 : expNegUpper (24790407023508408135073 / 279293071954309632000 : ℝ) ≤ (1415387882260872942059 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (10003 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_295_1 : expNegUpper (3102375425388760414963 / 34911633994288704000 : ℝ) ≤ (159705089037239952781 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2002201 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_295 : rowCell 3 295 ≤ (392756129266210155409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1415387882260872942059 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (159705089037239952781 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_295_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_295_1
  · norm_num [gridPoint]

theorem exp_3_296_0 : expNegUpper (28040529133690830635083 / 315545527155609664000 : ℝ) ≤ (2555281173456927065117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2002201 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_296_1 : expNegUpper (44916632973626934169947 / 504872843448975462400 : ℝ) ≤ (576543106342104182813 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1001903 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_296 : rowCell 3 296 ≤ (354501564138561764277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2555281173456927065117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (576543106342104182813 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_296_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_296_1
  · norm_num [gridPoint]

theorem exp_3_297_0 : expNegUpper (45107899880967202635507 / 507022725041344614400 : ℝ) ≤ (576543050158150469353 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1001903 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_297_1 : expNegUpper (112899999458208268481843 / 1267556812603361536000 : ℝ) ≤ (2080966712470932075361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (401083 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_297 : rowCell 3 297 ≤ (319914111113626937293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (576543050158150469353 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2080966712470932075361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_297_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_297_1
  · norm_num [gridPoint]

theorem exp_3_298_0 : expNegUpper (406378982454914738773 / 4562519482928896000 : ℝ) ≤ (1040483255697814536523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (401083 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_298_1 : expNegUpper (813697285896684569707 / 9125038965857792000 : ℝ) ≤ (938705413638805264557 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2007029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_298 : rowCell 3 298 ≤ (288648431890692846029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1040483255697814536523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (938705413638805264557 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_298_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_298_1
  · norm_num [gridPoint]

theorem exp_3_299_0 : expNegUpper (364774658363015239973 / 4090689529676288000 : ℝ) ≤ (1877410647401366786311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2007029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_299_1 : expNegUpper (91299122562699476613 / 1022672382419072000 : ℝ) ≤ (1693459564819734918801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1004323 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_299 : rowCell 3 299 ≤ (260391064078869028733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1877410647401366786311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1693459564819734918801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_299_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_299_1
  · norm_num [gridPoint]

theorem exp_3_300_0 : expNegUpper (57303394299575240537493 / 641874719731697792000 : ℝ) ≤ (1693459403933832254813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1004323 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_300_1 : expNegUpper (229478799833476273445491 / 2567498878926791168000 : ℝ) ≤ (1527257160318686099779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (502567 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_300 : rowCell 3 300 ≤ (234857545477831834039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1693459403933832254813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1527257160318686099779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_300_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_300_1
  · norm_num [gridPoint]

theorem exp_3_301_0 : expNegUpper (25605303262936709162771 / 286482182234628608000 : ℝ) ≤ (381814254110391091397 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (502567 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_301_1 : expNegUpper (2563494811529959860181 / 28648218223462860800 : ℝ) ≤ (344280032788727229371 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1005947 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_301 : rowCell 3 301 ≤ (211789791004078375509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (381814254110391091397 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (344280032788727229371 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_301_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_301_1
  · norm_num [gridPoint]

theorem exp_3_302_0 : expNegUpper (23168662797361143265709 / 258920323960227891200 : ℝ) ≤ (55084800100365455557 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1005947 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_302_1 : expNegUpper (231955016011747680173961 / 2589203239602278912000 : ℝ) ≤ (1241521633070348388061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (503381 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_302 : rowCell 3 302 ≤ (95476850376150247941 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (55084800100365455557 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1241521633070348388061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_302_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_302_1
  · norm_num [gridPoint]

theorem exp_3_303_0 : expNegUpper (232930283012182759455489 / 2600089677398655488000 : ℝ) ≤ (248304303612377982703 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (503381 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_303_1 : expNegUpper (14575016171748049902973 / 162505604837415968000 : ℝ) ≤ (559538600499800373519 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1007579 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_303 : rowCell 3 303 ≤ (2689640303818368059 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (248304303612377982703 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (559538600499800373519 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_303_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_303_1
  · norm_num [gridPoint]

theorem exp_3_304_0 : expNegUpper (65049640131800835997 / 725277487083552000 : ℝ) ≤ (1119077098199158479599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1007579 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_304_1 : expNegUpper (1042001205505326173183 / 11604439793336832000 : ℝ) ≤ (1008531755614354062583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (504199 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_304 : rowCell 3 304 ≤ (77573574571830466327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1119077098199158479599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1008531755614354062583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_304_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_304_1
  · norm_num [gridPoint]

theorem exp_3_305_0 : expNegUpper (235431902352850829787287 / 2621931067908674048000 : ℝ) ≤ (504265831870288612563 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (504199 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_305_1 : expNegUpper (117852531738137549229423 / 1310965533954337024000 : ℝ) ≤ (454373883256726849253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1009219 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_305 : rowCell 3 305 ≤ (8738108663116378363 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (504265831870288612563 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (454373883256726849253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_305_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_305_1
  · norm_num [gridPoint]

theorem exp_3_306_0 : expNegUpper (118344943319812433389407 / 1316443010311158016000 : ℝ) ≤ (113593460552229177693 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1009219 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_306_1 : expNegUpper (47392929090607514730929 / 526577204124463206400 : ℝ) ≤ (818694472059433122349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (505021 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_306 : rowCell 3 306 ≤ (5038665361965389457 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (113593460552229177693 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (818694472059433122349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_306_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_306_1
  · norm_num [gridPoint]

theorem exp_3_307_0 : expNegUpper (5287837051714305939841 / 58752529147593625600 : ℝ) ≤ (409347199356358071889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (505021 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_307_1 : expNegUpper (6617472976703457257851 / 73440661434492032000 : ℝ) ≤ (737438064209687319501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (404347 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_307 : rowCell 3 307 ≤ (11347457728406131739 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (409347199356358071889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (737438064209687319501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_307_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_307_1
  · norm_num [gridPoint]

theorem exp_3_308_0 : expNegUpper (59805063601936544514611 / 663716110241716352000 : ℝ) ≤ (737437998689658410907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (404347 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_308_1 : expNegUpper (239498218593474408071883 / 2654864440966865408000 : ℝ) ≤ (26565310174829708207 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2023389 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_308 : rowCell 3 308 ≤ (102203798536887902089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (737437998689658410907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26565310174829708207 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_308_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_308_1
  · norm_num [gridPoint]

theorem exp_3_309_0 : expNegUpper (9619706314950829832187 / 106635516343910912000 : ℝ) ≤ (6641326958512402449 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2023389 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_309_1 : expNegUpper (4815444594836521215029 / 53317758171955456000 : ℝ) ≤ (598012643367661410457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (253131 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_309 : rowCell 3 309 ≤ (92036772094545513191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6641326958512402449 / 10000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (598012643367661410457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_309_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_309_1
  · norm_num [gridPoint]

theorem exp_3_310_0 : expNegUpper (13431660428753117625589 / 148718567474135296000 : ℝ) ≤ (598012591108703699061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (253131 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_310_1 : expNegUpper (26894563399857562894489 / 297437134948270592000 : ℝ) ≤ (538384325114362937523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (202671 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_310 : rowCell 3 310 ≤ (41433542056295219151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (598012591108703699061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (538384325114362937523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_310_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_310_1
  · norm_num [gridPoint]

theorem exp_3_311_0 : expNegUpper (243051953931440939155289 / 2688003358776852992000 : ℝ) ≤ (134596069613318693549 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (202671 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_311_1 : expNegUpper (1216673755782445353489 / 13440016793884264960 : ℝ) ≤ (24231007976905451149 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2028377 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_311 : rowCell 3 311 ≤ (37299201361940732187 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (134596069613318693549 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24231007976905451149 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_311_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_311_1
  · norm_num [gridPoint]

theorem exp_3_312_0 : expNegUpper (1221694332538819291089 / 13495476706625128960 : ℝ) ≤ (484620117881548847819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2028377 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_312_1 : expNegUpper (244623281407477721422711 / 2699095341325025792000 : ℝ) ≤ (109038038948260896393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2030047 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_312 : rowCell 3 312 ≤ (209823567039659093 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (484620117881548847819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (109038038948260896393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_312_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_312_1
  · norm_num [gridPoint]

theorem exp_3_313_0 : expNegUpper (27292292826540391241911 / 301134462464328192000 : ℝ) ≤ (436152118609841248131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2030047 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_313_1 : expNegUpper (13662037296890148053011 / 150567231232164096000 : ℝ) ≤ (98116602957769754943 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1015861 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_313 : rowCell 3 313 ≤ (1208472154034256979 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (436152118609841248131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (98116602957769754943 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_313_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_313_1
  · norm_num [gridPoint]

theorem exp_3_314_0 : expNegUpper (4938545414341571495251 / 54426956426772736000 : ℝ) ≤ (196233189322901527533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1015861 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_314_1 : expNegUpper (9888597238338501920853 / 108853912853545472000 : ℝ) ≤ (5517157203413022683 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (10167 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_314 : rowCell 3 314 ≤ (1698975899480230841 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (196233189322901527533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5517157203413022683 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_314_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_314_1
  · norm_num [gridPoint]

theorem exp_3_315_0 : expNegUpper (248228782334747665702917 / 2732508318804075008000 : ℝ) ≤ (88274507851403679563 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (10167 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_315_1 : expNegUpper (62129517560784004338289 / 683127079701018752000 : ℝ) ≤ (317626680725077997841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2035083 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_315 : rowCell 3 315 ≤ (48909848612803667777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (88274507851403679563 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (317626680725077997841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_315_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_315_1
  · norm_num [gridPoint]

theorem exp_3_316_0 : expNegUpper (6931532785672484464649 / 76213657071535232000 : ℝ) ≤ (63525330860804747553 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2035083 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_316_1 : expNegUpper (5551691093119593770639 / 60970925657228185600 : ℝ) ≤ (5713442434044173291 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2036769 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_316 : rowCell 3 316 ≤ (43993088772618534877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (63525330860804747553 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5713442434044173291 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_316_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_316_1
  · norm_num [gridPoint]

theorem exp_3_317_0 : expNegUpper (50169294911560509312991 / 550979565730443366400 : ℝ) ≤ (285672098132347555807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2036769 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_317_1 : expNegUpper (125569513896269150863593 / 1377448914326108416000 : ℝ) ≤ (256890720627364759169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (101923 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_317 : rowCell 3 317 ≤ (19782084101370350719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (285672098132347555807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (256890720627364759169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_317_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_317_1
  · norm_num [gridPoint]

theorem exp_3_318_0 : expNegUpper (126081337573932814972377 / 1383063420517460224000 : ℝ) ≤ (32111337450508676187 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (101923 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_318_1 : expNegUpper (252456866041944410227513 / 2766126841034920448000 : ℝ) ≤ (230971861463663855887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1020077 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_318 : rowCell 3 318 ≤ (8893844066769704751 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32111337450508676187 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (230971861463663855887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_318_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_318_1
  · norm_num [gridPoint]

theorem exp_3_319_0 : expNegUpper (1126594631318832611537 / 12343905296548352000 : ℝ) ≤ (28871480339312812213 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1020077 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_319_1 : expNegUpper (17623584995204075827 / 192873520258568000 : ℝ) ≤ (207634854272580592753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2041853 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_319 : rowCell 3 319 ≤ (31983594405002423289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28871480339312812213 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (207634854272580592753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_319_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_319_1
  · norm_num [gridPoint]

theorem sum_3_288_2 : blockSum (rowCell 3) 288 2 ≤ (38100844882771028403 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_288) (by simpa only [blockSum_one] using cell_3_289) (by norm_num)

theorem sum_3_290_2 : blockSum (rowCell 3) 290 2 ≤ (622215184586178387713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_290) (by simpa only [blockSum_one] using cell_3_291) (by norm_num)

theorem sum_3_288_4 : blockSum (rowCell 3) 288 4 ≤ (1384232082241598955773 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_288_2 sum_3_290_2 (by norm_num)

theorem sum_3_292_2 : blockSum (rowCell 3) 292 2 ≤ (1015348885959209796063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_292) (by simpa only [blockSum_one] using cell_3_293) (by norm_num)

theorem sum_3_294_2 : blockSum (rowCell 3) 294 2 ≤ (827814301759857763099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_294) (by simpa only [blockSum_one] using cell_3_295) (by norm_num)

theorem sum_3_292_4 : blockSum (rowCell 3) 292 4 ≤ (921581593859533779581 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_292_2 sum_3_294_2 (by norm_num)

theorem sum_3_288_8 : blockSum (rowCell 3) 288 8 ≤ (1152906838050566367677 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_288_4 sum_3_292_4 (by norm_num)

theorem sum_3_296_2 : blockSum (rowCell 3) 296 2 ≤ (67441567525218870157 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_296) (by simpa only [blockSum_one] using cell_3_297) (by norm_num)

theorem sum_3_298_2 : blockSum (rowCell 3) 298 2 ≤ (274519747984780937381 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_298) (by simpa only [blockSum_one] using cell_3_299) (by norm_num)

theorem sum_3_296_4 : blockSum (rowCell 3) 296 4 ≤ (305863792805437644083 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_296_2 sum_3_298_2 (by norm_num)

theorem sum_3_300_2 : blockSum (rowCell 3) 300 2 ≤ (111661834120477552387 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_300) (by simpa only [blockSum_one] using cell_3_301) (by norm_num)

theorem sum_3_302_2 : blockSum (rowCell 3) 302 2 ≤ (181545340098338025829 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_302) (by simpa only [blockSum_one] using cell_3_303) (by norm_num)

theorem sum_3_300_4 : blockSum (rowCell 3) 300 4 ≤ (404869008339293130603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_300_2 sum_3_302_2 (by norm_num)

theorem sum_3_296_8 : blockSum (rowCell 3) 296 8 ≤ (1016596593950168418769 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_296_4 sum_3_300_4 (by norm_num)

theorem sum_3_288_16 : blockSum (rowCell 3) 288 16 ≤ (3322410270051301154123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_288_8 sum_3_296_8 (by norm_num)

theorem sum_3_304_2 : blockSum (rowCell 3) 304 2 ≤ (147478443876761493231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_304) (by simpa only [blockSum_one] using cell_3_305) (by norm_num)

theorem sum_3_306_2 : blockSum (rowCell 3) 306 2 ≤ (47888242266639210763 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_306) (by simpa only [blockSum_one] using cell_3_307) (by norm_num)

theorem sum_3_304_4 : blockSum (rowCell 3) 304 4 ≤ (534398099086719040277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_304_2 sum_3_306_2 (by norm_num)

theorem sum_3_308_2 : blockSum (rowCell 3) 308 2 ≤ (2428007132892917691 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_308) (by simpa only [blockSum_one] using cell_3_309) (by norm_num)

theorem sum_3_310_2 : blockSum (rowCell 3) 310 2 ≤ (39366371709117975669 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_310) (by simpa only [blockSum_one] using cell_3_311) (by norm_num)

theorem sum_3_308_4 : blockSum (rowCell 3) 308 4 ≤ (87926514366976329489 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_308_2 sum_3_310_2 (by norm_num)

theorem sum_3_304_8 : blockSum (rowCell 3) 304 8 ≤ (886104156554624358233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_304_4 sum_3_308_4 (by norm_num)

theorem sum_3_312_2 : blockSum (rowCell 3) 312 2 ≤ (12756714915440375871 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_312) (by simpa only [blockSum_one] using cell_3_313) (by norm_num)

theorem sum_3_314_2 : blockSum (rowCell 3) 314 2 ≤ (103277077396171054689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_314) (by simpa only [blockSum_one] using cell_3_315) (by norm_num)

theorem sum_3_312_4 : blockSum (rowCell 3) 312 4 ≤ (230844226550574813399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_312_2 sum_3_314_2 (by norm_num)

theorem sum_3_316_2 : blockSum (rowCell 3) 316 2 ≤ (16711451395071847263 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_316) (by simpa only [blockSum_one] using cell_3_317) (by norm_num)

theorem sum_3_318_2 : blockSum (rowCell 3) 318 2 ≤ (67558970672081242293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_318) (by simpa only [blockSum_one] using cell_3_319) (by norm_num)

theorem sum_3_316_4 : blockSum (rowCell 3) 316 4 ≤ (9444764227965029913 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_316_2 sum_3_318_2 (by norm_num)

theorem sum_3_312_8 : blockSum (rowCell 3) 312 8 ≤ (381960454198015292007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_312_4 sum_3_316_4 (by norm_num)

theorem sum_3_304_16 : blockSum (rowCell 3) 304 16 ≤ (3962701908601998907 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_304_8 sum_3_312_8 (by norm_num)

theorem sum_3_288_32 : blockSum (rowCell 3) 288 32 ≤ (3956442575427620979243 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_288_16 sum_3_304_16 (by norm_num)

#print axioms sum_3_288_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
