import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_384_0 : (13750482821446779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (276858325758172953853 / 2779479919945113600 : ℝ) := by
  apply lower_of_taylor (t := (1088761 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_384 : (1002697561289309 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 384 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (13750482821446779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_384_0
  · norm_num [gridPoint]

theorem exp_7_385_0 : (49110827133682283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (89013517397813654667117 / 892623369099510784000 : ℝ) := by
  apply lower_of_taylor (t := (43589 / 20000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_385 : (7162411275193729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 385 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (49110827133682283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_385_0
  · norm_num [gridPoint]

theorem exp_7_386_0 : (21922803272986949 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (715470139345871171957 / 7166550987144192000 : ℝ) := by
  apply lower_of_taylor (t := (1090691 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_386 : (1278904408747819 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 386 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (21922803272986949 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_386_0
  · norm_num [gridPoint]

theorem exp_7_387_0 : (39140350466739563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (359421667207842929591 / 3596080349051904000 : ℝ) := by
  apply lower_of_taylor (t := (2183317 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_387 : (2854149521193271 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 387 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (39140350466739563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_387_0
  · norm_num [gridPoint]

theorem exp_7_388_0 : (8734004440606841 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (45139234023539412029379 / 451113505354683392000 : ℝ) := by
  apply lower_of_taylor (t := (273157 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_388 : (5095131606129323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 388 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (8734004440606841 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_388_0
  · norm_num [gridPoint]

theorem exp_7_389_0 : (48718335668403 / 1562500000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (18140584730334566631983 / 181087928746439270400 : ℝ) := by
  apply lower_of_taylor (t := (2187199 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_389 : (90946171067383 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 389 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (48718335668403 / 1562500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_389_0
  · norm_num [gridPoint]

theorem exp_7_390_0 : (13912078880568443 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (91128786113827421383487 / 908657986331464704000 : ℝ) := by
  apply lower_of_taylor (t := (1094573 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_390 : (50724064555221 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 390 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (13912078880568443 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_390_0
  · norm_num [gridPoint]

theorem exp_7_391_0 : (1551681236546141 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4577802896581362520587 / 45594101925358592000 : ℝ) := by
  apply lower_of_taylor (t := (273887 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_391 : (3620799675441777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 391 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1551681236546141 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_391_0
  · norm_num [gridPoint]

theorem exp_7_392_0 : (5537504328762909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4599237080157849096347 / 45755590012965888000 : ℝ) := by
  apply lower_of_taylor (t := (43861 / 20000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_392 : (3230398326039493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 392 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5537504328762909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_392_0
  · norm_num [gridPoint]

theorem exp_7_393_0 : (790381949848029 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (92414839626501277611353 / 918347271587902464000 : ℝ) := by
  apply lower_of_taylor (t := (2195007 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_393 : (2881768094585067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 393 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (790381949848029 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_393_0
  · norm_num [gridPoint]

theorem exp_7_394_0 : (17625100602688011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (18569270899948959829449 / 184317690498585190400 : ℝ) := by
  apply lower_of_taylor (t := (274621 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_394 : (321309542749833 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 394 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (17625100602688011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_394_0
  · norm_num [gridPoint]

theorem exp_7_395_0 : (15719476252459579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (46639644360486104108441 / 462417671487194112000 : ℝ) := by
  apply lower_of_taylor (t := (2198933 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_395 : (573139165648149 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 395 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (15719476252459579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_395_0
  · norm_num [gridPoint]

theorem exp_7_396_0 : (876146428336051 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (9371364478826816650253 / 92808794303228928000 : ℝ) := by
  apply lower_of_taylor (t := (1100451 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_396 : (2044460310946289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 396 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (876146428336051 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_396_0
  · norm_num [gridPoint]

theorem exp_7_397_0 : (12499932640553197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (18829885039943467137291 / 186269250533325824000 : ℝ) := by
  apply lower_of_taylor (t := (1101437 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_397 : (1823012637114741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 397 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (12499932640553197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_397_0
  · norm_num [gridPoint]

theorem exp_7_398_0 : (11144775053399027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (94586632453404377450923 / 934610271877407744000 : ℝ) := by
  apply lower_of_taylor (t := (44097 / 20000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_398 : (406343504888847 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 398 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (11144775053399027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_398_0
  · norm_num [gridPoint]

theorem exp_7_399_0 : (9935456553787741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (475126345237069767391 / 4689400003323125760 : ℝ) := by
  apply lower_of_taylor (t := (2206829 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_399 : (1449004836577899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 399 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (9935456553787741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_399_0
  · norm_num [gridPoint]

theorem exp_7_400_0 : (8856405304304381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11933167184978840681319 / 117644429878535168000 : ℝ) := by
  apply lower_of_taylor (t := (552203 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_400 : (161454257929129 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 400 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (8856405304304381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_400_0
  · norm_num [gridPoint]

theorem exp_7_401_0 : (7893698161487299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (19181368049747871010049 / 188887317393675264000 : ℝ) := by
  apply lower_of_taylor (t := (2210799 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_401 : (1151231123860191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 401 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (7893698161487299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_401_0
  · norm_num [gridPoint]

theorem exp_7_402_0 : (1406977539284961 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (19269955970444900791909 / 189544688896982016000 : ℝ) := by
  apply lower_of_taylor (t := (2212789 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_402 : (1025980662460423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 402 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1406977539284961 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_402_0
  · norm_num [gridPoint]

theorem exp_7_403_0 : (3134423593409203 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (48397079394185416930359 / 475508005788941312000 : ℝ) := by
  apply lower_of_taylor (t := (2214783 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_403 : (182851987612077 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 403 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3134423593409203 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_403_0
  · norm_num [gridPoint]

theorem exp_7_404_0 : (5585631733201437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (9723997955526300643603 / 95431428824729395200 : ℝ) := by
  apply lower_of_taylor (t := (2216781 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_404 : (407309284326059 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 404 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5585631733201437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_404_0
  · norm_num [gridPoint]

theorem exp_7_405_0 : (4976353839690259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (97687244650985683367747 / 957618274493144064000 : ℝ) := by
  apply lower_of_taylor (t := (1109391 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_405 : (725760385866233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 405 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (4976353839690259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_405_0
  · norm_num [gridPoint]

theorem exp_7_406_0 : (1108267992126707 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (633135203700796944117 / 6199535292357632000 : ℝ) := by
  apply lower_of_taylor (t := (2220787 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_406 : (646527181563229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 406 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1108267992126707 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_406_0
  · norm_num [gridPoint]

theorem exp_7_407_0 : (987172682352069 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (159009867453647091983 / 1555231251151872000 : ℝ) := by
  apply lower_of_taylor (t := (444559 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_407 : (575884151280557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 407 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (987172682352069 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_407_0
  · norm_num [gridPoint]

theorem exp_7_408_0 : (703374300354377 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (24759432722995839280997 / 241891122672331776000 : ℝ) := by
  apply lower_of_taylor (t := (2224807 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_408 : (512906859196891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 408 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (703374300354377 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_408_0
  · norm_num [gridPoint]

theorem exp_7_409_0 : (3131952409929043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (19898159656774933660797 / 194178263048186470400 : ℝ) := by
  apply lower_of_taylor (t := (2226823 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_409 : (228384783595519 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 409 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3131952409929043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_409_0
  · norm_num [gridPoint]

theorem exp_7_410_0 : (1394438341394129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (99945322495019792251717 / 974223849368976384000 : ℝ) := by
  apply lower_of_taylor (t := (1114421 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_410 : (101683696670157 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 410 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1394438341394129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_410_0
  · norm_num [gridPoint]

theorem exp_7_411_0 : (155195533004331 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2008026120470067812989 / 19551241861469184000 : ℝ) := by
  apply lower_of_taylor (t := (446173 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_411 : (905359816013 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 411 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (155195533004331 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_411_0
  · norm_num [gridPoint]

theorem exp_7_412_0 : (2210675740701769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2017175027348202503589 / 19618120927087616000 : ℝ) := by
  apply lower_of_taylor (t := (2232891 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_412 : (322408922331917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 412 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2210675740701769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_412_0
  · norm_num [gridPoint]

theorem exp_7_413_0 : (983959172562969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (101317661024824657523983 / 984255709211741184000 : ℝ) := by
  apply lower_of_taylor (t := (2234921 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_413 : (287004747556443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 413 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (983959172562969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_413_0
  · norm_num [gridPoint]

theorem exp_7_414_0 : (1751642643276369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (20355607498766329873063 / 197522216329108070400 : ℝ) := by
  apply lower_of_taylor (t := (447391 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_414 : (2554627105783 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 414 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1751642643276369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_414_0
  · norm_num [gridPoint]

theorem exp_7_415_0 : (389745026186607 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6389992704532235149107 / 61935760228486144000 : ℝ) := by
  apply lower_of_taylor (t := (139937 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_415 : (113682229884297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 415 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (389745026186607 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_415_0
  · norm_num [gridPoint]

theorem sum_7_384_2 : (15183991765508201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 384 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_384) (by simpa only [blockSum_one] using cell_7_385) (by norm_num)

theorem sum_7_386_2 : (12102821086125637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 386 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_386) (by simpa only [blockSum_one] using cell_7_387) (by norm_num)

theorem sum_7_384_4 : (13643406425816919 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 384 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_384_2 sum_7_386_2 (by norm_num)

theorem sum_7_388_2 : (9642440159498473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 388 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_388) (by simpa only [blockSum_one] using cell_7_389) (by norm_num)

theorem sum_7_390_2 : (7678724839859457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 390 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_390) (by simpa only [blockSum_one] using cell_7_391) (by norm_num)

theorem sum_7_388_4 : (1732116499935793 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 388 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_388_2 sum_7_390_2 (by norm_num)

theorem sum_7_384_8 : (5575997231373971 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 384 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_384_4 sum_7_388_4 (by norm_num)

theorem sum_7_392_2 : (76402080257807 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 392 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_392) (by simpa only [blockSum_one] using cell_7_393) (by norm_num)

theorem sum_7_394_2 : (243151650229563 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 394 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_394) (by simpa only [blockSum_one] using cell_7_395) (by norm_num)

theorem sum_7_392_4 : (548759971260791 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 392 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_392_2 sum_7_394_2 (by norm_num)

theorem sum_7_396_2 : (386747294806103 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 396 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_396) (by simpa only [blockSum_one] using cell_7_397) (by norm_num)

theorem sum_7_398_2 : (3074378856133287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 398 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_398) (by simpa only [blockSum_one] using cell_7_399) (by norm_num)

theorem sum_7_396_4 : (6941851804194317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 396 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_396_2 sum_7_398_2 (by norm_num)

theorem sum_7_392_8 : (17917051229410137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 392 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_392_4 sum_7_396_4 (by norm_num)

theorem sum_7_384_16 : (12505005816080381 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 384 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_384_8 sum_7_392_8 (by norm_num)

theorem sum_7_400_2 : (2442865187293223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 400 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_400) (by simpa only [blockSum_one] using cell_7_401) (by norm_num)

theorem sum_7_402_2 : (242530075065101 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 402 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_402) (by simpa only [blockSum_one] using cell_7_403) (by norm_num)

theorem sum_7_400_4 : (4383105787814031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 400 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_400_2 sum_7_402_2 (by norm_num)

theorem sum_7_404_2 : (1540378954518351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 404 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_404) (by simpa only [blockSum_one] using cell_7_405) (by norm_num)

theorem sum_7_406_2 : (611205666421893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 406 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_406) (by simpa only [blockSum_one] using cell_7_407) (by norm_num)

theorem sum_7_404_4 : (2762790287362137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 404 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_404_2 sum_7_406_2 (by norm_num)

theorem sum_7_400_8 : (893237009397021 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 400 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_400_4 sum_7_404_4 (by norm_num)

theorem sum_7_408_2 : (969676426387929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 408 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_408) (by simpa only [blockSum_one] using cell_7_409) (by norm_num)

theorem sum_7_410_2 : (192219678271457 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 410 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_410) (by simpa only [blockSum_one] using cell_7_411) (by norm_num)

theorem sum_7_408_4 : (1738555139473757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 408 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_408_2 sum_7_410_2 (by norm_num)

theorem sum_7_412_2 : (15235341747209 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 412 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_412) (by simpa only [blockSum_one] using cell_7_413) (by norm_num)

theorem sum_7_414_2 : (241413585173447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 414 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_414) (by simpa only [blockSum_one] using cell_7_415) (by norm_num)

theorem sum_7_412_4 : (546120420117627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 412 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_412_2 sum_7_414_2 (by norm_num)

theorem sum_7_408_8 : (2830795979709011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 408 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_408_4 sum_7_412_4 (by norm_num)

theorem sum_7_400_16 : (9976692054885179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 400 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_400_8 sum_7_408_8 (by norm_num)

theorem sum_7_384_32 : (18125430283821771 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 384 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_384_16 sum_7_400_16 (by norm_num)

#print axioms sum_7_384_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
