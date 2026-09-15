import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_32_0 : (8639967552364299467770957 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (120363470817858143987 / 1516879987012608000 : ℝ) := by
  apply lower_of_taylor (t := (929387 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_32 : (504027357111402035592129 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 32 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (8639967552364299467770957 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_32_0
  · norm_num [gridPoint]

theorem exp_7_33_0 : (37891384264858703160746081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (9711435266367754315613 / 122530422771631104000 : ℝ) := by
  apply lower_of_taylor (t := (928719 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_33 : (110522951345361883738909 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 33 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (37891384264858703160746081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_33_0
  · norm_num [gridPoint]

theorem exp_7_34_0 : (20724608081774546524330617 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (63189099398244369987 / 798168749410918400 : ℝ) := by
  apply lower_of_taylor (t := (232017 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_34 : (3022514082176146803746663 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 34 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (20724608081774546524330617 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_34_0
  · norm_num [gridPoint]

theorem exp_7_35_0 : (22619546547715918596753911 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (159317832009575520941 / 2014638695519232000 : ℝ) := by
  apply lower_of_taylor (t := (463717 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_35 : (6597750626033184990383637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 35 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (22619546547715918596753911 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_35_0
  · norm_num [gridPoint]

theorem exp_7_36_0 : (49265981501019643226962117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (199232465960996616979 / 2522095033242624000 : ℝ) := by
  apply lower_of_taylor (t := (1853633 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_36 : (3592519633459607206445789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 36 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (49265981501019643226962117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_36_0
  · norm_num [gridPoint]

theorem exp_7_37_0 : (10706801856480209934852719 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (401842641807239387283 / 5092304551140352000 : ℝ) := by
  apply lower_of_taylor (t := (185243 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_37 : (243984253364634324965023 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 37 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (10706801856480209934852719 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_37_0
  · norm_num [gridPoint]

theorem exp_7_38_0 : (58046390988286858821605857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (10131036324071805479983 / 128516185471325184000 : ℝ) := by
  apply lower_of_taylor (t := (1851259 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_38 : (8465589963840562568492443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 38 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (58046390988286858821605857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_38_0
  · norm_num [gridPoint]

theorem exp_7_39_0 : (12561071365948380614687117 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (510826831640347746247 / 6486523337029017600 : ℝ) := by
  apply lower_of_taylor (t := (46253 / 25000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_39 : (915964609342511258671193 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 39 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (12561071365948380614687117 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_39_0
  · norm_num [gridPoint]

theorem exp_7_40_0 : (33906043183728000835358377 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2575642367367773674803 / 32737614396568576000 : ℝ) := by
  apply lower_of_taylor (t := (462253 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_40 : (9889836525672474806160333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 40 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (33906043183728000835358377 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_40_0
  · norm_num [gridPoint]

theorem exp_7_41_0 : (73066647684373362264028367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2077827466429777297013 / 26435231601681408000 : ℝ) := by
  apply lower_of_taylor (t := (923967 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_41 : (2131234237984313802194243 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 41 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (73066647684373362264028367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_41_0
  · norm_num [gridPoint]

theorem exp_7_42_0 : (39283971409700913780769393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2095248543784998392953 / 26681513601395712000 : ℝ) := by
  apply lower_of_taylor (t := (923443 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_42 : (2864622489388454036058429 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 42 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (39283971409700913780769393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_42_0
  · norm_num [gridPoint]

theorem exp_7_43_0 : (84313660189161475539453073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5281944063942036410289 / 67322343790994432000 : ℝ) := by
  apply lower_of_taylor (t := (461467 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_43 : (3074113925773865498050049 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 43 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (84313660189161475539453073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_43_0
  · norm_num [gridPoint]

theorem exp_7_44_0 : (45150117332938785774005853 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1065207605711079073477 / 13588751673343795200 : ℝ) := by
  apply lower_of_taylor (t := (1844879 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_44 : (6584774240952875141661701 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 44 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (45150117332938785774005853 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_44_0
  · norm_num [gridPoint]

theorem exp_7_45_0 : (96522815911308840724218389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (10740809004689807389607 / 137136055461325824000 : ℝ) := by
  apply lower_of_taylor (t := (1843919 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_45 : (7038530455970060982146593 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 45 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (96522815911308840724218389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_45_0
  · norm_num [gridPoint]

theorem exp_7_46_0 : (102975245489909778992698391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2166017893741156893471 / 27678060753130496000 : ℝ) := by
  apply lower_of_taylor (t := (1842987 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_46 : (750904741794634092496463 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 46 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (102975245489909778992698391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_46_0
  · norm_num [gridPoint]

theorem exp_7_47_0 : (54825021600134326132306861 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (272997998681084591257 / 3491256541160448000 : ℝ) := by
  apply lower_of_taylor (t := (1842083 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_47 : (15991559327748555729005803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 47 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (54825021600134326132306861 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_47_0
  · norm_num [gridPoint]

theorem exp_7_48_0 : (58269201486684056659981983 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1376287867298408327581 / 17614491137952768000 : ℝ) := by
  apply lower_of_taylor (t := (920603 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_48 : (8498085047289424208706083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 48 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (58269201486684056659981983 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_48_0
  · norm_num [gridPoint]

theorem exp_7_49_0 : (61815099295301886139371227 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (444049637608883802429 / 5687492245490606080 : ℝ) := by
  apply lower_of_taylor (t := (1840357 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_49 : (2253806288808343330035639 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 49 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (61815099295301886139371227 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_49_0
  · norm_num [gridPoint]

theorem exp_7_50_0 : (130913999375060452834472809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11192736450832530652777 / 143464392747346944000 : ℝ) := by
  apply lower_of_taylor (t := (919767 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_50 : (19092732904951443503130701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 50 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (130913999375060452834472809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_50_0
  · norm_num [gridPoint]

theorem exp_7_51_0 : (69188547953814383264319069 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1128479196830323507907 / 14474718893386752000 : ℝ) := by
  apply lower_of_taylor (t := (1838737 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_51 : (10090582156756394165488221 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 51 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (69188547953814383264319069 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_51_0
  · norm_num [gridPoint]

theorem exp_7_52_0 : (146005535716515328536404113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1137740999071887002187 / 14603569469682688000 : ℝ) := by
  apply lower_of_taylor (t := (918983 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_52 : (21293709682593586127230139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 52 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (146005535716515328536404113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_52_0
  · norm_num [gridPoint]

theorem exp_7_53_0 : (38446042196482905140136863 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11470593016164097163443 / 147329910036225024000 : ℝ) := by
  apply lower_of_taylor (t := (1837221 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_53 : (4485631901333710952686187 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 53 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (38446042196482905140136863 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_53_0
  · norm_num [gridPoint]

theorem exp_7_54_0 : (20212087828574236357756569 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2312868708544715637211 / 29725966990412390400 : ℝ) := by
  apply lower_of_taylor (t := (1836501 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_54 : (11791068830058334398984693 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 54 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (20212087828574236357756569 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_54_0
  · norm_num [gridPoint]

theorem exp_7_55_0 : (169725766568444266487757873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2914666017120493692993 / 37483867361084416000 : ℝ) := by
  apply lower_of_taylor (t := (917903 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_55 : (24753110772328714497865953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 55 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (169725766568444266487757873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_55_0
  · norm_num [gridPoint]

theorem exp_7_56_0 : (177852984785965858325983869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (587677854576197430173 / 7562340675652608000 : ℝ) := by
  apply lower_of_taylor (t := (367027 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_56 : (12969199440383649030331583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 56 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (177852984785965858325983869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_56_0
  · norm_num [gridPoint]

theorem exp_7_57_0 : (93029528794893771622714133 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2369805021986832272557 / 30512773431641088000 : ℝ) := by
  apply lower_of_taylor (t := (1834489 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_57 : (27135187283763721956405027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 57 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (93029528794893771622714133 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_57_0
  · norm_num [gridPoint]

theorem exp_7_58_0 : (7772954011841483075670923 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11945070621797274732213 / 153886630379797504000 : ℝ) := by
  apply lower_of_taylor (t := (916933 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_58 : (1133621580113701919420749 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 58 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (7772954011841483075670923 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_58_0
  · norm_num [gridPoint]

theorem exp_7_59_0 : (20262648902207365737978189 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1204169612519795039401 / 15521510317782835200 : ℝ) := by
  apply lower_of_taylor (t := (1833267 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_59 : (5910282250690336746174099 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 59 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (20262648902207365737978189 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_59_0
  · norm_num [gridPoint]

theorem exp_7_60_0 : (105472731317329913130383609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6069452059110425015221 / 78274642776148992000 : ℝ) := by
  apply lower_of_taylor (t := (1832691 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_60 : (30764665313266960716245603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 60 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (105472731317329913130383609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_60_0
  · norm_num [gridPoint]

theorem exp_7_61_0 : (219258730035032006864077983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (489467883958025412951 / 6315567100128256000 : ℝ) := by
  apply lower_of_taylor (t := (1832137 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_61 : (15988543584419799789597233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 61 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (219258730035032006864077983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_61_0
  · norm_num [gridPoint]

theorem exp_7_62_0 : (5688595797881841535815469 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (493403102618878718251 / 6369391161222144000 : ℝ) := by
  apply lower_of_taylor (t := (915803 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_62 : (16592700657173241770346753 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 62 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5688595797881841535815469 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_62_0
  · norm_num [gridPoint]

theorem exp_7_63_0 : (117889003041157596770722819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (388564000495922175319 / 5018315316698112000 : ℝ) := by
  apply lower_of_taylor (t := (915549 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_63 : (17193144035324763493098913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 63 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (117889003041157596770722819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_63_0
  · norm_num [gridPoint]

theorem sum_7_32_2 : (528321056919105727143337 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 32 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_32) (by simpa only [blockSum_one] using cell_7_33) (by norm_num)

theorem sum_7_34_2 : (12642778790385478597876963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 34 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_34) (by simpa only [blockSum_one] using cell_7_35) (by norm_num)

theorem sum_7_32_4 : (23209199928767593140743703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 32 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_32_2 sum_7_34_2 (by norm_num)

theorem sum_7_36_2 : (7496267687293756405886157 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 36 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_36) (by simpa only [blockSum_one] using cell_7_37) (by norm_num)

theorem sum_7_38_2 : (17625236057265675155204373 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 38 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_38) (by simpa only [blockSum_one] using cell_7_39) (by norm_num)

theorem sum_7_36_4 : (32617771431853187966976687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 36 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_36_2 sum_7_38_2 (by norm_num)

theorem sum_7_32_8 : (5582697136062078110772039 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 32 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_32_4 sum_7_36_4 (by norm_num)

theorem sum_7_40_2 : (5136501928898510954282887 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 40 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_40) (by simpa only [blockSum_one] using cell_7_41) (by norm_num)

theorem sum_7_42_2 : (2969368207581159767054239 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 42 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_42) (by simpa only [blockSum_one] using cell_7_43) (by norm_num)

theorem sum_7_40_4 : (2215047668812166097678273 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 40 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_40_2 sum_7_42_2 (by norm_num)

theorem sum_7_44_2 : (6811652348461468061904147 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 44 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_44) (by simpa only [blockSum_one] using cell_7_45) (by norm_num)

theorem sum_7_46_2 : (31009654163641237578935063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 46 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_46) (by simpa only [blockSum_one] using cell_7_47) (by norm_num)

theorem sum_7_44_4 : (58256263557487109826551651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 44 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_44_2 sum_7_46_2 (by norm_num)

theorem sum_7_40_8 : (102557216933730431780117111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 40 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_40_4 sum_7_44_4 (by norm_num)

theorem sum_7_32_16 : (158384188294351212887837501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 32 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_32_8 sum_7_40_8 (by norm_num)

theorem sum_7_48_2 : (17513310202522797528848639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 48 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_48) (by simpa only [blockSum_one] using cell_7_49) (by norm_num)

theorem sum_7_50_2 : (39273897218464231834107143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 50 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_50) (by simpa only [blockSum_one] using cell_7_51) (by norm_num)

theorem sum_7_48_4 : (74300517623509826891804421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 48 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_48_2 sum_7_50_2 (by norm_num)

theorem sum_7_52_2 : (21860934594631070445330537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 52 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_52) (by simpa only [blockSum_one] using cell_7_53) (by norm_num)

theorem sum_7_54_2 : (48335248432445383295835339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 54 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_54) (by simpa only [blockSum_one] using cell_7_55) (by norm_num)

theorem sum_7_52_4 : (92057117621707524186496413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 52 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_52_2 sum_7_54_2 (by norm_num)

theorem sum_7_48_8 : (83178817622608675539150417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 48 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_48_4 sum_7_52_4 (by norm_num)

theorem sum_7_56_2 : (53073586164531020017068193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 56 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_56) (by simpa only [blockSum_one] using cell_7_57) (by norm_num)

theorem sum_7_58_2 : (2894597537814711585819461 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 58 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_58) (by simpa only [blockSum_one] using cell_7_59) (by norm_num)

theorem sum_7_56_4 : (110965536920825251733457413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 56 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_56_2 sum_7_58_2 (by norm_num)

theorem sum_7_60_2 : (62741752482106560295440069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 60 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_60) (by simpa only [blockSum_one] using cell_7_61) (by norm_num)

theorem sum_7_62_2 : (16892922346249002631722833 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 62 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_62) (by simpa only [blockSum_one] using cell_7_63) (by norm_num)

theorem sum_7_60_4 : (130313441867102570822331401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 60 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_60_2 sum_7_62_2 (by norm_num)

theorem sum_7_56_8 : (120639489393963911277894407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 56 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_56_4 sum_7_60_4 (by norm_num)

theorem sum_7_48_16 : (25477288377071573352130603 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 48 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_48_8 sum_7_56_8 (by norm_num)

theorem sum_7_32_32 : (566020802327496386521927149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 32 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_32_16 sum_7_48_16 (by norm_num)

#print axioms sum_7_32_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
