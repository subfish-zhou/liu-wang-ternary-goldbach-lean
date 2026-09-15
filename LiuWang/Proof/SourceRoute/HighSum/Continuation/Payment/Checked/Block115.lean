import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_96_0 : (71753358072161789954946653 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6470727337763046631 / 84025172960256000 : ℝ) := by
  apply lower_of_taylor (t := (912551 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_96 : (2092927734611872272549149 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 96 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (71753358072161789954946653 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_96_0
  · norm_num [gridPoint]

theorem exp_7_97_0 : (356207125108557351786627561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (104309161678804548231 / 1354373326736384000 : ℝ) := by
  apply lower_of_taylor (t := (365041 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_97 : (10389977437101986724710651 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 97 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (356207125108557351786627561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_97_0
  · norm_num [gridPoint]

theorem exp_7_98_0 : (70661098808133883329554961 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (16289113739616422207473 / 211479011923282944000 : ℝ) := by
  apply lower_of_taylor (t := (1825321 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_98 : (12881677024175208012942379 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 98 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (70661098808133883329554961 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_98_0
  · norm_num [gridPoint]

theorem exp_7_99_0 : (350074487524896271949072487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (328219746678843380443 / 4260717355577303040 : ℝ) := by
  apply lower_of_taylor (t := (456363 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_99 : (51055492300725643599041389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 99 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (350074487524896271949072487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_99_0
  · norm_num [gridPoint]

theorem exp_7_100_0 : (173263709614723219818798191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8266771670638303551051 / 107299216605443072000 : ℝ) := by
  apply lower_of_taylor (t := (1825597 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_100 : (1263454537171972416707957 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 100 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (173263709614723219818798191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_100_0
  · norm_num [gridPoint]

theorem exp_7_101_0 : (171339124148799542246990717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3331356851940879625919 / 43233341643869184000 : ℝ) := by
  apply lower_of_taylor (t := (1825757 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_101 : (24988405740849630115478601 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 101 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (171339124148799542246990717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_101_0
  · norm_num [gridPoint]

theorem exp_7_102_0 : (42317687623377155524348421 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3356142517462040757379 / 43548138560848896000 : ℝ) := by
  apply lower_of_taylor (t := (182593 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_102 : (12343375205176545234994613 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 102 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (42317687623377155524348421 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_102_0
  · norm_num [gridPoint]

theorem exp_7_103_0 : (1670660961426410277400333 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4226332705544671439067 / 54830096741395456000 : ℝ) := by
  apply lower_of_taylor (t := (1826117 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_103 : (48730439316668547587406353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 103 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1670660961426410277400333 / 5000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_103_0
  · norm_num [gridPoint]

theorem exp_7_104_0 : (329465747988937556261108893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (851532073119725285999 / 11045289535167897600 : ℝ) := by
  apply lower_of_taylor (t := (913159 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_104 : (48049876695472570827291527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 104 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (329465747988937556261108893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_104_0
  · norm_num [gridPoint]

theorem exp_7_105_0 : (324557927706361855809485089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (17156647006042325360297 / 222496904017572864000 : ℝ) := by
  apply lower_of_taylor (t := (456633 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_105 : (47334111366722160420214963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 105 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (324557927706361855809485089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_105_0
  · norm_num [gridPoint]

theorem exp_7_106_0 : (159712374607738174670598019 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3456669990241361271897 / 44818745381645312000 : ℝ) := by
  apply lower_of_taylor (t := (1826759 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_106 : (11646369847982829336746313 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 106 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (159712374607738174670598019 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_106_0
  · norm_num [gridPoint]

theorem exp_7_107_0 : (39260301822009963691527619 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1741075279597261039981 / 22569625937531904000 : ℝ) := by
  apply lower_of_taylor (t := (1827 / 1000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_107 : (45806343708614156231407169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 107 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (39260301822009963691527619 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_107_0
  · norm_num [gridPoint]

theorem exp_7_108_0 : (308547238363850139947014299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8769429019212199581769 / 113652250709425152000 : ℝ) := by
  apply lower_of_taylor (t := (913627 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_108 : (22499541831901419726546391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 108 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (308547238363850139947014299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_108_0
  · norm_num [gridPoint]

theorem exp_7_109_0 : (151417789179594670814126691 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3533533635329366866587 / 45783690607764070400 : ℝ) := by
  apply lower_of_taylor (t := (1827521 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_109 : (44166084905584037751412711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 109 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (151417789179594670814126691 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_109_0
  · norm_num [gridPoint]

theorem exp_7_110_0 : (74240942247365436264350171 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (17797185708724577590267 / 230538114235229184000 : ℝ) := by
  apply lower_of_taylor (t := (9139 / 5000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_110 : (8661945935239100767648893 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 110 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (74240942247365436264350171 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_110_0
  · norm_num [gridPoint]

theorem exp_7_111_0 : (145474028894085990718676513 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (89637065663711453089 / 1160817425040384000 : ℝ) := by
  apply lower_of_taylor (t := (457023 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_111 : (4243238754511833989435271 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 111 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (145474028894085990718676513 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_111_0
  · norm_num [gridPoint]

theorem exp_7_112_0 : (284804545099561079345491981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (90291764733923175489 / 1168972826786816000 : ℝ) := by
  apply lower_of_taylor (t := (1828397 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_112 : (41536406615486963585560999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 112 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (284804545099561079345491981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_112_0
  · norm_num [gridPoint]

theorem exp_7_113_0 : (34818640902787950046167547 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (18190007648936272712533 / 235431355283088384000 : ℝ) := by
  apply lower_of_taylor (t := (365743 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_113 : (20312052616031867327323257 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 113 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (34818640902787950046167547 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_113_0
  · norm_num [gridPoint]

theorem exp_7_114_0 : (272197443151745568124202877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3664475947456373028853 / 47414770957050470400 : ℝ) := by
  apply lower_of_taylor (t := (457261 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_114 : (3969776421403123694805147 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 114 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (272197443151745568124202877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_114_0
  · norm_num [gridPoint]

theorem exp_7_115_0 : (132882412523351258738946861 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (9227735854953037037631 / 119361031931927552000 : ℝ) := by
  apply lower_of_taylor (t := (914693 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_115 : (38759619630981100942562113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 115 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (132882412523351258738946861 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_115_0
  · norm_num [gridPoint]

theorem exp_7_116_0 : (129633126257238746993053719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1858928606489356118779 / 24037598251889664000 : ℝ) := by
  apply lower_of_taylor (t := (91487 / 50000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_116 : (7562371227151776934936183 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 116 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (129633126257238746993053719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_116_0
  · norm_num [gridPoint]

theorem exp_7_117_0 : (252716310776672296472277687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3744765060065797632823 / 48407122150075392000 : ℝ) := by
  apply lower_of_taylor (t := (915053 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_117 : (36856600863290814550549701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 117 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (252716310776672296472277687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_117_0
  · norm_num [gridPoint]

theorem exp_7_118_0 : (9845166109949445976728281 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (18859091914297016686503 / 243700948558296064000 : ℝ) := by
  apply lower_of_taylor (t := (1830483 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_118 : (17947958950098512708209899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 118 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (9845166109949445976728281 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_118_0
  · norm_num [gridPoint]

theorem exp_7_119_0 : (47903693007636295171766441 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (949754420244115421861 / 12268599797132697600 : ℝ) := by
  apply lower_of_taylor (t := (1830873 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_119 : (17465901662955125960795761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 119 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (47903693007636295171766441 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_119_0
  · norm_num [gridPoint]

theorem exp_7_120_0 : (232897437840126813667835987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4782954317542381274633 / 61762188225862656000 : ℝ) := by
  apply lower_of_taylor (t := (915637 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_120 : (33966180822187713483185509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 120 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (232897437840126813667835987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_120_0
  · norm_num [gridPoint]

theorem exp_7_121_0 : (9051149547376253449664199 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3853856201648665670541 / 49746243888137216000 : ℝ) := by
  apply lower_of_taylor (t := (915843 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_121 : (33000897844342393620111103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 121 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (9051149547376253449664199 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_121_0
  · norm_num [gridPoint]

theorem exp_7_122_0 : (219674489965992880691733727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3881496423437675976401 / 50083879110872064000 : ℝ) := by
  apply lower_of_taylor (t := (183211 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_122 : (32037722344239559363539939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 122 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (219674489965992880691733727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_122_0
  · norm_num [gridPoint]

theorem exp_7_123_0 : (53274062542492954383805301 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (9773211547544670684349 / 126056640622236672000 : ℝ) := by
  apply lower_of_taylor (t := (366509 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_123 : (31078340032113214037446293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 123 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (53274062542492954383805301 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_123_0
  · norm_num [gridPoint]

theorem exp_7_124_0 : (206554998683808807014903983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (393722128800617489901 / 5076257530220503040 : ℝ) := by
  apply lower_of_taylor (t := (57281 / 31250 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_124 : (30124352161559936384003701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 124 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (206554998683808807014903983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_124_0
  · norm_num [gridPoint]

theorem exp_7_125_0 : (200061124073186578444656849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (19826534650097640943327 / 255518181354015744000 : ℝ) := by
  apply lower_of_taylor (t := (1833449 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_125 : (29177273819665849607501897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 125 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (200061124073186578444656849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_125_0
  · norm_num [gridPoint]

theorem exp_7_126_0 : (6050762990101120040519313 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3993542044674860479159 / 51445839154689024000 : ℝ) := by
  apply lower_of_taylor (t := (916959 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_126 : (28238532702115045909101101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 126 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (6050762990101120040519313 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_126_0
  · norm_num [gridPoint]

theorem exp_7_127_0 : (182865291420436393268249 / 976562500000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2027181013905798441 / 26103419331584000 : ℝ) := by
  apply lower_of_taylor (t := (1834397 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_127 : (13654734175655405921733421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 127 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (182865291420436393268249 / 976562500000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_127_0
  · norm_num [gridPoint]

theorem sum_7_96_2 : (5213654027540337021864099 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 96 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_96) (by simpa only [blockSum_one] using cell_7_97) (by norm_num)

theorem sum_7_98_2 : (20516440079485295130162181 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 98 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_98) (by simpa only [blockSum_one] using cell_7_99) (by norm_num)

theorem sum_7_96_4 : (41371056189646643217618577 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 96 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_96_2 sum_7_98_2 (by norm_num)

theorem sum_7_100_2 : (50257496484289078449637741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 100 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_100) (by simpa only [blockSum_one] using cell_7_101) (by norm_num)

theorem sum_7_102_2 : (19620788027474945705476961 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 102 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_102) (by simpa only [blockSum_one] using cell_7_103) (by norm_num)

theorem sum_7_100_4 : (198618933105952885426660287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 100 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_100_2 sum_7_102_2 (by norm_num)

theorem sum_7_96_8 : (101368553513546525378688293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 96 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_96_4 sum_7_100_4 (by norm_num)

theorem sum_7_104_2 : (9538398806219473124750649 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 104 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_104) (by simpa only [blockSum_one] using cell_7_105) (by norm_num)

theorem sum_7_106_2 : (92391823100545473578392421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 106 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_106) (by simpa only [blockSum_one] using cell_7_107) (by norm_num)

theorem sum_7_104_4 : (187775811162740204825898911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 104 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_104_2 sum_7_106_2 (by norm_num)

theorem sum_7_108_2 : (89165168569386877204505493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 108 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_108) (by simpa only [blockSum_one] using cell_7_109) (by norm_num)

theorem sum_7_110_2 : (3429684688852553749303887 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 110 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_110) (by simpa only [blockSum_one] using cell_7_111) (by norm_num)

theorem sum_7_108_4 : (43726821447675180234275667 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 108 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_108_2 sum_7_110_2 (by norm_num)

theorem sum_7_104_8 : (362683096953440925763001579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 104 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_104_4 sum_7_108_4 (by norm_num)

theorem sum_7_96_16 : (768157311007627027277754751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 96 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_96_8 sum_7_104_8 (by norm_num)

theorem sum_7_112_2 : (82160511847550698240207513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 112 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_112) (by simpa only [blockSum_one] using cell_7_113) (by norm_num)

theorem sum_7_114_2 : (78457383845012337890613583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 114 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_114) (by simpa only [blockSum_one] using cell_7_115) (by norm_num)

theorem sum_7_112_4 : (20077236961570379516352637 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 112 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_112_2 sum_7_114_2 (by norm_num)

theorem sum_7_116_2 : (9333557124881212403153827 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 116 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_116) (by simpa only [blockSum_one] using cell_7_117) (by norm_num)

theorem sum_7_118_2 : (1770693030652681933450283 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 118 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_118) (by simpa only [blockSum_one] using cell_7_119) (by norm_num)

theorem sum_7_116_4 : (9093511139072311035202621 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 116 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_116_2 sum_7_118_2 (by norm_num)

theorem sum_7_112_8 : (38264259239715001586757879 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 112 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_112_4 sum_7_116_4 (by norm_num)

theorem sum_7_120_2 : (16741769666632526775824153 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 120 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_120) (by simpa only [blockSum_one] using cell_7_121) (by norm_num)

theorem sum_7_122_2 : (7889507797044096675123279 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 122 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_122) (by simpa only [blockSum_one] using cell_7_123) (by norm_num)

theorem sum_7_120_4 : (32520785260720720126070711 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 120 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_120_2 sum_7_122_2 (by norm_num)

theorem sum_7_124_2 : (29650812990612892995752799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 124 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_124) (by simpa only [blockSum_one] using cell_7_125) (by norm_num)

theorem sum_7_126_2 : (55548001053425857752567943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 126 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_126) (by simpa only [blockSum_one] using cell_7_127) (by norm_num)

theorem sum_7_124_4 : (114849627034651643744073541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 124 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_124_2 sum_7_126_2 (by norm_num)

theorem sum_7_120_8 : (48986553615506904849671277 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 120 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_120_4 sum_7_124_4 (by norm_num)

theorem sum_7_112_16 : (551046841995254536942419417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 112 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_112_8 sum_7_120_8 (by norm_num)

theorem sum_7_96_32 : (164900519125360195527521771 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 96 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_96_16 sum_7_112_16 (by norm_num)

#print axioms sum_7_96_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
