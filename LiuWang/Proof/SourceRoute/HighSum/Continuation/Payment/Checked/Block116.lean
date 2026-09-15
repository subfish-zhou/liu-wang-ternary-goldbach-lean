import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_128_0 : (5654957203521204585216871 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (10207819280189494477 / 131385258740736000 : ℝ) := by
  apply lower_of_taylor (t := (1834887 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_128 : (329891647925103021549007 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 128 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5654957203521204585216871 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_128_0
  · norm_num [gridPoint]

theorem exp_7_129_0 : (436865260504559472718951 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4079149220662054720201 / 52479299298073190400 : ℝ) := by
  apply lower_of_taylor (t := (458847 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_129 : (12742642916849984526326871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 129 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (436865260504559472718951 / 2500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_129_0
  · norm_num [gridPoint]

theorem exp_7_130_0 : (21077981123171775661872481 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (20539936110273131892897 / 264130349215550464000 : ℝ) := by
  apply lower_of_taylor (t := (18359 / 10000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_130 : (4918481026401123938899 / 200000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 130 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (21077981123171775661872481 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_130_0
  · norm_num [gridPoint]

theorem exp_7_131_0 : (162598637432472538776958583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2068488597086919360031 / 26586991151717376000 : ℝ) := by
  apply lower_of_taylor (t := (918211 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_131 : (11856838726289215764662377 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 131 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (162598637432472538776958583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_131_0
  · norm_num [gridPoint]

theorem exp_7_132_0 : (78338326632559139698722219 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2083059818318312040551 / 26761518339523584000 : ℝ) := by
  apply lower_of_taylor (t := (918477 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_132 : (22850004640546185626731589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 132 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (78338326632559139698722219 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_132_0
  · norm_num [gridPoint]

theorem exp_7_133_0 : (75431750779551492508021849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (20977075245299573990763 / 269366164849736704000 : ℝ) := by
  apply lower_of_taylor (t := (1837497 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_133 : (22002204150233943347916013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 133 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (75431750779551492508021849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_133_0
  · norm_num [gridPoint]

theorem exp_7_134_0 : (5806568834859743157107653 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4224863931060643207667 / 54224571176135270400 : ℝ) := by
  apply lower_of_taylor (t := (1838049 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_134 : (10585505406929001007919569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 134 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5806568834859743157107653 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_134_0
  · norm_num [gridPoint]

theorem exp_7_135_0 : (139583297108346462343001463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5318083477819677057623 / 68221314122013696000 : ℝ) := by
  apply lower_of_taylor (t := (1838613 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_135 : (4071415772803647925630571 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 135 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (139583297108346462343001463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_135_0
  · norm_num [gridPoint]

theorem exp_7_136_0 : (134124678948511796725282021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (42842241022621424499 / 549306733343744000 : ℝ) := by
  apply lower_of_taylor (t := (919593 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_136 : (1956098418313344604154987 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 136 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (134124678948511796725282021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_136_0
  · norm_num [gridPoint]

theorem exp_7_137_0 : (64395897321341599282240833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (172565455627871118221 / 2211417491457024000 : ℝ) := by
  apply lower_of_taylor (t := (1839769 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_137 : (9391613376722458125008213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 137 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (64395897321341599282240833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_137_0
  · norm_num [gridPoint]

theorem exp_7_138_0 : (12358757001115030556950043 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (21721020735882902497133 / 278206715768822784000 : ℝ) := by
  apply lower_of_taylor (t := (920181 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_138 : (9012116640920512174980631 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 138 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (12358757001115030556950043 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_138_0
  · norm_num [gridPoint]

theorem exp_7_139_0 : (118514447468907823907171311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2187213935659241209029 / 27999195468195635200 : ℝ) := by
  apply lower_of_taylor (t := (460241 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_139 : (17284359974513312732367947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 139 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (118514447468907823907171311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_139_0
  · norm_num [gridPoint]

theorem exp_7_140_0 : (56787202956377007909393083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11012020156848540119681 / 140891451585764352000 : ℝ) := by
  apply lower_of_taylor (t := (1841577 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_140 : (4140973859331667536720987 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 140 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (56787202956377007909393083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_140_0
  · norm_num [gridPoint]

theorem exp_7_141_0 : (27192245327916489944795453 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4435345221056313725323 / 56715912247507968000 : ℝ) := by
  apply lower_of_taylor (t := (1842199 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_141 : (15863063678756657973967353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 141 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (27192245327916489944795453 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_141_0
  · norm_num [gridPoint]

theorem exp_7_142_0 : (6506205490560217828150041 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4466039845886107786863 / 57076385775997952000 : ℝ) := by
  apply lower_of_taylor (t := (1842831 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_142 : (1518202719330068829518099 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 142 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (6506205490560217828150041 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_142_0
  · norm_num [gridPoint]

theorem exp_7_143_0 : (99566039472467657710039233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2810557773028581605591 / 35898750762359808000 : ℝ) := by
  apply lower_of_taylor (t := (115217 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_143 : (14520890104391860290754569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 143 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (99566039472467657710039233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_143_0
  · norm_num [gridPoint]

theorem exp_7_144_0 : (95169571716926884650895469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (565987936694014301003 / 7225094822355148800 : ℝ) := by
  apply lower_of_taylor (t := (922061 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_144 : (3469925336755198927620613 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 144 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (95169571716926884650895469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_144_0
  · norm_num [gridPoint]

theorem exp_7_145_0 : (45454931835666517798848871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (22795367578110958202757 / 290823289265972224000 : ℝ) := by
  apply lower_of_taylor (t := (922391 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_145 : (6629228935744247169058289 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 145 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (45454931835666517798848871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_145_0
  · norm_num [gridPoint]

theorem exp_7_146_0 : (86786559972295794265787269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4590403002672894602981 / 58529699042835456000 : ℝ) := by
  apply lower_of_taylor (t := (1845451 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_146 : (1582138481369946106840967 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 146 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (86786559972295794265787269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_146_0
  · norm_num [gridPoint]

theorem exp_7_147_0 : (20699748178326480986212933 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2310946227160577815883 / 29447941073882112000 : ℝ) := by
  apply lower_of_taylor (t := (1846129 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_147 : (2415110775349713533939853 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 147 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (20699748178326480986212933 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_147_0
  · norm_num [gridPoint]

theorem exp_7_148_0 : (15789240633684665642438703 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11633855925459767658399 / 148158017919951872000 : ℝ) := by
  apply lower_of_taylor (t := (1846817 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_148 : (11513656126541676447134183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 148 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (15789240633684665642438703 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_148_0
  · norm_num [gridPoint]

theorem exp_7_149_0 : (75226963237605919878016463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (937070649975616246843 / 11926334820697006080 : ℝ) := by
  apply lower_of_taylor (t := (1847513 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_149 : (10971235492022014928147201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 149 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (75226963237605919878016463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_149_0
  · norm_num [gridPoint]

theorem exp_7_150_0 : (71639796529488709085042363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (23586627965103052403927 / 300006414771385344000 : ℝ) := by
  apply lower_of_taylor (t := (1848219 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_150 : (2089615330724004451597343 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 150 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (71639796529488709085042363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_150_0
  · norm_num [gridPoint]

theorem exp_7_151_0 : (68182999005873658467597333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1187364974807106784881 / 15093008430089216000 : ℝ) := by
  apply lower_of_taylor (t := (1848933 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_151 : (4971965545671476515072227 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 151 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (68182999005873658467597333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_151_0
  · norm_num [gridPoint]

theorem exp_7_152_0 : (32427329560225132448791811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1195439167029615886721 / 15185981600431104000 : ℝ) := by
  apply lower_of_taylor (t := (231207 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_152 : (9458520021842073691733333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 152 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (32427329560225132448791811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_152_0
  · norm_num [gridPoint]

theorem exp_7_153_0 : (61652677392290990615936229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (24071081996538260196593 / 305584804991898624000 : ℝ) := by
  apply lower_of_taylor (t := (462597 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_153 : (4495768626523203672150951 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 153 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (61652677392290990615936229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_153_0
  · norm_num [gridPoint]

theorem exp_7_154_0 : (58574785362416831541953507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4846839592412924953281 / 61491137510322790400 : ℝ) := by
  apply lower_of_taylor (t := (231391 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_154 : (2135662987205579701205669 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 154 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (58574785362416831541953507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_154_0
  · norm_num [gridPoint]

theorem exp_7_155_0 : (55618563889174292870480147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (12199066867628036563061 / 154666139843884032000 : ℝ) := by
  apply lower_of_taylor (t := (1851877 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_155 : (4055755648602083616144163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 155 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (55618563889174292870480147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_155_0
  · norm_num [gridPoint]

theorem exp_7_156_0 : (26390730372639491098160923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2456289181419726695801 / 31121458140036096000 : ℝ) := by
  apply lower_of_taylor (t := (370527 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_156 : (962217884597345429585339 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 156 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (26390730372639491098160923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_156_0
  · norm_num [gridPoint]

theorem exp_7_157_0 : (25030403743070562928850919 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4945694939394573588867 / 62620518537878528000 : ℝ) := by
  apply lower_of_taylor (t := (1853401 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_157 : (7300958116792273454922761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 157 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (25030403743070562928850919 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_157_0
  · norm_num [gridPoint]

theorem exp_7_158_0 : (47453835565477529972609997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (803060802634436702173 / 10161171404995584000 : ℝ) := by
  apply lower_of_taylor (t := (57943 / 31250 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_158 : (6920752647480024688642111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 158 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (47453835565477529972609997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_158_0
  · norm_num [gridPoint]

theorem exp_7_159_0 : (44957691680220270269147913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (10105695510631426657 / 127780541934182400 : ℝ) := by
  apply lower_of_taylor (t := (927479 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_159 : (6556710537995562111850671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 159 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (44957691680220270269147913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_159_0
  · norm_num [gridPoint]

theorem sum_7_128_2 : (25938308833854105388287151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 128 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_128) (by simpa only [blockSum_one] using cell_7_129) (by norm_num)

theorem sum_7_130_2 : (24153041292292025611909877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 130 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_130) (by simpa only [blockSum_one] using cell_7_131) (by norm_num)

theorem sum_7_128_4 : (12522837531536532750049257 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 128 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_128_2 sum_7_130_2 (by norm_num)

theorem sum_7_132_2 : (22426104395390064487323801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 132 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_132) (by simpa only [blockSum_one] using cell_7_133) (by norm_num)

theorem sum_7_134_2 : (41528089677876241643991993 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 134 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_134) (by simpa only [blockSum_one] using cell_7_135) (by norm_num)

theorem sum_7_132_4 : (17276059693731274123727919 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 132 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_132_2 sum_7_134_2 (by norm_num)

theorem sum_7_128_8 : (186562998720948632619033651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 128 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_128_4 sum_7_132_4 (by norm_num)

theorem sum_7_136_2 : (4793026367072295286445787 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 136 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_136) (by simpa only [blockSum_one] using cell_7_137) (by norm_num)

theorem sum_7_138_2 : (35308593256354337082329209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 138 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_138) (by simpa only [blockSum_one] using cell_7_139) (by norm_num)

theorem sum_7_136_4 : (14730560838586539874779101 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 136 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_136_2 sum_7_138_2 (by norm_num)

theorem sum_7_140_2 : (32426959116083328120851301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 140 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_140) (by simpa only [blockSum_one] using cell_7_141) (by norm_num)

theorem sum_7_142_2 : (29702917297692548585935559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 142 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_142) (by simpa only [blockSum_one] using cell_7_143) (by norm_num)

theorem sum_7_140_4 : (3106493820688793835339343 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 140 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_140_2 sum_7_142_2 (by norm_num)

theorem sum_7_136_8 : (27156536121341715216136473 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 136 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_136_4 sum_7_140_4 (by norm_num)

theorem sum_7_128_16 : (20146604957978575543732251 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 128 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_128_8 sum_7_136_8 (by norm_num)

theorem sum_7_144_2 : (2713815921850929004859903 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 144 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_144) (by simpa only [blockSum_one] using cell_7_145) (by norm_num)

theorem sum_7_146_2 : (24732661727708136524427001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 146 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_146) (by simpa only [blockSum_one] using cell_7_147) (by norm_num)

theorem sum_7_144_4 : (51870820946217426573026031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 144 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_144_2 sum_7_146_2 (by norm_num)

theorem sum_7_148_2 : (2810611452320461421910173 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 148 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_148) (by simpa only [blockSum_one] using cell_7_149) (by norm_num)

theorem sum_7_150_2 : (20392007744962975288131169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 150 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_150) (by simpa only [blockSum_one] using cell_7_151) (by norm_num)

theorem sum_7_148_4 : (42876899363526666663412553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 148 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_148_2 sum_7_150_2 (by norm_num)

theorem sum_7_144_8 : (11843465038718011654554823 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 144 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_144_4 sum_7_148_4 (by norm_num)

theorem sum_7_152_2 : (3690011454977696207207047 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 152 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_152) (by simpa only [blockSum_one] using cell_7_153) (by norm_num)

theorem sum_7_154_2 : (8327081623013243018555501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 154 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_154) (by simpa only [blockSum_one] using cell_7_155) (by norm_num)

theorem sum_7_152_4 : (35104220520914967073146237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 152 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_152_2 sum_7_154_2 (by norm_num)

theorem sum_7_156_2 : (14998701193571036891605473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 156 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_156) (by simpa only [blockSum_one] using cell_7_157) (by norm_num)

theorem sum_7_158_2 : (6738731592737793400246391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 158 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_158) (by simpa only [blockSum_one] using cell_7_159) (by norm_num)

theorem sum_7_156_4 : (5695232875809324738419651 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 156 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_156_2 sum_7_158_2 (by norm_num)

theorem sum_7_152_8 : (15895096224990397691311123 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 152 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_152_4 sum_7_156_4 (by norm_num)

theorem sum_7_144_16 : (39582026302426421000420769 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 144 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_144_8 sum_7_152_8 (by norm_num)

theorem sum_7_128_32 : (120168446134340723175349773 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 128 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_128_16 sum_7_144_16 (by norm_num)

#print axioms sum_7_128_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
