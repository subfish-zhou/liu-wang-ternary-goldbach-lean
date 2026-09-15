import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_32_0 : expNegUpper (238360574117331481427 / 3033777816451587200 : ℝ) ≤ (9447264083961909184995701 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923737 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_32_1 : expNegUpper (38094403611715695174511 / 485404450632253952000 : ℝ) ≤ (20656955983686061990330579 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1846187 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_32 : rowCell 5 32 ≤ (11536519035487739751506261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9447264083961909184995701 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20656955983686061990330579 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_32_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_32_1
  · norm_num [gridPoint]

theorem exp_5_33_0 : expNegUpper (38464836689472398098919 / 490124545874743808000 : ℝ) ≤ (82627597714827563305361157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1846187 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_33_1 : expNegUpper (19211118414793321052279 / 245062272937371904000 : ℝ) ≤ (90130636544558941418181361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (922467 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_33 : rowCell 5 33 ≤ (6298842827335278171001779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (82627597714827563305361157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (90130636544558941418181361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_33_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_33_1
  · norm_num [gridPoint]

theorem exp_5_34_0 : expNegUpper (775881000249321313151 / 9897349588459776000 : ℝ) ≤ (45065197250978881427754797 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (922467 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_34_1 : expNegUpper (1550085674821257777293 / 19794699176919552000 : ℝ) ≤ (9809565111771675302688029 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (921857 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_34 : rowCell 5 34 ≤ (6862806177962263562233367 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45065197250978881427754797 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9809565111771675302688029 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_34_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_34_1
  · norm_num [gridPoint]

theorem exp_5_35_0 : expNegUpper (39125341820092686433277 / 499633251276988928000 : ℝ) ≤ (49047696349413010020029887 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (921857 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_35_1 : expNegUpper (9771032181722187221719 / 124908312819247232000 : ℝ) ≤ (106530048436677803932657159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (921263 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_35 : rowCell 5 35 ≤ (1492147101077070902330737 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (49047696349413010020029887 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (106530048436677803932657159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_35_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_35_1
  · norm_num [gridPoint]

theorem exp_5_36_0 : expNegUpper (9864680526172726788791 / 126105465359186048000 : ℝ) ≤ (106529773114210154796143259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (921263 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_36_1 : expNegUpper (1576728295639888087891 / 20176874457469767680 : ℝ) ≤ (115439157156214072823679641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (184137 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_36 : rowCell 5 36 ≤ (16186173820530124512304489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (106529773114210154796143259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (115439157156214072823679641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_36_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_36_1
  · norm_num [gridPoint]

theorem exp_5_37_0 : expNegUpper (1591768034343974982091 / 20369332396090183680 : ℝ) ≤ (7214929027060338275472497 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (184137 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_37_1 : expNegUpper (19877193927597725546293 / 254616654951127296000 : ℝ) ≤ (62413159465505442752450737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (920123 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_37 : rowCell 5 37 ≤ (17520353034151830216231843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7214929027060338275472497 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (62413159465505442752450737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_37_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_37_1
  · norm_num [gridPoint]

theorem exp_5_38_0 : expNegUpper (20065894037078367676837 / 257033798336760064000 : ℝ) ≤ (124826008343553294939584703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (920123 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_38_1 : expNegUpper (40092680111822142301873 / 514067596673520128000 : ℝ) ≤ (16836595447424983914296899 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_38 : rowCell 5 38 ≤ (9462171005009197205737031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (124826008343553294939584703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16836595447424983914296899 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_38_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_38_1
  · norm_num [gridPoint]

theorem exp_5_39_0 : expNegUpper (1618859749748065451537 / 20756988870021632000 : ℝ) ≤ (33673108675417361120220337 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_39_1 : expNegUpper (202165470766079612771 / 2594623608752704000 : ℝ) ≤ (145037495859388793440828539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (183809 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_39 : rowCell 5 39 ≤ (10199078928185927580005859 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33673108675417361120220337 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (145037495859388793440828539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_39_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_39_1
  · norm_num [gridPoint]

theorem exp_5_40_0 : expNegUpper (5101665982446590510699 / 65475585641664576000 : ℝ) ≤ (72518574153068245495389537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (183809 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_40_1 : expNegUpper (40775639971715438578631 / 523804685133316608000 : ℝ) ≤ (38964298836484865270096363 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1837057 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_40 : rowCell 5 40 ≤ (21941485873871253337017507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (72518574153068245495389537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38964298836484865270096363 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_40_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_40_1
  · norm_num [gridPoint]

theorem exp_5_41_0 : expNegUpper (41157300414108645474239 / 528707486821847552000 : ℝ) ≤ (155856828776013949653735699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1837057 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_41_1 : expNegUpper (4112032755965933710423 / 52870748682184755200 : ℝ) ≤ (167146130790454265695053407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (918027 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_41 : rowCell 5 41 ≤ (2355366600955834776202093 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (155856828776013949653735699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (167146130790454265695053407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_41_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_41_1
  · norm_num [gridPoint]

theorem exp_5_42_0 : expNegUpper (4150342139964804718343 / 53363312681613363200 : ℝ) ≤ (167145744909886946539394929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (918027 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_42_1 : expNegUpper (41467166909386264860061 / 533633126816133632000 : ℝ) ≤ (17889609021599553261622881 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_42 : rowCell 5 42 ≤ (504673630286811925801359 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (167145744909886946539394929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17889609021599553261622881 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_42_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_42_1
  · norm_num [gridPoint]

theorem exp_5_43_0 : expNegUpper (41851700808529575942229 / 538581605116174848000 : ℝ) ≤ (178895684780859543088164677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_43_1 : expNegUpper (10454042003308717143797 / 134645401279043712000 : ℝ) ≤ (47774081964130815192457719 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (917067 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_43 : rowCell 5 43 ≤ (26980149976216807955937877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (178895684780859543088164677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47774081964130815192457719 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_43_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_43_1
  · norm_num [gridPoint]

theorem exp_5_44_0 : expNegUpper (422021486330918784797 / 5435529217219712000 : ℝ) ≤ (191095902675540132568670951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (917067 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_44_1 : expNegUpper (1686693634541751799147 / 21742116868878848000 : ℝ) ≤ (50933382221830368895845013 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28644 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_44 : rowCell 5 44 ≤ (14395658439565644112461817 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (191095902675540132568670951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (50933382221830368895845013 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_44_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_44_1
  · norm_num [gridPoint]

theorem exp_5_45_0 : expNegUpper (42554774865673601524907 / 548547076633522688000 : ℝ) ≤ (12733317739011958062732679 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28644 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_45_1 : expNegUpper (21260347726325845399793 / 274273538316761344000 : ℝ) ≤ (43358358543792713131907067 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1832327 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_45 : rowCell 5 45 ≤ (15332525906422812079785231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12733317739011958062732679 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43358358543792713131907067 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_45_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_45_1
  · norm_num [gridPoint]

theorem exp_5_46_0 : expNegUpper (21454794749306695903457 / 276782034925414656000 : ℝ) ≤ (6774728990449911867217937 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1832327 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_46_1 : expNegUpper (8575248354579440553397 / 110712813970165862400 : ℝ) ≤ (230252635441021997761208567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366293 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_46 : rowCell 5 46 ≤ (509356991138990560974307 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6774728990449911867217937 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (230252635441021997761208567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_46_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_46_1
  · norm_num [gridPoint]

theorem exp_5_47_0 : expNegUpper (8653320504849979210957 / 111720780274778214400 : ℝ) ≤ (115126075217227894416100911 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366293 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_47_1 : expNegUpper (2702124363538686100621 / 34912743835868192000 : ℝ) ≤ (122047505903400773233696449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (183063 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_47 : rowCell 5 47 ≤ (34589821241911061019683631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (115126075217227894416100911 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (122047505903400773233696449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_47_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_47_1
  · norm_num [gridPoint]

theorem exp_5_48_0 : expNegUpper (2726613995932610062349 / 35229160700169248000 : ℝ) ≤ (244094506857779375930035237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (183063 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_48_1 : expNegUpper (43593949576155662057503 / 563666571202707968000 : ℝ) ≤ (64573839237332743143558513 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1829821 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_48 : rowCell 5 48 ≤ (36634720234707750813635051 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (244094506857779375930035237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64573839237332743143558513 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_48_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_48_1
  · norm_num [gridPoint]

theorem exp_5_49_0 : expNegUpper (70379621956748213383 / 910003326939648000 : ℝ) ≤ (12914741607926987583515793 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1829821 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_49_1 : expNegUpper (35164904835076722271 / 455001663469824000 : ℝ) ≤ (136413823907211264673023179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1829039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_49 : rowCell 5 49 ≤ (9682482104995377560003121 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12914741607926987583515793 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (136413823907211264673023179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_49_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_49_1
  · norm_num [gridPoint]

theorem exp_5_50_0 : expNegUpper (715337610979454191681 / 9255813318993664000 : ℝ) ≤ (27282710334437175334767561 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1829039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_50_1 : expNegUpper (1429694974581559570411 / 18511626637987328000 : ℝ) ≤ (2876634840915650301652737 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (914141 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_50 : rowCell 5 50 ≤ (20435738600795329864109101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27282710334437175334767561 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2876634840915650301652737 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_50_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_50_1
  · norm_num [gridPoint]

theorem exp_5_51_0 : expNegUpper (44716838400535987286189 / 578991610523689472000 : ℝ) ≤ (71915730041725904482168103 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (914141 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_51_1 : expNegUpper (2234359953652082015927 / 28949580526184473600 : ℝ) ≤ (151386094110249206597396943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1827551 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_51 : rowCell 5 51 ≤ (86110117145304095832071 / 2000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (71915730041725904482168103 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (151386094110249206597396943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_51_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_51_1
  · norm_num [gridPoint]

theorem exp_5_52_0 : expNegUpper (2254249663736788114967 / 29207281678776345600 : ℝ) ≤ (60554321025593101804321891 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1827551 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_52_1 : expNegUpper (45056105619224430475211 / 584145633575526912000 : ℝ) ≤ (318120923853205875093005317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (365369 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_52 : rowCell 5 52 ≤ (14488333134860327632257 / 320000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (60554321025593101804321891 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (318120923853205875093005317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_52_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_52_1
  · norm_num [gridPoint]

theorem exp_5_53_0 : expNegUpper (45455406495664131652739 / 589322494933119488000 : ℝ) ≤ (318120321941215548728529013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (365369 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_53_1 : expNegUpper (22713636921457681940909 / 294661247466559744000 : ℝ) ≤ (333674831960327705909381273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456541 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_53 : rowCell 5 53 ≤ (47529488219709117545964257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (318120321941215548728529013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (333674831960327705909381273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_53_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_53_1
  · norm_num [gridPoint]

theorem exp_5_54_0 : expNegUpper (916561761113194841509 / 11890443891929344000 : ℝ) ≤ (333674211638190724227068317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456541 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_54_1 : expNegUpper (1832028549458123490697 / 23780887783858688000 : ℝ) ≤ (174698591795038801741383967 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825507 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_54 : rowCell 5 54 ≤ (49810179837001976853926937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (333674211638190724227068317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (174698591795038801741383967 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_54_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_54_1
  · norm_num [gridPoint]

theorem exp_5_55_0 : expNegUpper (46203047947061240296537 / 599744732565570048000 : ℝ) ≤ (21837284082929162912346291 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825507 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_55_1 : expNegUpper (5772054411522030920137 / 74968091570696256000 : ℝ) ≤ (365249548118875243571187797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (14599 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_55 : rowCell 5 55 ≤ (5211263519891307587299719 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21837284082929162912346291 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (365249548118875243571187797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_55_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_55_1
  · norm_num [gridPoint]

theorem exp_5_56_0 : expNegUpper (123883766388849130439 / 1609016246916032000 : ℝ) ≤ (182624446220971351749447119 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (14599 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_56_1 : expNegUpper (198104036180525493157 / 2574425995065651200 : ℝ) ≤ (47648996959766716340907731 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912133 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_56 : rowCell 5 56 ≤ (54431138733783425214942677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (182624446220971351749447119 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47648996959766716340907731 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_56_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_56_1
  · norm_num [gridPoint]

theorem exp_5_57_0 : expNegUpper (9391968538687297410019 / 122051664684208230400 : ℝ) ≤ (76238260634258993899482181 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912133 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_57_1 : expNegUpper (23467381679766732294443 / 305129161710520576000 : ℝ) ≤ (397183192302753750478687639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (5699 / 3125 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_57 : rowCell 5 57 ≤ (1418994188270085253157599 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (76238260634258993899482181 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (397183192302753750478687639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_57_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_57_1
  · norm_num [gridPoint]

theorem exp_5_58_0 : expNegUpper (23670848766543764520347 / 307774688153704704000 : ℝ) ≤ (99295625901037504238460953 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (5699 / 3125 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_58_1 : expNegUpper (47317389855844815181133 / 615549376307409408000 : ℝ) ≤ (51647600778176686751608843 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911559 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_58 : rowCell 5 58 ≤ (5909242061355794621815971 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (99295625901037504238460953 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51647600778176686751608843 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_58_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_58_1
  · norm_num [gridPoint]

theorem exp_5_59_0 : expNegUpper (1909034826939961829837 / 24834530699981312000 : ℝ) ≤ (413180102025072617942154737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911559 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_59_1 : expNegUpper (477023379836961893977 / 6208632674995328000 : ℝ) ≤ (85828304727592605537300251 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911289 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_59 : rowCell 5 59 ≤ (12284569943336823182565893 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (413180102025072617942154737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (85828304727592605537300251 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_59_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_59_1
  · norm_num [gridPoint]

theorem exp_5_60_0 : expNegUpper (12028093026752420973713 / 156549999249352832000 : ℝ) ≤ (13410650146096170705590291 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911289 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_60_1 : expNegUpper (48089617735426233967651 / 626199996997411328000 : ℝ) ≤ (445021372158103241493887917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822061 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_60 : rowCell 5 60 ≤ (63744691314756285501775731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13410650146096170705590291 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (445021372158103241493887917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_60_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_60_1
  · norm_num [gridPoint]

theorem exp_5_61_0 : expNegUpper (48501211825958090216539 / 631559564801044992000 : ℝ) ≤ (445020639218047355269824479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822061 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_61_1 : expNegUpper (969584782067471912401 / 12631191296020899840 : ℝ) ≤ (460775930176727425486236313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (364313 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_61 : rowCell 5 61 ≤ (66051499641872292630699039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (445020639218047355269824479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (460775930176727425486236313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_61_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_61_1
  · norm_num [gridPoint]

theorem exp_5_62_0 : expNegUpper (977847996453658228801 / 12738839418208675840 : ℝ) ≤ (460775184087837683880562721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (364313 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_62_1 : expNegUpper (48871212079876921083961 / 636941970910433792000 : ℝ) ≤ (59545070027400819638785907 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455273 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_62 : rowCell 5 62 ≤ (34168390216382470956556523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (460775184087837683880562721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (59545070027400819638785907 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_62_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_62_1
  · norm_num [gridPoint]

theorem exp_5_63_0 : expNegUpper (49285946089522794294449 / 642347215325577728000 : ℝ) ≤ (59544975231168719704677919 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455273 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_63_1 : expNegUpper (769774166519919642007 / 10036675239462152000 : ℝ) ≤ (491730644432594182265126921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11379 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_63 : rowCell 5 63 ≤ (70594025111639683531702473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (59544975231168719704677919 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (491730644432594182265126921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_63_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_63_1
  · norm_num [gridPoint]

theorem sum_5_32_2 : blockSum (rowCell 5) 32 2 ≤ (24134204690158296093509819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_32) (by simpa only [blockSum_one] using cell_5_33) (by norm_num)

theorem sum_5_34_2 : blockSum (rowCell 5) 34 2 ≤ (3580885420836904518471763 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_34) (by simpa only [blockSum_one] using cell_5_35) (by norm_num)

theorem sum_5_32_4 : blockSum (rowCell 5) 32 4 ≤ (52781288056853532241283923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_32_2 sum_5_34_2 (by norm_num)

theorem sum_5_36_2 : blockSum (rowCell 5) 36 2 ≤ (8426631713670488682134083 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_36) (by simpa only [blockSum_one] using cell_5_37) (by norm_num)

theorem sum_5_38_2 : blockSum (rowCell 5) 38 2 ≤ (1966124993319512478574289 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_38) (by simpa only [blockSum_one] using cell_5_39) (by norm_num)

theorem sum_5_36_4 : blockSum (rowCell 5) 36 4 ≤ (2282157085033506384375691 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_36_2 sum_5_38_2 (by norm_num)

theorem sum_5_32_8 : blockSum (rowCell 5) 32 8 ≤ (25162062955585147308261207 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_32_4 sum_5_36_4 (by norm_num)

theorem sum_5_40_2 : blockSum (rowCell 5) 40 2 ≤ (45495151883429601099038437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_40) (by simpa only [blockSum_one] using cell_5_41) (by norm_num)

theorem sum_5_42_2 : blockSum (rowCell 5) 42 2 ≤ (52213831490557404246005827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_42) (by simpa only [blockSum_one] using cell_5_43) (by norm_num)

theorem sum_5_40_4 : blockSum (rowCell 5) 40 4 ≤ (12213622921748375668130533 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_40_2 sum_5_42_2 (by norm_num)

theorem sum_5_44_2 : blockSum (rowCell 5) 44 2 ≤ (3716023043248557024030881 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_44) (by simpa only [blockSum_one] using cell_5_45) (by norm_num)

theorem sum_5_46_2 : blockSum (rowCell 5) 46 2 ≤ (67188668674806456922039279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_46) (by simpa only [blockSum_one] using cell_5_47) (by norm_num)

theorem sum_5_44_4 : blockSum (rowCell 5) 44 4 ≤ (1013160298934266954452267 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_44_2 sum_5_46_2 (by norm_num)

theorem sum_5_40_8 : blockSum (rowCell 5) 40 8 ≤ (224354020740770374651577639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_40_4 sum_5_44_4 (by norm_num)

theorem sum_5_32_16 : blockSum (rowCell 5) 32 16 ≤ (175082167759348055596441837 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_32_8 sum_5_40_8 (by norm_num)

theorem sum_5_48_2 : blockSum (rowCell 5) 48 2 ≤ (15072929730937852210729507 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_48) (by simpa only [blockSum_one] using cell_5_49) (by norm_num)

theorem sum_5_50_2 : blockSum (rowCell 5) 50 2 ≤ (41963267887121353822126851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_50) (by simpa only [blockSum_one] using cell_5_51) (by norm_num)

theorem sum_5_48_4 : blockSum (rowCell 5) 48 4 ≤ (159291184428931968697901237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_48_2 sum_5_50_2 (by norm_num)

theorem sum_5_52_2 : blockSum (rowCell 5) 52 2 ≤ (46402764633073820698383691 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_52) (by simpa only [blockSum_one] using cell_5_53) (by norm_num)

theorem sum_5_54_2 : blockSum (rowCell 5) 54 2 ≤ (101922815035915052726924127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_54) (by simpa only [blockSum_one] using cell_5_55) (by norm_num)

theorem sum_5_52_4 : blockSum (rowCell 5) 52 4 ≤ (194728344302062694123691509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_52_2 sum_5_54_2 (by norm_num)

theorem sum_5_48_8 : blockSum (rowCell 5) 48 8 ≤ (177009764365497331410796373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_48_4 sum_5_52_4 (by norm_num)

theorem sum_5_56_2 : blockSum (rowCell 5) 56 2 ≤ (111190906264586835341246637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_56) (by simpa only [blockSum_one] using cell_5_57) (by norm_num)

theorem sum_5_58_2 : blockSum (rowCell 5) 58 2 ≤ (4820610813209682485239567 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_58) (by simpa only [blockSum_one] using cell_5_59) (by norm_num)

theorem sum_5_56_4 : blockSum (rowCell 5) 56 4 ≤ (57926544148707224368058953 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_56_2 sum_5_58_2 (by norm_num)

theorem sum_5_60_2 : blockSum (rowCell 5) 60 2 ≤ (12979619095662857813247477 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_60) (by simpa only [blockSum_one] using cell_5_61) (by norm_num)

theorem sum_5_62_2 : blockSum (rowCell 5) 62 2 ≤ (138930805544404625444815519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_62) (by simpa only [blockSum_one] using cell_5_63) (by norm_num)

theorem sum_5_60_4 : blockSum (rowCell 5) 60 4 ≤ (268726996501033203577290289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_60_2 sum_5_62_2 (by norm_num)

theorem sum_5_56_8 : blockSum (rowCell 5) 56 8 ≤ (500433173095862101049526101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_56_4 sum_5_60_4 (by norm_num)

theorem sum_5_48_16 : blockSum (rowCell 5) 48 16 ≤ (854452701826856763871118847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_48_8 sum_5_56_8 (by norm_num)

theorem sum_5_32_32 : blockSum (rowCell 5) 32 32 ≤ (1204617037345552875064002521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_32_16 sum_5_48_16 (by norm_num)

#print axioms sum_5_32_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
