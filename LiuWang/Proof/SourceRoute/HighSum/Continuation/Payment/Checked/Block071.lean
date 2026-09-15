import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_224_0 : expNegUpper (7475679825394328329 / 90521295575824000 : ℝ) ≤ (1362469582094299265981653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (381271 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_224_1 : expNegUpper (239465566426169430047 / 2896681458426368000 : ℝ) ≤ (1252484898684850879995863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1907609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_224 : rowCell 4 224 ≤ (19068483011158195366239 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1362469582094299265981653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1252484898684850879995863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_224_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_224_1
  · norm_num [gridPoint]

theorem exp_4_225_0 : expNegUpper (150418684135745821470247 / 1819530961463955968000 : ℝ) ≤ (313121164074710553945013 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1907609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_225_1 : expNegUpper (75286197270530062594583 / 909765480731977984000 : ℝ) ≤ (1151023176673425839047891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1908869 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_225 : rowCell 4 225 ≤ (35053190116381294516027 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (313121164074710553945013 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1151023176673425839047891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_225_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_225_1
  · norm_num [gridPoint]

theorem exp_4_226_0 : expNegUpper (75663879392459777414407 / 914329424858593536000 : ℝ) ≤ (14387786951795963447959 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1908869 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_226_1 : expNegUpper (30296560083571676795393 / 365731769943437414400 : ℝ) ≤ (528728375898094185451373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (955067 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_226 : rowCell 4 226 ≤ (32208864896792518119821 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14387786951795963447959 / 12500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (528728375898094185451373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_226_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_226_1
  · norm_num [gridPoint]

theorem exp_4_227_0 : expNegUpper (30448166089549282676953 / 367561915255234662400 : ℝ) ≤ (211491310241663471452691 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (955067 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_227_1 : expNegUpper (38099301659772329217959 / 459452394069043328000 : ℝ) ≤ (485600509733559428166549 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (477851 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_227 : rowCell 4 227 ≤ (36982883168922240601921 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (211491310241663471452691 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (485600509733559428166549 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_227_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_227_1
  · norm_num [gridPoint]

theorem exp_4_228_0 : expNegUpper (38289477279141260966791 / 461745785285228672000 : ℝ) ≤ (971200837068752110678623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (477851 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_228_1 : expNegUpper (153315623197091570602843 / 1846983141140914688000 : ℝ) ≤ (222927993039723595506541 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1912679 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_228 : rowCell 4 228 ≤ (135845275759607022711679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (971200837068752110678623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (222927993039723595506541 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_228_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_228_1
  · norm_num [gridPoint]

theorem exp_4_229_0 : expNegUpper (6163160191348563720203 / 74247181772456448000 : ℝ) ≤ (891711806346518819399109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1912679 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_229_1 : expNegUpper (3084761201684075837981 / 37123590886228224000 : ℝ) ≤ (32739344778146683823763 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (47849 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_229 : rowCell 4 229 ≤ (31177246738263106068959 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (891711806346518819399109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32739344778146683823763 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_229_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_229_1
  · norm_num [gridPoint]

theorem exp_4_230_0 : expNegUpper (77502063720766103763781 / 932699392893831424000 : ℝ) ≤ (163696693752098782974103 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (47849 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_230_1 : expNegUpper (155164527292764627489521 / 1865398785787662848000 : ℝ) ≤ (46940346936523421404709 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (957623 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_230 : rowCell 4 230 ≤ (22890293248704899904819 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (163696693752098782974103 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (46940346936523421404709 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_230_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_230_1
  · norm_num [gridPoint]

theorem exp_4_231_0 : expNegUpper (155933287082358034163689 / 1874640865569669632000 : ℝ) ≤ (18776135351728571410343 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (957623 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_231_1 : expNegUpper (3902375870377818102583 / 46866021639241740800 : ℝ) ≤ (137792127243295711768337 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (958269 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_231 : rowCell 4 231 ≤ (21001306988452663417683 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18776135351728571410343 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (137792127243295711768337 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_231_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_231_1
  · norm_num [gridPoint]

theorem exp_4_232_0 : expNegUpper (3921662342463255491063 / 47097644591435788800 : ℝ) ≤ (344480255926564826341803 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (958269 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_232_1 : expNegUpper (157029592643586728469511 / 1883905783657431552000 : ℝ) ≤ (25272914204127163229321 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (383567 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_232 : rowCell 4 232 ≤ (96312709759760282649369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (344480255926564826341803 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25272914204127163229321 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_232_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_232_1
  · norm_num [gridPoint]

theorem exp_4_233_0 : expNegUpper (157803757282387410693119 / 1893193540050948608000 : ℝ) ≤ (9872230346427200503449 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (383567 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_233_1 : expNegUpper (78984105385262643658579 / 946596770025474304000 : ℝ) ≤ (14481381343714288736633 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (59973 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_233 : rowCell 4 233 ≤ (22078223885091742542207 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9872230346427200503449 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14481381343714288736633 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_233_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_233_1
  · norm_num [gridPoint]

theorem exp_4_234_0 : expNegUpper (3174901756525365080891 / 38050082695004416000 : ℝ) ≤ (144813787806197435838613 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (59973 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_234_1 : expNegUpper (6356435967530681895013 / 76100165390008832000 : ℝ) ≤ (530908019330334963329121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (480111 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_234 : rowCell 4 234 ≤ (4047704790455161961561 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (144813787806197435838613 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (530908019330334963329121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_234_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_234_1
  · norm_num [gridPoint]

theorem exp_4_235_0 : expNegUpper (159690495322511396425877 / 1911837567755248128000 : ℝ) ≤ (530907926279999196113073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (480111 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_235_1 : expNegUpper (39964416972287663843269 / 477959391938812032000 : ℝ) ≤ (243228334332033327491261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (480439 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_235 : rowCell 4 235 ≤ (37093570150912275960527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (530907926279999196113073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (243228334332033327491261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_235_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_235_1
  · norm_num [gridPoint]

theorem exp_4_236_0 : expNegUpper (1295483788414963585211 / 15493498702145408000 : ℝ) ≤ (486456584233978060085951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (480439 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_236_1 : expNegUpper (207494873374857752309 / 2478959792343265280 : ℝ) ≤ (445600344933131825899641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (961537 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_236 : rowCell 4 236 ≤ (33983214334881475730679 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (486456584233978060085951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (445600344933131825899641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_236_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_236_1
  · norm_num [gridPoint]

theorem exp_4_237_0 : expNegUpper (6463743245657566607779 / 77222917947302727680 : ℝ) ≤ (445600268344664765565303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (961537 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_237_1 : expNegUpper (80881743054849001051793 / 965286474341284096000 : ℝ) ≤ (204030108629465083509013 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (481099 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_237 : rowCell 4 237 ≤ (62249689570806676963799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (445600268344664765565303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (204030108629465083509013 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_237_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_237_1
  · norm_num [gridPoint]

theorem exp_4_238_0 : expNegUpper (81275639724400542519937 / 969987448302430464000 : ℝ) ≤ (408060147801743144009323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (481099 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_238_1 : expNegUpper (162722555614039034294473 / 1939974896604860928000 : ℝ) ≤ (37357797794499706972763 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (481431 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_238 : rowCell 4 238 ≤ (5699775438245589697261 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (408060147801743144009323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37357797794499706972763 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_238_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_238_1
  · norm_num [gridPoint]

theorem exp_4_239_0 : expNegUpper (6540523787115195633257 / 77975987313316352000 : ℝ) ≤ (373577914971251219235279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (481431 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_239_1 : expNegUpper (409214363427191253353 / 4873499207082272000 : ℝ) ≤ (68382886478545099752797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1927057 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_239 : rowCell 4 239 ≤ (52174344794937017099339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (373577914971251219235279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (68382886478545099752797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_239_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_239_1
  · norm_num [gridPoint]

theorem exp_4_240_0 : expNegUpper (446953904404929970919 / 5322954639583456000 : ℝ) ≤ (2735315002494175502893 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1927057 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_240_1 : expNegUpper (7158828929241263042297 / 85167274233335296000 : ℝ) ≤ (312848176855240736229739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (385679 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_240 : rowCell 4 240 ≤ (5968234195906128343149 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2735315002494175502893 / 8000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (312848176855240736229739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_240_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_240_1
  · norm_num [gridPoint]

theorem exp_4_241_0 : expNegUpper (165449115870542747169239 / 1968317770206269952000 : ℝ) ≤ (312848125128740784039231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (385679 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_241_1 : expNegUpper (16562452561139532691843 / 196831777020626995200 : ℝ) ≤ (28617435936775310218189 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (964869 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_241 : rowCell 4 241 ≤ (43681257753747749001971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (312848125128740784039231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28617435936775310218189 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_241_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_241_1
  · norm_num [gridPoint]

theorem exp_4_242_0 : expNegUpper (16642334181880409117363 / 197781107135158323200 : ℝ) ≤ (286174312505197947568249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (964869 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_242_1 : expNegUpper (166600136079753978907061 / 1977811071351583232000 : ℝ) ≤ (10468140774654339390919 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (965543 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_242 : rowCell 4 242 ≤ (7990348746812693429561 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (286174312505197947568249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10468140774654339390919 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_242_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_242_1
  · norm_num [gridPoint]

theorem exp_4_243_0 : expNegUpper (167401724658136908040429 / 1987327210802651648000 : ℝ) ≤ (261703476920957278660863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (965543 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_243_1 : expNegUpper (41894976692490913166947 / 496831802700662912000 : ℝ) ≤ (239260501681685278016103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1932439 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_243 : rowCell 4 243 ≤ (36530743404529221044557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (261703476920957278660863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (239260501681685278016103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_243_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_243_1
  · norm_num [gridPoint]

theorem exp_4_244_0 : expNegUpper (1683842743808798444987 / 19968661885594752000 : ℝ) ≤ (59815115811648218209603 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1932439 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_244_1 : expNegUpper (6742553906974519797187 / 79874647542379008000 : ℝ) ≤ (5467086019201248315419 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1933797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_244 : rowCell 4 244 ≤ (33393680914724016529437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (59815115811648218209603 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5467086019201248315419 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_244_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_244_1
  · norm_num [gridPoint]

theorem exp_4_245_0 : expNegUpper (169371000979371547277507 / 2006428004622053888000 : ℝ) ≤ (27335425746613448781211 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1933797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_245_1 : expNegUpper (84775984392645326210893 / 1003214002311026944000 : ℝ) ≤ (99911405601021447028583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (48379 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_245 : rowCell 4 245 ≤ (953682792439902576101 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27335425746613448781211 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (99911405601021447028583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_245_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_245_1
  · norm_num [gridPoint]

theorem exp_4_246_0 : expNegUpper (85180957222975331552957 / 1008006329495193856000 : ℝ) ≤ (24977847463725905484367 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (48379 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_246_1 : expNegUpper (34108856019017054374637 / 403202531798077542400 : ℝ) ≤ (36508108131197132007471 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1936529 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_246 : rowCell 4 246 ≤ (27882276850619259695347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24977847463725905484367 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36508108131197132007471 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_246_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_246_1
  · norm_num [gridPoint]

theorem exp_4_247_0 : expNegUpper (34271404954591167742597 / 405124030332895334400 : ℝ) ≤ (91270256080011509081241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1936529 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_247_1 : expNegUpper (21442598949510687501617 / 253202518958059584000 : ℝ) ≤ (166709181720836068421131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (968951 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_247 : rowCell 4 247 ≤ (25467601456814090678013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (91270256080011509081241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (166709181720836068421131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_247_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_247_1
  · norm_num [gridPoint]

theorem exp_4_248_0 : expNegUpper (21544542744090715103473 / 254406310330540096000 : ℝ) ≤ (16670915594226093529393 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (968951 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_248_1 : expNegUpper (172541513280629983570103 / 2035250482644320768000 : ℝ) ≤ (6088445564772719069163 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (24241 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_248 : rowCell 4 248 ≤ (11627977222921464326011 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16670915594226093529393 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6088445564772719069163 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_248_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_248_1
  · norm_num [gridPoint]

theorem exp_4_249_0 : expNegUpper (277375801564158329887 / 3271845843087872000 : ℝ) ≤ (19026389475569514990051 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (24241 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_249_1 : expNegUpper (138837164112845895419 / 1635922921543936000 : ℝ) ≤ (69468974506419313441703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (970331 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_249 : rowCell 4 249 ≤ (21230851385722346815027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19026389475569514990051 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (69468974506419313441703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_249_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_249_1
  · norm_num [gridPoint]

theorem exp_4_250_0 : expNegUpper (87183818419957095748411 / 1027289829760637184000 : ℝ) ≤ (138937927931396636479019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (970331 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_250_1 : expNegUpper (174555627169706303852941 / 2054579659521274368000 : ℝ) ≤ (126789607264731062125651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (38841 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_250 : rowCell 4 250 ≤ (1211068162880252159577 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (138937927931396636479019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (126789607264731062125651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_250_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_250_1
  · norm_num [gridPoint]

theorem exp_4_251_0 : expNegUpper (175379634532010073509189 / 2064278505418383872000 : ℝ) ≤ (63394794103577821786737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (38841 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_251_1 : expNegUpper (8778451967945771701837 / 103213925270919193600 : ℝ) ≤ (115673943677185908179453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1943443 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_251 : rowCell 4 251 ≤ (17680658583335613291937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (63394794103577821786737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (115673943677185908179453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_251_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_251_1
  · norm_num [gridPoint]

theorem exp_4_252_0 : expNegUpper (8819793952311262447277 / 103700009481062425600 : ℝ) ≤ (115673926453197458472299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1943443 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_252_1 : expNegUpper (176586701701023406554211 / 2074000189621248512000 : ℝ) ≤ (105506039369643626182783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (48621 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_252 : rowCell 4 252 ≤ (4032160456044278962959 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (115673926453197458472299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (105506039369643626182783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_252_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_252_1
  · norm_num [gridPoint]

theorem exp_4_253_0 : expNegUpper (177416380374898364534939 / 2083744712129868288000 : ℝ) ≤ (105506023806429829614627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (48621 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_253_1 : expNegUpper (88804312094184434067209 / 1041872356064934144000 : ℝ) ≤ (48103842306093666922737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1946243 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_253 : rowCell 4 253 ≤ (14709144845045470910869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (105506023806429829614627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (48103842306093666922737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_253_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_253_1
  · norm_num [gridPoint]

theorem exp_4_254_0 : expNegUpper (3568822970207361340129 / 41870241458884864000 : ℝ) ≤ (1503244852388181547007 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1946243 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_254_1 : expNegUpper (7145392672531618620257 / 83740482917769728000 : ℝ) ≤ (43853437284219920165367 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (38953 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_254 : rowCell 4 254 ≤ (6705606932984061129061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1503244852388181547007 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43853437284219920165367 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_254_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_254_1
  · norm_num [gridPoint]

theorem exp_4_255_0 : expNegUpper (179470193444973003089137 / 2103302272064373248000 : ℝ) ≤ (2740839433454517684611 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (38953 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_255_1 : expNegUpper (701817537375495489841 / 8216024500251458000 : ℝ) ≤ (39968670269252016659997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (974531 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_255 : rowCell 4 255 ≤ (6112382928752962867637 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2740839433454517684611 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39968670269252016659997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_255_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_255_1
  · norm_num [gridPoint]

theorem sum_4_224_2 : blockSum (rowCell 4) 224 2 ≤ (14638031227739537049701 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_224) (by simpa only [blockSum_one] using cell_4_225) (by norm_num)

theorem sum_4_226_2 : blockSum (rowCell 4) 226 2 ≤ (308975857159651553006789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_226) (by simpa only [blockSum_one] using cell_4_227) (by norm_num)

theorem sum_4_224_4 : blockSum (rowCell 4) 224 4 ≤ (337463318926569989624657 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_224_2 sum_4_226_2 (by norm_num)

theorem sum_4_228_2 : blockSum (rowCell 4) 228 2 ≤ (52110852542531889397503 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_228) (by simpa only [blockSum_one] using cell_4_229) (by norm_num)

theorem sum_4_230_2 : blockSum (rowCell 4) 230 2 ≤ (21945800118578781661251 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_230) (by simpa only [blockSum_one] using cell_4_231) (by norm_num)

theorem sum_4_228_4 : blockSum (rowCell 4) 228 4 ≤ (19200490555937890544001 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_228_2 sum_4_230_2 (by norm_num)

theorem sum_4_224_8 : blockSum (rowCell 4) 224 8 ≤ (1154938901751587242849339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_224_4 sum_4_228_4 (by norm_num)

theorem sum_4_232_2 : blockSum (rowCell 4) 232 2 ≤ (184625605300127252818197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_232) (by simpa only [blockSum_one] using cell_4_233) (by norm_num)

theorem sum_4_234_2 : blockSum (rowCell 4) 234 2 ≤ (77570618055463895576137 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_234) (by simpa only [blockSum_one] using cell_4_235) (by norm_num)

theorem sum_4_232_4 : blockSum (rowCell 4) 232 4 ≤ (339766841411055043970471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_232_2 sum_4_234_2 (by norm_num)

theorem sum_4_236_2 : blockSum (rowCell 4) 236 2 ≤ (130216118240569628425157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_236) (by simpa only [blockSum_one] using cell_4_237) (by norm_num)

theorem sum_4_238_2 : blockSum (rowCell 4) 238 2 ≤ (109172099177392914071949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_238) (by simpa only [blockSum_one] using cell_4_239) (by norm_num)

theorem sum_4_236_4 : blockSum (rowCell 4) 236 4 ≤ (119694108708981271248553 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_236_2 sum_4_238_2 (by norm_num)

theorem sum_4_232_8 : blockSum (rowCell 4) 232 8 ≤ (579155058829017586467577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_232_4 sum_4_236_4 (by norm_num)

theorem sum_4_224_16 : blockSum (rowCell 4) 224 16 ≤ (433523490145151207329229 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_224_8 sum_4_232_8 (by norm_num)

theorem sum_4_240_2 : blockSum (rowCell 4) 240 2 ≤ (91427131320996775747163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_240) (by simpa only [blockSum_one] using cell_4_241) (by norm_num)

theorem sum_4_242_2 : blockSum (rowCell 4) 242 2 ≤ (38241243569296344096181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_242) (by simpa only [blockSum_one] using cell_4_243) (by norm_num)

theorem sum_4_240_4 : blockSum (rowCell 4) 240 4 ≤ (6716384738383578557581 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_240_2 sum_4_242_2 (by norm_num)

theorem sum_4_244_2 : blockSum (rowCell 4) 244 2 ≤ (63911530272800898964669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_244) (by simpa only [blockSum_one] using cell_4_245) (by norm_num)

theorem sum_4_246_2 : blockSum (rowCell 4) 246 2 ≤ (666873478842916879667 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_246) (by simpa only [blockSum_one] using cell_4_247) (by norm_num)

theorem sum_4_244_4 : blockSum (rowCell 4) 244 4 ≤ (117261408580234249338029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_244_2 sum_4_246_2 (by norm_num)

theorem sum_4_240_8 : blockSum (rowCell 4) 240 8 ≤ (142585513519911856638777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_240_4 sum_4_244_4 (by norm_num)

theorem sum_4_248_2 : blockSum (rowCell 4) 248 2 ≤ (44486805831565275467049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_248) (by simpa only [blockSum_one] using cell_4_249) (by norm_num)

theorem sum_4_250_2 : blockSum (rowCell 4) 250 2 ≤ (37057749189419647845169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_250) (by simpa only [blockSum_one] using cell_4_251) (by norm_num)

theorem sum_4_248_4 : blockSum (rowCell 4) 248 4 ≤ (40772277510492461656109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_248_2 sum_4_250_2 (by norm_num)

theorem sum_4_252_2 : blockSum (rowCell 4) 252 2 ≤ (6167557333844517352541 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_252) (by simpa only [blockSum_one] using cell_4_253) (by norm_num)

theorem sum_4_254_2 : blockSum (rowCell 4) 254 2 ≤ (6408994930868511998349 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_254) (by simpa only [blockSum_one] using cell_4_255) (by norm_num)

theorem sum_4_252_4 : blockSum (rowCell 4) 252 4 ≤ (56473766392696634756101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_252_2 sum_4_254_2 (by norm_num)

theorem sum_4_248_8 : blockSum (rowCell 4) 248 8 ≤ (138018321413681558068319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_248_4 sum_4_252_4 (by norm_num)

theorem sum_4_240_16 : blockSum (rowCell 4) 240 16 ≤ (423189348453505271345873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_240_8 sum_4_248_8 (by norm_num)

theorem sum_4_224_32 : blockSum (rowCell 4) 224 32 ≤ (2157283309034110100662789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_224_16 sum_4_240_16 (by norm_num)

#print axioms sum_4_224_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
