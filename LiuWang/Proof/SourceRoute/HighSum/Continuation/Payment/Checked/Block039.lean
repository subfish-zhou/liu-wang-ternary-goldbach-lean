import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_224_0 : expNegUpper (7282143709946110729 / 90521295575824000 : ℝ) ≤ (2311458071276022601412871 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1874777 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_224_1 : expNegUpper (233287945098376073247 / 2896681458426368000 : ℝ) ≤ (10567509974447381174777227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1876089 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_224 : rowCell 2 224 ≤ (1613360317874238103566693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2311458071276022601412871 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10567509974447381174777227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_224_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_224_1
  · norm_num [gridPoint]

theorem exp_2_225_0 : expNegUpper (146538252847687965470247 / 1819530961463955968000 : ℝ) ≤ (10567508107211527705294457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1876089 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_225_1 : expNegUpper (73350836116047886594583 / 909765480731977984000 : ℝ) ≤ (9659771597611569623690257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (938703 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_225 : rowCell 2 225 ≤ (46093481531947189350971 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10567508107211527705294457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9659771597611569623690257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_225_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_225_1
  · norm_num [gridPoint]

theorem exp_2_226_0 : expNegUpper (24572936419628032471469 / 304776474952864512000 : ℝ) ≤ (9659769907787724067129909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (938703 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_226_1 : expNegUpper (9840157941986701865131 / 121910589981145804800 : ℝ) ≤ (4413768962984741694308243 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (234841 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_226 : rowCell 2 226 ≤ (1348111096928207458914101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9659769907787724067129909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4413768962984741694308243 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_226_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_226_1
  · norm_num [gridPoint]

theorem exp_2_227_0 : expNegUpper (29668196240300309876953 / 367561915255234662400 : ℝ) ≤ (8827536397090506639308203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (234841 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_227_1 : expNegUpper (37126766592984489217959 / 459452394069043328000 : ℝ) ≤ (15751496301974226282823 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376011 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_227 : rowCell 2 227 ≤ (9623452150374454925959 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8827536397090506639308203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15751496301974226282823 / 1953125000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_227_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_227_1
  · norm_num [gridPoint]

theorem exp_2_228_0 : expNegUpper (37312087722806668966791 / 461745785285228672000 : ℝ) ≤ (8064764723697182308431983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376011 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_228_1 : expNegUpper (149415773950846706602843 / 1846983141140914688000 : ℝ) ≤ (1473174880167675702591289 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1881387 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_228 : rowCell 2 228 ≤ (112521606842597154501357 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8064764723697182308431983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1473174880167675702591289 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_228_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_228_1
  · norm_num [gridPoint]

theorem exp_2_229_0 : expNegUpper (286018547770061373343 / 3535580084402688000 : ℝ) ≤ (1841468287567016050579551 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1881387 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_229_1 : expNegUpper (143170001770348022761 / 1767790042201344000 : ℝ) ≤ (6725709100077275820945667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470681 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_229 : rowCell 2 229 ≤ (1027570838101110239137829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1841468287567016050579551 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6725709100077275820945667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_229_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_229_1
  · norm_num [gridPoint]

theorem exp_2_230_0 : expNegUpper (75537575629003415763781 / 932699392893831424000 : ℝ) ≤ (1345141593893296382790691 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470681 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_230_1 : expNegUpper (151245260088332755489521 / 1865398785787662848000 : ℝ) ≤ (383719601352991066480129 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376813 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_230 : rowCell 2 230 ≤ (234535879255395216259527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1345141593893296382790691 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (383719601352991066480129 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_230_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_230_1
  · norm_num [gridPoint]

theorem exp_2_231_0 : expNegUpper (151994601919739154163689 / 1874640865569669632000 : ℝ) ≤ (3069756299870965186725163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376813 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_231_1 : expNegUpper (3804151465789683702583 / 46866021639241740800 : ℝ) ≤ (5602899658531919430484953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (471353 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_231 : rowCell 2 231 ≤ (428133625848421210307447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3069756299870965186725163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5602899658531919430484953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_231_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_231_1
  · norm_num [gridPoint]

theorem exp_2_232_0 : expNegUpper (1274317496306815297021 / 15699214863811929600 : ℝ) ≤ (1120579747021095538633701 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (471353 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_232_1 : expNegUpper (51030302493655949489837 / 627968594552477184000 : ℝ) ≤ (5111820262887742572633123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (471691 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_232 : rowCell 2 232 ≤ (97665866979876922664511 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1120579747021095538633701 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5111820262887742572633123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_232_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_232_1
  · norm_num [gridPoint]

theorem exp_2_233_0 : expNegUpper (153845654161581522693119 / 1893193540050948608000 : ℝ) ≤ (127795485716333142816207 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (471691 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_233_1 : expNegUpper (77009908314406451658579 / 946596770025474304000 : ℝ) ≤ (932508949720969496945113 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (47203 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_233 : rowCell 2 233 ≤ (712755417460981494942483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (127795485716333142816207 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (932508949720969496945113 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_233_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_233_1
  · norm_num [gridPoint]

theorem exp_2_234_0 : expNegUpper (3095545514527377240891 / 38050082695004416000 : ℝ) ≤ (932508799025877868923809 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (47203 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_234_1 : expNegUpper (6198111842698446375013 / 76100165390008832000 : ℝ) ≤ (4251635303615244621539731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (944741 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_234 : rowCell 2 234 ≤ (650029963297422424694377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (932508799025877868923809 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4251635303615244621539731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_234_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_234_1
  · norm_num [gridPoint]

theorem exp_2_235_0 : expNegUpper (51904324747839500141959 / 637279189251749376000 : ℝ) ≤ (531454327905465608631919 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (944741 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_235_1 : expNegUpper (12990821315770938614423 / 159319797312937344000 : ℝ) ≤ (96898130199508418492953 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (59089 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_235 : rowCell 2 235 ≤ (296334482498697218939807 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (531454327905465608631919 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (96898130199508418492953 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_235_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_235_1
  · norm_num [gridPoint]

theorem exp_2_236_0 : expNegUpper (180475529614480512173 / 2213356957449344000 : ℝ) ≤ (242245287110376383764097 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (59089 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_236_1 : expNegUpper (28908941158805873187 / 354137113191895040 : ℝ) ≤ (3532498558939286354925283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1892219 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_236 : rowCell 2 236 ≤ (540228872300447354142001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (242245287110376383764097 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3532498558939286354925283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_236_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_236_1
  · norm_num [gridPoint]

theorem exp_2_237_0 : expNegUpper (6303865684170370447779 / 77222917947302727680 : ℝ) ≤ (706499600916003308934653 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1892219 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_237_1 : expNegUpper (78888128025805801051793 / 965286474341284096000 : ℝ) ≤ (3218671409125581757943271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (378719 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_237 : rowCell 2 237 ≤ (492301339151182354350273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (706499600916003308934653 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3218671409125581757943271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_237_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_237_1
  · norm_num [gridPoint]

theorem exp_2_238_0 : expNegUpper (26424105238754612839979 / 323329149434143488000 : ℝ) ≤ (321867090890559729475671 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (378719 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_238_1 : expNegUpper (52908538858953043431491 / 646658298868286976000 : ℝ) ≤ (2931974229025746500071959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (75799 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_238 : rowCell 2 238 ≤ (224255284714097349855299 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (321867090890559729475671 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2931974229025746500071959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_238_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_238_1
  · norm_num [gridPoint]

theorem exp_2_239_0 : expNegUpper (6379869507300519153257 / 77975987313316352000 : ℝ) ≤ (18324836111016228214383 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (75799 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_239_1 : expNegUpper (399197743386507733353 / 4873499207082272000 : ℝ) ≤ (2670135609461433147961911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1896361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_239 : rowCell 2 239 ≤ (204255424830764413530691 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18324836111016228214383 / 6250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2670135609461433147961911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_239_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_239_1
  · norm_num [gridPoint]

theorem exp_2_240_0 : expNegUpper (10028310677909613331137 / 122427956710419488000 : ℝ) ≤ (1335067601228768284054233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1896361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_240_1 : expNegUpper (160636708377182137972831 / 1958847307366711808000 : ℝ) ≤ (1215533562209465600138973 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1897751 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_240 : rowCell 2 240 ≤ (23249016049206098921703 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1335067601228768284054233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1215533562209465600138973 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_240_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_240_1
  · norm_num [gridPoint]

theorem exp_2_241_0 : expNegUpper (53804446972329609056413 / 656105923402089984000 : ℝ) ≤ (2431066757417399474637731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1897751 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_241_1 : expNegUpper (5386615321231163697281 / 65610592340208998400 : ℝ) ≤ (221284927892525136701293 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (949573 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_241 : rowCell 2 241 ≤ (84659632409605000243383 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2431066757417399474637731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (221284927892525136701293 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_241_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_241_1
  · norm_num [gridPoint]

theorem exp_2_242_0 : expNegUpper (16237785788615666717363 / 197781107135158323200 : ℝ) ≤ (221284894806961202455177 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (949573 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_242_1 : expNegUpper (162564361126200058907061 / 1977811071351583232000 : ℝ) ≤ (503429617718889689415007 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950273 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_242 : rowCell 2 242 ≤ (308205093496147311990759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (221284894806961202455177 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (503429617718889689415007 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_242_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_242_1
  · norm_num [gridPoint]

theorem exp_2_243_0 : expNegUpper (23335218820913711434347 / 283903887257521664000 : ℝ) ≤ (1006859086336524108946801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950273 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_243_1 : expNegUpper (5840515101332722452421 / 70975971814380416000 : ℝ) ≤ (1832054899752089843826709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (38039 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_243 : rowCell 2 243 ≤ (280437227627985824420623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1006859086336524108946801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1832054899752089843826709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_243_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_243_1
  · norm_num [gridPoint]

theorem exp_2_244_0 : expNegUpper (547731241633484708329 / 6656220628531584000 : ℝ) ≤ (366410926208042151377421 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (38039 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_244_1 : expNegUpper (2193448730168294225729 / 26624882514126336000 : ℝ) ≤ (1666371359040080542603121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1903359 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_244 : rowCell 2 244 ≤ (127554183156877652160271 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (366410926208042151377421 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1666371359040080542603121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_244_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_244_1
  · norm_num [gridPoint]

theorem exp_2_245_0 : expNegUpper (165296390109443611277507 / 2006428004622053888000 : ℝ) ≤ (5207409740487949274557 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1903359 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_245_1 : expNegUpper (82743533447228110210893 / 1003214002311026944000 : ℝ) ≤ (1515302852842813367031101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1904773 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_245 : rowCell 2 245 ≤ (116005262206473597763341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5207409740487949274557 / 3125000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1515302852842813367031101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_245_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_245_1
  · norm_num [gridPoint]

theorem exp_2_246_0 : expNegUpper (83138797298464611552957 / 1008006329495193856000 : ℝ) ≤ (1515302634796207623640383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1904773 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_246_1 : expNegUpper (33293933845031467174637 / 403202531798077542400 : ℝ) ≤ (688798490363791742119727 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1906191 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_246 : rowCell 2 246 ≤ (13184552440843323108917 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1515302634796207623640383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (688798490363791742119727 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_246_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_246_1
  · norm_num [gridPoint]

theorem exp_2_247_0 : expNegUpper (11150866396322726314199 / 135041343444298444800 : ℝ) ≤ (1377596784374536863427359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1906191 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_247_1 : expNegUpper (6977352989461002500539 / 84400839652686528000 : ℝ) ≤ (626052519099885000054849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (953807 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_247 : rowCell 2 247 ≤ (38352043904969935118589 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1377596784374536863427359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (626052519099885000054849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_247_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_247_1
  · norm_num [gridPoint]

theorem exp_2_248_0 : expNegUpper (21031575518189659103473 / 254406310330540096000 : ℝ) ≤ (313026215355096760531281 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (953807 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_248_1 : expNegUpper (168447484452515039570103 / 2035250482644320768000 : ℝ) ≤ (568886891703213561697413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1909041 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_248 : rowCell 2 248 ≤ (174272097937366250540567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (313026215355096760531281 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (568886891703213561697413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_248_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_248_1
  · norm_num [gridPoint]

theorem exp_2_249_0 : expNegUpper (270794286706075206687 / 3271845843087872000 : ℝ) ≤ (1137773624283803149735503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1909041 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_249_1 : expNegUpper (135554173867079137019 / 1635922921543936000 : ℝ) ≤ (1033637823717503654322337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (955237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_249 : rowCell 2 249 ≤ (7917063683286405291299 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1137773624283803149735503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1033637823717503654322337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_249_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_249_1
  · norm_num [gridPoint]

theorem exp_2_250_0 : expNegUpper (4053440025583779416591 / 48918563321935104000 : ℝ) ≤ (1033637680518734618066567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (955237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_250_1 : expNegUpper (8116294303971635802521 / 97837126643870208000 : ℝ) ≤ (469406289362989385383459 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (191191 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_250 : rowCell 2 250 ≤ (35958211256851072621481 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1033637680518734618066567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (469406289362989385383459 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_250_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_250_1
  · norm_num [gridPoint]

theorem exp_2_251_0 : expNegUpper (171246769787521113509189 / 2064278505418383872000 : ℝ) ≤ (938812449884900147953233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (191191 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_251_1 : expNegUpper (8572294179675998901837 / 103213925270919193600 : ℝ) ≤ (852487778952212162412217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (239169 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_251 : rowCell 2 251 ≤ (6531161102905078775747 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (938812449884900147953233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (852487778952212162412217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_251_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_251_1
  · norm_num [gridPoint]

theorem exp_2_252_0 : expNegUpper (8612665266132139247277 / 103700009481062425600 : ℝ) ≤ (213121915763428612958247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (239169 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_252_1 : expNegUpper (172453836956534446554211 / 2074000189621248512000 : ℝ) ≤ (773921462137251439815069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1914797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_252 : rowCell 2 252 ≤ (23719842927174729315479 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (213121915763428612958247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (773921462137251439815069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_252_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_252_1
  · norm_num [gridPoint]

theorem exp_2_253_0 : expNegUpper (57754699224074132178313 / 694581570709956096000 : ℝ) ≤ (386960678951516378746099 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1914797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_253_1 : expNegUpper (28911008410797734022403 / 347290785354978048000 : ℝ) ≤ (702434431469524586635521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (239531 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_253 : rowCell 2 253 ≤ (107657190574451395940783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (386960678951516378746099 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (702434431469524586635521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_253_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_253_1
  · norm_num [gridPoint]

theorem exp_2_254_0 : expNegUpper (3485583136571971900129 / 41870241458884864000 : ℝ) ≤ (175608584436288179692871 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (239531 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_254_1 : expNegUpper (6979301364424579900257 / 83740482917769728000 : ℝ) ≤ (31870257120711185903321 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1917703 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_254 : rowCell 2 254 ≤ (24425574663813671365997 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (175608584436288179692871 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31870257120711185903321 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_254_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_254_1
  · norm_num [gridPoint]

theorem exp_2_255_0 : expNegUpper (175298492784110027089137 / 2103302272064373248000 : ℝ) ≤ (159351264539347727721067 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1917703 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_255_1 : expNegUpper (685559757368583489841 / 8216024500251458000 : ℝ) ≤ (578264987009814067104619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (959581 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_255 : rowCell 2 255 ≤ (88647751897148791905673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (159351264539347727721067 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (578264987009814067104619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_255_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_255_1
  · norm_num [gridPoint]

theorem sum_2_224_2 : blockSum (rowCell 2) 224 2 ≤ (617670345379309632559553 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_224) (by simpa only [blockSum_one] using cell_2_225) (by norm_num)

theorem sum_2_226_2 : blockSum (rowCell 2) 226 2 ≤ (2579912972176137689436853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_226) (by simpa only [blockSum_one] using cell_2_227) (by norm_num)

theorem sum_2_224_4 : blockSum (rowCell 2) 224 4 ≤ (2834132349536342926117309 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_224_2 sum_2_226_2 (by norm_num)

theorem sum_2_228_2 : blockSum (rowCell 2) 228 2 ≤ (2152786906527081784151399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_228) (by simpa only [blockSum_one] using cell_2_229) (by norm_num)

theorem sum_2_230_2 : blockSum (rowCell 2) 230 2 ≤ (897205384359211642826501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_230) (by simpa only [blockSum_one] using cell_2_231) (by norm_num)

theorem sum_2_228_4 : blockSum (rowCell 2) 228 4 ≤ (3947197675245505069804401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_228_2 sum_2_230_2 (by norm_num)

theorem sum_2_224_8 : blockSum (rowCell 2) 224 8 ≤ (9615462374318190922039019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_224_4 sum_2_228_4 (by norm_num)

theorem sum_2_232_2 : blockSum (rowCell 2) 232 2 ≤ (1494082353299996876258571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_232) (by simpa only [blockSum_one] using cell_2_233) (by norm_num)

theorem sum_2_234_2 : blockSum (rowCell 2) 234 2 ≤ (1242698928294816862573991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_234) (by simpa only [blockSum_one] using cell_2_235) (by norm_num)

theorem sum_2_232_4 : blockSum (rowCell 2) 232 4 ≤ (1368390640797406869416281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_232_2 sum_2_234_2 (by norm_num)

theorem sum_2_236_2 : blockSum (rowCell 2) 236 2 ≤ (516265105725814854246137 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_236) (by simpa only [blockSum_one] using cell_2_237) (by norm_num)

theorem sum_2_238_2 : blockSum (rowCell 2) 238 2 ≤ (42851070954486176338599 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_238) (by simpa only [blockSum_one] using cell_2_239) (by norm_num)

theorem sum_2_236_4 : blockSum (rowCell 2) 236 4 ≤ (944775815270676617632127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_236_2 sum_2_238_2 (by norm_num)

theorem sum_2_232_8 : blockSum (rowCell 2) 232 8 ≤ (289145807008510435881051 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_232_4 sum_2_236_4 (by norm_num)

theorem sum_2_224_16 : blockSum (rowCell 2) 224 16 ≤ (2848359057290871579227167 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_224_8 sum_2_232_8 (by norm_num)

theorem sum_2_240_2 : blockSum (rowCell 2) 240 2 ≤ (35531139321285879186039 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_240) (by simpa only [blockSum_one] using cell_2_241) (by norm_num)

theorem sum_2_242_2 : blockSum (rowCell 2) 242 2 ≤ (294321160562066568205691 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_242) (by simpa only [blockSum_one] using cell_2_243) (by norm_num)

theorem sum_2_240_4 : blockSum (rowCell 2) 240 4 ≤ (649632553774925360066081 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_240_2 sum_2_242_2 (by norm_num)

theorem sum_2_244_2 : blockSum (rowCell 2) 244 2 ≤ (60889861340837812480903 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_244) (by simpa only [blockSum_one] using cell_2_245) (by norm_num)

theorem sum_2_246_2 : blockSum (rowCell 2) 246 2 ≤ (402713058578342845335617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_246) (by simpa only [blockSum_one] using cell_2_247) (by norm_num)

theorem sum_2_244_4 : blockSum (rowCell 2) 244 4 ≤ (889831949305045345182841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_244_2 sum_2_246_2 (by norm_num)

theorem sum_2_240_8 : blockSum (rowCell 2) 240 8 ≤ (2189097056854896065315003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_240_4 sum_2_244_4 (by norm_num)

theorem sum_2_248_2 : blockSum (rowCell 2) 248 2 ≤ (332613371603094356366547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_248) (by simpa only [blockSum_one] using cell_2_249) (by norm_num)

theorem sum_2_250_2 : blockSum (rowCell 2) 250 2 ≤ (8576752096422058312527 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_250) (by simpa only [blockSum_one] using cell_2_251) (by norm_num)

theorem sum_2_248_4 : blockSum (rowCell 2) 248 4 ≤ (607069438688600222367411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_248_2 sum_2_250_2 (by norm_num)

theorem sum_2_252_2 : blockSum (rowCell 2) 252 2 ≤ (113128202605162521259089 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_252) (by simpa only [blockSum_one] using cell_2_253) (by norm_num)

theorem sum_2_254_2 : blockSum (rowCell 2) 254 2 ≤ (186350050552403477369661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_254) (by simpa only [blockSum_one] using cell_2_255) (by norm_num)

theorem sum_2_252_4 : blockSum (rowCell 2) 252 4 ≤ (412606455762728519887839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_252_2 sum_2_254_2 (by norm_num)

theorem sum_2_248_8 : blockSum (rowCell 2) 248 8 ≤ (4078703577805314969021 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_248_4 sum_2_252_4 (by norm_num)

theorem sum_2_240_16 : blockSum (rowCell 2) 240 16 ≤ (3208772951306224807570253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_240_8 sum_2_248_8 (by norm_num)

theorem sum_2_224_32 : blockSum (rowCell 2) 224 32 ≤ (2181321029720072837963261 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_224_16 sum_2_240_16 (by norm_num)

#print axioms sum_2_224_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
