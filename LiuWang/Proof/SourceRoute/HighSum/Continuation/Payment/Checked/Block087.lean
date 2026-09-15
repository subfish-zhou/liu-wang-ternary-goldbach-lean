import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_224_0 : expNegUpper (7524063854256382729 / 90521295575824000 : ℝ) ≤ (399176087597907850578071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1914333 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_224_1 : expNegUpper (241009971758117769247 / 2896681458426368000 : ℝ) ≤ (734890200409204477025961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (478893 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_224 : rowCell 5 224 ≤ (27951352887891226007089 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (399176087597907850578071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (734890200409204477025961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_224_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_224_1
  · norm_num [gridPoint]

theorem exp_5_225_0 : expNegUpper (151388791957760285470247 / 1819530961463955968000 : ℝ) ≤ (734890055098525995585149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (478893 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_225_1 : expNegUpper (75770037559150606594583 / 909765480731977984000 : ℝ) ≤ (33812974390695553584991 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (119801 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_225 : rowCell 5 225 ≤ (51451146249421185669549 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (734890055098525995585149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33812974390695553584991 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_225_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_225_1
  · norm_num [gridPoint]

theorem exp_5_226_0 : expNegUpper (76150146925853697414407 / 914329424858593536000 : ℝ) ≤ (42266209714350170697651 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (119801 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_226_1 : expNegUpper (30490581647974569595393 / 365731769943437414400 : ℝ) ≤ (24884468053574582286851 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1918067 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_226 : rowCell 5 226 ≤ (94678383964839410534341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42266209714350170697651 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24884468053574582286851 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_226_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_226_1
  · norm_num [gridPoint]

theorem exp_5_227_0 : expNegUpper (30643158551861525876953 / 367561915255234662400 : ℝ) ≤ (155527895191564552573673 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1918067 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_227_1 : expNegUpper (38342435426469289217959 / 459452394069043328000 : ℝ) ≤ (572121762499932358052803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (959661 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_227 : rowCell 5 227 ≤ (87084568334989956961989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (155527895191564552573673 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (572121762499932358052803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_227_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_227_1
  · norm_num [gridPoint]

theorem exp_5_228_0 : expNegUpper (38533824668224908966791 / 461745785285228672000 : ℝ) ≤ (143030413178903556565447 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (959661 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_228_1 : expNegUpper (154290585508652786602843 / 1846983141140914688000 : ℝ) ≤ (131496646784133480128517 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1920583 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_228 : rowCell 5 228 ≤ (80075039431640385027247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (143030413178903556565447 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (131496646784133480128517 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_228_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_228_1
  · norm_num [gridPoint]

theorem exp_5_229_0 : expNegUpper (6202352863392882440203 / 74247181772456448000 : ℝ) ≤ (105197297440793593864827 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1920583 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_229_1 : expNegUpper (3104308992810767677981 / 37123590886228224000 : ℝ) ≤ (48342373603637657076851 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (38437 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_229 : rowCell 5 229 ≤ (18401775092670841590151 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (105197297440793593864827 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (48342373603637657076851 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_229_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_229_1
  · norm_num [gridPoint]

theorem exp_5_230_0 : expNegUpper (77993185743706775763781 / 932699392893831424000 : ℝ) ≤ (483423645097081870475637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (38437 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_230_1 : expNegUpper (156144344093872595489521 / 1865398785787662848000 : ℝ) ≤ (444170136256904267782323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (961561 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_230 : rowCell 5 230 ≤ (16910242980342651105923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (483423645097081870475637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (444170136256904267782323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_230_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_230_1
  · norm_num [gridPoint]

theorem exp_5_231_0 : expNegUpper (156917958373012754163689 / 1874640865569669632000 : ℝ) ≤ (222085026762323924985583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (961561 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_231_1 : expNegUpper (3926931971524851702583 / 46866021639241740800 : ℝ) ≤ (407980870512213882357039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1924399 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_231 : rowCell 5 231 ≤ (7767451373139221486167 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (222085026762323924985583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (407980870512213882357039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_231_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_231_1
  · norm_num [gridPoint]

theorem exp_5_232_0 : expNegUpper (3946339805848957891063 / 47097644591435788800 : ℝ) ≤ (8159615905343659645083 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1924399 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_232_1 : expNegUpper (158014263934241448469511 / 1883905783657431552000 : ℝ) ≤ (93657007994752314484339 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (962841 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_232 : rowCell 5 232 ≤ (28534269403955283577803 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8159615905343659645083 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (93657007994752314484339 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_232_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_232_1
  · norm_num [gridPoint]

theorem exp_5_233_0 : expNegUpper (158793283062588882693119 / 1893193540050948608000 : ℝ) ≤ (187313981781214546509129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (962841 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_233_1 : expNegUpper (79477654652976691658579 / 946596770025474304000 : ℝ) ≤ (68779928378039632292207 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (192697 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_233 : rowCell 5 233 ≤ (52395678541751103241429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (187313981781214546509129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (68779928378039632292207 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_233_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_233_1
  · norm_num [gridPoint]

theorem exp_5_234_0 : expNegUpper (3194740817024862040891 / 38050082695004416000 : ℝ) ≤ (171949789849681770602113 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (192697 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_234_1 : expNegUpper (6396016998738740775013 / 76100165390008832000 : ℝ) ≤ (157799313653049487720073 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1928263 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_234 : rowCell 5 234 ≤ (24045600886379341591969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (171949789849681770602113 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (157799313653049487720073 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_234_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_234_1
  · norm_num [gridPoint]

theorem exp_5_235_0 : expNegUpper (160684875592259620425877 / 1911837567755248128000 : ℝ) ≤ (315598570789790069129137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1928263 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_235_1 : expNegUpper (40212405228531375843269 / 477959391938812032000 : ℝ) ≤ (3619273206057689592021 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (964781 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_235 : rowCell 5 235 ≤ (22063691818851129596683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (315598570789790069129137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3619273206057689592021 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_235_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_235_1
  · norm_num [gridPoint]

theorem exp_5_236_0 : expNegUpper (1303522558693363585211 / 15493498702145408000 : ℝ) ≤ (289541805138869679970023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (964781 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_236_1 : expNegUpper (208777944690661912309 / 2478959792343265280 : ℝ) ≤ (132779614655725397264713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (386173 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_236 : rowCell 5 236 ≤ (20239233077851503980151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (289541805138869679970023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (132779614655725397264713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_236_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_236_1
  · norm_num [gridPoint]

theorem exp_5_237_0 : expNegUpper (6503712636029365647779 / 77222917947302727680 : ℝ) ≤ (265559182675666618723491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (386173 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_237_1 : expNegUpper (81380146812109801051793 / 965286474341284096000 : ℝ) ≤ (243492820298363061113371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (77287 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_237 : rowCell 5 237 ≤ (7424105881655033246699 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (265559182675666618723491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (243492820298363061113371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_237_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_237_1
  · norm_num [gridPoint]

theorem exp_5_238_0 : expNegUpper (81776470726434718519937 / 969987448302430464000 : ℝ) ≤ (243492777951707190112299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (77287 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_238_1 : expNegUpper (163721790373334010294473 / 1939974896604860928000 : ℝ) ≤ (111598035855273636761331 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1933489 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_238 : rowCell 5 238 ≤ (34031370208134963920007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (243492777951707190112299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (111598035855273636761331 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_238_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_238_1
  · norm_num [gridPoint]

theorem exp_5_239_0 : expNegUpper (6580687357068864753257 / 77975987313316352000 : ℝ) ≤ (223196033268648378869019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1933489 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_239_1 : expNegUpper (411718518437362133353 / 4873499207082272000 : ℝ) ≤ (51133258610644115288643 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (241851 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_239 : rowCell 5 239 ≤ (3898798488167098392261 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (223196033268648378869019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51133258610644115288643 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_239_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_239_1
  · norm_num [gridPoint]

theorem exp_5_240_0 : expNegUpper (10342847082164333331137 / 122427956710419488000 : ℝ) ≤ (25566624944310008163987 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (241851 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_240_1 : expNegUpper (165657154621390777972831 / 1958847307366711808000 : ℝ) ≤ (5855551697656305363561 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1936133 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_240 : rowCell 5 240 ≤ (5715695397623982079411 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25566624944310008163987 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5855551697656305363561 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_240_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_240_1
  · norm_num [gridPoint]

theorem exp_5_241_0 : expNegUpper (166458059608931227169239 / 1968317770206269952000 : ℝ) ≤ (187377622670368381686117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1936133 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_241_1 : expNegUpper (16663104210501043091843 / 196831777020626995200 : ℝ) ≤ (1716131016099643854507 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1937463 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_241 : rowCell 5 241 ≤ (1636120384078169436943 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (187377622670368381686117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1716131016099643854507 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_241_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_241_1
  · norm_num [gridPoint]

theorem exp_5_242_0 : expNegUpper (16743471280196594717363 / 197781107135158323200 : ℝ) ≤ (171613072896492304964939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1937463 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_242_1 : expNegUpper (167609079818142458907061 / 1977811071351583232000 : ℝ) ≤ (78565570726624862589219 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (969399 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_242 : rowCell 5 242 ≤ (23972323466513268684411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (171613072896492304964939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (78565570726624862589219 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_242_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_242_1
  · norm_num [gridPoint]

theorem exp_5_243_0 : expNegUpper (168415522886072140040429 / 1987327210802651648000 : ℝ) ≤ (39282778853576382601409 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (969399 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_243_1 : expNegUpper (42147819438281377166947 / 496831802700662912000 : ℝ) ≤ (143831543281471657598591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (970069 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_243 : rowCell 5 243 ≤ (10973233734117372268293 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (39282778853576382601409 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (143831543281471657598591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_243_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_243_1
  · norm_num [gridPoint]

theorem exp_5_244_0 : expNegUpper (36042659543316692021 / 424865146502016000 : ℝ) ≤ (71915759836956257732169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (970069 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_244_1 : expNegUpper (144321400767913384621 / 1699460586008064000 : ℝ) ≤ (526486108023651130269 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1941483 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_244 : rowCell 5 244 ≤ (4017256728247897427601 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (71915759836956257732169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (526486108023651130269 / 4000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_244_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_244_1
  · norm_num [gridPoint]

theorem exp_5_245_0 : expNegUpper (170389653696853531277507 / 2006428004622053888000 : ℝ) ≤ (26324301121617181026057 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1941483 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_245_1 : expNegUpper (85284097128999630210893 / 1003214002311026944000 : ℝ) ≤ (120415244118430654253311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1942833 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_245 : rowCell 5 245 ≤ (9189373114662459963737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26324301121617181026057 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (120415244118430654253311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_245_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_245_1
  · norm_num [gridPoint]

theorem exp_5_246_0 : expNegUpper (85691497204103011552957 / 1008006329495193856000 : ℝ) ≤ (24083044945667246233699 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1942833 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_246_1 : expNegUpper (34312586562513451174637 / 403202531798077542400 : ℝ) ≤ (110133291779288362013201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (486047 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_246 : rowCell 5 246 ≤ (840590247858439257689 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24083044945667246233699 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (110133291779288362013201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_246_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_246_1
  · norm_num [gridPoint]

theorem exp_5_247_0 : expNegUpper (34476106395996914942597 / 405124030332895334400 : ℝ) ≤ (2753331855322332315909 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (486047 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_247_1 : expNegUpper (21570233944792607501617 / 253202518958059584000 : ℝ) ≤ (25175564520338184766053 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (486387 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_247 : rowCell 5 247 ≤ (614972657497798649731 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2753331855322332315909 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25175564520338184766053 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_247_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_247_1
  · norm_num [gridPoint]

theorem exp_5_248_0 : expNegUpper (21672784550565979103473 / 254406310330540096000 : ℝ) ≤ (50351121085521701339179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (486387 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_248_1 : expNegUpper (173565020487658719570103 / 2035250482644320768000 : ℝ) ≤ (9205429674944441555449 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (973457 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_248 : rowCell 5 248 ≤ (7027989998892454040657 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (50351121085521701339179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9205429674944441555449 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_248_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_248_1
  · norm_num [gridPoint]

theorem exp_5_249_0 : expNegUpper (279021180278679110687 / 3271845843087872000 : ℝ) ≤ (719174080801621681059 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (973457 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_249_1 : expNegUpper (139657911674287585019 / 1635922921543936000 : ℝ) ≤ (42063364803692914379807 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (487071 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_249 : rowCell 5 249 ≤ (401477427469420088661 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (719174080801621681059 / 7812500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42063364803692914379807 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_249_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_249_1
  · norm_num [gridPoint]

theorem exp_5_250_0 : expNegUpper (87699212890631527748411 / 1027289829760637184000 : ℝ) ≤ (42063358282553782188479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (487071 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_250_1 : expNegUpper (175583988866281791852941 / 2054579659521274368000 : ℝ) ≤ (15372335043636534531603 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1949659 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_250 : rowCell 5 250 ≤ (11739418166845766884413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42063358282553782188479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15372335043636534531603 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_250_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_250_1
  · norm_num [gridPoint]

theorem exp_5_251_0 : expNegUpper (176412850718132313509189 / 2064278505418383872000 : ℝ) ≤ (38430831707027993372703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1949659 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_251_1 : expNegUpper (8829991415013214901837 / 103213925270919193600 : ℝ) ≤ (4387856385908509123331 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1951039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_251 : rowCell 5 251 ≤ (167566944211818895603 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38430831707027993372703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4387856385908509123331 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_251_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_251_1
  · norm_num [gridPoint]

theorem exp_5_252_0 : expNegUpper (8871576123856043247277 / 103700009481062425600 : ℝ) ≤ (7020569149356858071481 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1951039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_252_1 : expNegUpper (177619917887145646554211 / 2074000189621248512000 : ℝ) ≤ (64109505587298242138297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (244053 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_252 : rowCell 5 252 ≤ (1958876968989337212747 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7020569149356858071481 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64109505587298242138297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_252_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_252_1
  · norm_num [gridPoint]

theorem exp_5_253_0 : expNegUpper (178454451050567356534939 / 2083744712129868288000 : ℝ) ≤ (64109495924911496974451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (244053 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_253_1 : expNegUpper (89322133809632242067209 / 1041872356064934144000 : ℝ) ≤ (457246917096588132781 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (976907 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_253 : rowCell 5 253 ≤ (279462737797959623591 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (64109495924911496974451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (457246917096588132781 / 7812500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_253_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_253_1
  · norm_num [gridPoint]

theorem exp_5_254_0 : expNegUpper (3589632928616208700129 / 41870241458884864000 : ℝ) ≤ (58527596649477423609027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (976907 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_254_1 : expNegUpper (7186915499558378300257 / 83740482917769728000 : ℝ) ≤ (53418065131678779836417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1955209 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_254 : rowCell 5 254 ≤ (8163178233262416862769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (58527596649477423609027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (53418065131678779836417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_254_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_254_1
  · norm_num [gridPoint]

theorem exp_5_255_0 : expNegUpper (180513118610188747089137 / 2103302272064373248000 : ℝ) ≤ (2670902861493710311961 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1955209 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_255_1 : expNegUpper (705881982377223489841 / 8216024500251458000 : ℝ) ≤ (304638937758922874483 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1956609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_255 : rowCell 5 255 ≤ (7449619932456427390403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2670902861493710311961 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (304638937758922874483 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_255_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_255_1
  · norm_num [gridPoint]

theorem sum_5_224_2 : blockSum (rowCell 5) 224 2 ≤ (107353852025203637683727 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_224) (by simpa only [blockSum_one] using cell_5_225) (by norm_num)

theorem sum_5_226_2 : blockSum (rowCell 5) 226 2 ≤ (18176295229982936749633 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_226) (by simpa only [blockSum_one] using cell_5_227) (by norm_num)

theorem sum_5_224_4 : blockSum (rowCell 5) 224 4 ≤ (49558832043779580357973 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_224_2 sum_5_226_2 (by norm_num)

theorem sum_5_228_2 : blockSum (rowCell 5) 228 2 ≤ (153682139802323751387851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_228) (by simpa only [blockSum_one] using cell_5_229) (by norm_num)

theorem sum_5_230_2 : blockSum (rowCell 5) 230 2 ≤ (32445145726621094078257 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_230) (by simpa only [blockSum_one] using cell_5_231) (by norm_num)

theorem sum_5_228_4 : blockSum (rowCell 5) 228 4 ≤ (283462722708808127700879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_228_2 sum_5_230_2 (by norm_num)

theorem sum_5_224_8 : blockSum (rowCell 5) 224 8 ≤ (679933379059044770564663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_224_4 sum_5_228_4 (by norm_num)

theorem sum_5_232_2 : blockSum (rowCell 5) 232 2 ≤ (21892843469932334079407 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_232) (by simpa only [blockSum_one] using cell_5_233) (by norm_num)

theorem sum_5_234_2 : blockSum (rowCell 5) 234 2 ≤ (11527323176307617797163 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_234) (by simpa only [blockSum_one] using cell_5_235) (by norm_num)

theorem sum_5_232_4 : blockSum (rowCell 5) 232 4 ≤ (201682802760122612774339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_232_2 sum_5_234_2 (by norm_num)

theorem sum_5_236_2 : blockSum (rowCell 5) 236 2 ≤ (77598995563978174193797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_236) (by simpa only [blockSum_one] using cell_5_237) (by norm_num)

theorem sum_5_238_2 : blockSum (rowCell 5) 238 2 ≤ (13044351622694350211619 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_238) (by simpa only [blockSum_one] using cell_5_239) (by norm_num)

theorem sum_5_236_4 : blockSum (rowCell 5) 236 4 ≤ (35705188419362481312973 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_236_2 sum_5_238_2 (by norm_num)

theorem sum_5_232_8 : blockSum (rowCell 5) 232 8 ≤ (344503556437572538026231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_232_4 sum_5_236_4 (by norm_num)

theorem sum_5_224_16 : blockSum (rowCell 5) 224 16 ≤ (512218467748308654295447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_224_8 sum_5_232_8 (by norm_num)

theorem sum_5_240_2 : blockSum (rowCell 5) 240 2 ≤ (54756403133370621388143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_240) (by simpa only [blockSum_one] using cell_5_241) (by norm_num)

theorem sum_5_242_2 : blockSum (rowCell 5) 242 2 ≤ (45918790934748013220997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_242) (by simpa only [blockSum_one] using cell_5_243) (by norm_num)

theorem sum_5_240_4 : blockSum (rowCell 5) 240 4 ≤ (5033759703405931730457 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_240_2 sum_5_242_2 (by norm_num)

theorem sum_5_244_2 : blockSum (rowCell 5) 244 2 ≤ (38465029870564407065479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_244) (by simpa only [blockSum_one] using cell_5_245) (by norm_num)

theorem sum_5_246_2 : blockSum (rowCell 5) 246 2 ≤ (6437224278922750279411 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_246) (by simpa only [blockSum_one] using cell_5_247) (by norm_num)

theorem sum_5_244_4 : blockSum (rowCell 5) 244 4 ≤ (35325575632589079231267 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_244_2 sum_5_246_2 (by norm_num)

theorem sum_5_240_8 : blockSum (rowCell 5) 240 8 ≤ (85663172666648396535837 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_240_4 sum_5_244_4 (by norm_num)

theorem sum_5_248_2 : blockSum (rowCell 5) 248 2 ≤ (13451628838403175459233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_248) (by simpa only [blockSum_one] using cell_5_249) (by norm_num)

theorem sum_5_250_2 : blockSum (rowCell 5) 250 2 ≤ (4492740519280435240601 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_250) (by simpa only [blockSum_one] using cell_5_251) (by norm_num)

theorem sum_5_248_4 : blockSum (rowCell 5) 248 4 ≤ (49366960273208527121471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_248_2 sum_5_250_2 (by norm_num)

theorem sum_5_252_2 : blockSum (rowCell 5) 252 2 ≤ (18737192454481394018647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_252) (by simpa only [blockSum_one] using cell_5_253) (by norm_num)

theorem sum_5_254_2 : blockSum (rowCell 5) 254 2 ≤ (3903199541429711063293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_254) (by simpa only [blockSum_one] using cell_5_255) (by norm_num)

theorem sum_5_252_4 : blockSum (rowCell 5) 252 4 ≤ (34349990620200238271819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_252_2 sum_5_254_2 (by norm_num)

theorem sum_5_248_8 : blockSum (rowCell 5) 248 8 ≤ (8371695089340876539329 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_248_4 sum_5_252_4 (by norm_num)

theorem sum_5_240_16 : blockSum (rowCell 5) 240 16 ≤ (63760824056676389616241 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_240_8 sum_5_248_8 (by norm_num)

theorem sum_5_224_32 : blockSum (rowCell 5) 224 32 ≤ (639740115861661433527929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_224_16 sum_5_240_16 (by norm_num)

#print axioms sum_5_224_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
