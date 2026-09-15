import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_224_0 : expNegUpper (7136991623359947529 / 90521295575824000 : ℝ) ≤ (57445092239328661192027199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (925719 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_224_1 : expNegUpper (228654729102531055647 / 2896681458426368000 : ℝ) ≤ (10462917193884717890218743 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1852791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_224 : rowCell 1 224 ≤ (1600754869438620958549313 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (57445092239328661192027199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10462917193884717890218743 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_224_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_224_1
  · norm_num [gridPoint]

theorem exp_1_225_0 : expNegUpper (143627929381644573470247 / 1819530961463955968000 : ℝ) ≤ (26157288692959701199194151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1852791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_225_1 : expNegUpper (71899315250186254594583 / 909765480731977984000 : ℝ) ≤ (47629821035574940557421757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (37083 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_225 : rowCell 1 225 ≤ (7288035326690824299661419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26157288692959701199194151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47629821035574940557421757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_225_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_225_1
  · norm_num [gridPoint]

theorem exp_1_226_0 : expNegUpper (1852820683556470190113 / 23444344227143424000 : ℝ) ≤ (5953726662330221325207301 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (37083 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_226_1 : expNegUpper (742010490583369928087 / 9377737690857369600 : ℝ) ≤ (43353316399772037806770253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1855513 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_226 : rowCell 1 226 ≤ (663457156026392332779861 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5953726662330221325207301 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43353316399772037806770253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_226_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_226_1
  · norm_num [gridPoint]

theorem exp_1_227_0 : expNegUpper (29083218853363580276953 / 367561915255234662400 : ℝ) ≤ (4335330942755076870478689 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1855513 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_227_1 : expNegUpper (36397365292893609217959 / 459452394069043328000 : ℝ) ≤ (39450613536936316988109129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1856881 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_227 : rowCell 1 227 ≤ (603813645671993669509203 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4335330942755076870478689 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39450613536936316988109129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_227_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_227_1
  · norm_num [gridPoint]

theorem exp_1_228_0 : expNegUpper (36579045555555724966791 / 461745785285228672000 : ℝ) ≤ (4931325906913277234515231 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1856881 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_228_1 : expNegUpper (146490887016163058602843 / 1846983141140914688000 : ℝ) ≤ (35890052446296397645944619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (929127 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_228 : rowCell 1 228 ≤ (549390859431481338246897 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4931325906913277234515231 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35890052446296397645944619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_228_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_228_1
  · norm_num [gridPoint]

theorem exp_1_229_0 : expNegUpper (1962937162346110893401 / 24749060590818816000 : ℝ) ≤ (17945023394081265212946871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (929127 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_229_1 : expNegUpper (982642221265744319327 / 12374530295409408000 : ℝ) ≤ (32642555009249990267165269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1859631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_229 : rowCell 1 229 ≤ (312341180957921773234339 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17945023394081265212946871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32642555009249990267165269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_229_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_229_1
  · norm_num [gridPoint]

theorem exp_1_230_0 : expNegUpper (74064209560181399763781 / 932699392893831424000 : ℝ) ≤ (32642549913894231539061609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1859631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_230_1 : expNegUpper (148305809685008851489521 / 1865398785787662848000 : ℝ) ≤ (14840712050653337220439321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1861013 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_230 : rowCell 1 230 ≤ (454472017938385434612121 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32642549913894231539061609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14840712050653337220439321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_230_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_230_1
  · norm_num [gridPoint]

theorem exp_1_231_0 : expNegUpper (149040588047774994163689 / 1874640865569669632000 : ℝ) ≤ (29681419513796882876751351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1861013 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_231_1 : expNegUpper (3730483162348582902583 / 46866021639241740800 : ℝ) ≤ (26982157408728000746996431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1164 / 625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_231 : rowCell 1 231 ≤ (4131958937872905844793819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29681419513796882876751351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26982157408728000746996431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_231_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_231_1
  · norm_num [gridPoint]

theorem exp_1_232_0 : expNegUpper (1249640032921112897021 / 15699214863811929600 : ℝ) ≤ (26982153279380309251357213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1164 / 625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_232_1 : expNegUpper (50045631203001229489837 / 627968594552477184000 : ℝ) ≤ (24522274961293406430642939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (116487 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_232 : rowCell 1 232 ≤ (751149836163934965564577 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26982153279380309251357213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24522274961293406430642939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_232_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_232_1
  · norm_num [gridPoint]

theorem exp_1_233_0 : expNegUpper (150877076820977106693119 / 1893193540050948608000 : ℝ) ≤ (24522271245183032342911213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (116487 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_233_1 : expNegUpper (75529260511264307658579 / 946596770025474304000 : ℝ) ≤ (4456231890156107852991369 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466297 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_233 : rowCell 1 233 ≤ (1706474108153464773208553 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24522271245183032342911213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4456231890156107852991369 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_233_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_233_1
  · norm_num [gridPoint]

theorem exp_1_234_0 : expNegUpper (3036028333028886360891 / 38050082695004416000 : ℝ) ≤ (2785144513412110957871899 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466297 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_234_1 : expNegUpper (6079368749074269735013 / 76100165390008832000 : ℝ) ≤ (10119954230141514558319929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466647 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_234 : rowCell 1 234 ≤ (775168557696718741662753 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2785144513412110957871899 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10119954230141514558319929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_234_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_234_1
  · norm_num [gridPoint]

theorem exp_1_235_0 : expNegUpper (50909944478091276141959 / 637279189251749376000 : ℝ) ≤ (20239905452725216261385751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466647 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_235_1 : expNegUpper (12742833059527226614423 / 159319797312937344000 : ℝ) ≤ (18381197782434997129909797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1867993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_235 : rowCell 1 235 ≤ (2816285546555320599747491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20239905452725216261385751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18381197782434997129909797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_235_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_235_1
  · norm_num [gridPoint]

theorem exp_1_236_0 : expNegUpper (1239212396466163585211 / 15493498702145408000 : ℝ) ≤ (18381195077644245392621641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1867993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_236_1 : expNegUpper (198513374164228632309 / 2478959792343265280 : ℝ) ≤ (32596005966829466799277 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1869403 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_236 : rowCell 1 236 ≤ (2557361440191332502716097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18381195077644245392621641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32596005966829466799277 / 1953125000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_236_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_236_1
  · norm_num [gridPoint]

theorem exp_1_237_0 : expNegUpper (6183957513054973327779 / 77222917947302727680 : ℝ) ≤ (16689152623042341243469169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1869403 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_237_1 : expNegUpper (77392916754023401051793 / 965286474341284096000 : ℝ) ≤ (15149242990334681448744119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (935409 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_237 : rowCell 1 237 ≤ (1160842206468005694067509 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16689152623042341243469169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15149242990334681448744119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_237_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_237_1
  · norm_num [gridPoint]

theorem exp_1_238_0 : expNegUpper (25923274236720436839979 / 323329149434143488000 : ℝ) ≤ (3787310201032717915785639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (935409 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_238_1 : expNegUpper (51909304099658067431491 / 646658298868286976000 : ℝ) ≤ (171851894003314153875493 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1872237 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_238 : rowCell 1 238 ≤ (2107223810795873059259251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3787310201032717915785639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (171851894003314153875493 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_238_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_238_1
  · norm_num [gridPoint]

theorem exp_1_239_0 : expNegUpper (481490676726116291789 / 5998152870255104000 : ℝ) ≤ (6874074777707680066206451 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1872237 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_239_1 : expNegUpper (30129636796615007181 / 374884554390944000 : ℝ) ≤ (2494739644397347697243847 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (93683 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_239 : rowCell 1 239 ≤ (956060349309761770484317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6874074777707680066206451 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2494739644397347697243847 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_239_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_239_1
  · norm_num [gridPoint]

theorem exp_1_240_0 : expNegUpper (9839588835356781331137 / 122427956710419488000 : ℝ) ≤ (3118424114113474400119817 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (93683 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_240_1 : expNegUpper (157624440630656953972831 / 1958847307366711808000 : ℝ) ≤ (5657368215141882127007837 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (117193 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_240 : rowCell 1 240 ≤ (433668474630270495199461 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3118424114113474400119817 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5657368215141882127007837 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_240_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_240_1
  · norm_num [gridPoint]

theorem exp_1_241_0 : expNegUpper (52795503233941129056413 / 656105923402089984000 : ℝ) ≤ (11314734844183318262419587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (117193 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_241_1 : expNegUpper (5285963671869653297281 / 65610592340208998400 : ℝ) ≤ (641316905058974357816231 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1876521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_241 : rowCell 1 241 ≤ (314665421764170184830677 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11314734844183318262419587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (641316905058974357816231 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_241_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_241_1
  · norm_num [gridPoint]

theorem exp_1_242_0 : expNegUpper (15934374493667109917363 / 197781107135158323200 : ℝ) ≤ (10261069056337827176786949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1876521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_242_1 : expNegUpper (159537529911034618907061 / 1977811071351583232000 : ℝ) ≤ (232584439157152788748923 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (938979 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_242 : rowCell 1 242 ≤ (1426657025154250125649113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10261069056337827176786949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (232584439157152788748923 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_242_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_242_1
  · norm_num [gridPoint]

theorem exp_1_243_0 : expNegUpper (160305137062590284040429 / 1987327210802651648000 : ℝ) ≤ (9303376286997577841950111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (938979 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_243_1 : expNegUpper (40125077471957665166947 / 496831802700662912000 : ℝ) ≤ (8433135718323566273406399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1879399 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_243 : rowCell 1 243 ≤ (1293362390575522609607213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9303376286997577841950111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8433135718323566273406399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_243_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_243_1
  · norm_num [gridPoint]

theorem exp_1_244_0 : expNegUpper (537568986906398628329 / 6656220628531584000 : ℝ) ≤ (2108283642441484324461807 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1879399 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_244_1 : expNegUpper (2152896801050884945729 / 26624882514126336000 : ℝ) ≤ (1910639366884988165920731 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376169 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_244 : rowCell 1 244 ≤ (1172253906364910263005291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2108283642441484324461807 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1910639366884988165920731 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_244_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_244_1
  · norm_num [gridPoint]

theorem exp_1_245_0 : expNegUpper (162240431956997659277507 / 2006428004622053888000 : ℝ) ≤ (1528511287312953305712549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376169 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_245_1 : expNegUpper (81219195238165198210893 / 1003214002311026944000 : ℝ) ≤ (865566094485076616094147 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376459 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_245 : rowCell 1 245 ≤ (265561234962179914418271 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1528511287312953305712549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (865566094485076616094147 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_245_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_245_1
  · norm_num [gridPoint]

theorem exp_1_246_0 : expNegUpper (81607177355081571552957 / 1008006329495193856000 : ℝ) ≤ (3462263915319207446154717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376459 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_246_1 : expNegUpper (32682742214542276774637 / 403202531798077542400 : ℝ) ≤ (3136276355668048808895327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1507 / 800 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_246 : rowCell 1 246 ≤ (481171484936415441231291 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3462263915319207446154717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3136276355668048808895327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_246_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_246_1
  · norm_num [gridPoint]

theorem exp_1_247_0 : expNegUpper (10946164954916979114199 / 135041343444298444800 : ℝ) ≤ (6272551881150680548044009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1507 / 800 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_247_1 : expNegUpper (6849717994179082500539 / 84400839652686528000 : ℝ) ≤ (5680697918571090649611177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1885209 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_247 : rowCell 1 247 ≤ (871641714643578493261827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6272551881150680548044009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5680697918571090649611177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_247_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_247_1
  · norm_num [gridPoint]

theorem exp_1_248_0 : expNegUpper (20646850098763867103473 / 254406310330540096000 : ℝ) ≤ (2840348586912814884452533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1885209 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_248_1 : expNegUpper (165376962831428831570103 / 2035250482644320768000 : ℝ) ≤ (5143550845468914138506633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1886673 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_248 : rowCell 1 248 ≤ (789313890477287976670253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2840348586912814884452533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5143550845468914138506633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_248_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_248_1
  · norm_num [gridPoint]

theorem exp_1_249_0 : expNegUpper (265858150562512864287 / 3271845843087872000 : ℝ) ≤ (5143550177502901394536761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1886673 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_249_1 : expNegUpper (133091931182754068219 / 1635922921543936000 : ℝ) ≤ (4656172109313724948943369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94407 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_249 : rowCell 1 249 ≤ (357302276796330227389651 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5143550177502901394536761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4656172109313724948943369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_249_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_249_1
  · norm_num [gridPoint]

theorem exp_1_250_0 : expNegUpper (27858685708412023916137 / 342429943253545728000 : ℝ) ≤ (931234302065941171994511 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94407 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_250_1 : expNegUpper (55785698431225962617647 / 684859886507091456000 : ℝ) ≤ (842811257738634395941531 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1889613 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_250 : rowCell 1 250 ≤ (646824980450036436686291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (931234302065941171994511 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (842811257738634395941531 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_250_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_250_1
  · norm_num [gridPoint]

theorem exp_1_251_0 : expNegUpper (168147121229154393509189 / 2064278505418383872000 : ℝ) ≤ (4214055751672376965293529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1889613 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_251_1 : expNegUpper (8417675838473669301837 / 103213925270919193600 : ℝ) ≤ (3813095008149432429687769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1891089 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_251 : rowCell 1 251 ≤ (117069409059893423697783 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4214055751672376965293529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3813095008149432429687769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_251_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_251_1
  · norm_num [gridPoint]

theorem exp_1_252_0 : expNegUpper (650562980884445911329 / 7976923806235571200 : ℝ) ≤ (953273631693869034276637 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1891089 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_252_1 : expNegUpper (13027245261397517427247 / 159538476124711424000 : ℝ) ≤ (3449543042209621924969151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (189257 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_252 : rowCell 1 252 ≤ (529598056556334235735601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (953273631693869034276637 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3449543042209621924969151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_252_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_252_1
  · norm_num [gridPoint]

theorem exp_1_253_0 : expNegUpper (56716628548405140178313 / 694581570709956096000 : ℝ) ≤ (1724771305399759261044023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (189257 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_253_1 : expNegUpper (28393186695349926022403 / 347290785354978048000 : ℝ) ≤ (1559993601879427641505617 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (236757 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_253 : rowCell 1 253 ≤ (239528008194769692578403 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1724771305399759261044023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1559993601879427641505617 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_253_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_253_1
  · norm_num [gridPoint]

theorem exp_1_254_0 : expNegUpper (3423153261345429820129 / 41870241458884864000 : ℝ) ≤ (389998352150083211164531 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (236757 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_254_1 : expNegUpper (6854732883344300860257 / 83740482917769728000 : ℝ) ≤ (1410658899424855995926387 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (379109 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_254 : rowCell 1 254 ≤ (108311317623314880818011 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (389998352150083211164531 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1410658899424855995926387 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_254_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_254_1
  · norm_num [gridPoint]

theorem exp_1_255_0 : expNegUpper (172169717288462795089137 / 2103302272064373248000 : ℝ) ≤ (2821317452546201094825519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (379109 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_255_1 : expNegUpper (673366422363399489841 / 8216024500251458000 : ℝ) ≤ (19927362859665125604941 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1897039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_255 : rowCell 1 255 ≤ (195866258714412290034021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2821317452546201094825519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19927362859665125604941 / 7812500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_255_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_255_1
  · norm_num [gridPoint]

theorem sum_1_224_2 : blockSum (rowCell 1) 224 2 ≤ (955738104617745568275499 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_224) (by simpa only [blockSum_one] using cell_1_225) (by norm_num)

theorem sum_1_226_2 : blockSum (rowCell 1) 226 2 ≤ (158408850212298250286133 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_226) (by simpa only [blockSum_one] using cell_1_227) (by norm_num)

theorem sum_1_224_4 : blockSum (rowCell 1) 224 4 ≤ (436945588919809204926541 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_224_2 sum_1_226_2 (by norm_num)

theorem sum_1_228_2 : blockSum (rowCell 1) 228 2 ≤ (5245683744820780877109197 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_228) (by simpa only [blockSum_one] using cell_1_229) (by norm_num)

theorem sum_1_230_2 : blockSum (rowCell 1) 230 2 ≤ (8676679117256760190915029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_230) (by simpa only [blockSum_one] using cell_1_231) (by norm_num)

theorem sum_1_228_4 : blockSum (rowCell 1) 228 4 ≤ (19168046606898321945133423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_228_2 sum_1_230_2 (by norm_num)

theorem sum_1_224_8 : blockSum (rowCell 1) 224 8 ≤ (47132564297766111060432047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_224_4 sum_1_228_4 (by norm_num)

theorem sum_1_232_2 : blockSum (rowCell 1) 232 2 ≤ (7168697397126604374239991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_232) (by simpa only [blockSum_one] using cell_1_233) (by norm_num)

theorem sum_1_234_2 : blockSum (rowCell 1) 234 2 ≤ (5916959777342195566398503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_234) (by simpa only [blockSum_one] using cell_1_235) (by norm_num)

theorem sum_1_232_4 : blockSum (rowCell 1) 232 4 ≤ (6542828587234399970319247 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_232_2 sum_1_234_2 (by norm_num)

theorem sum_1_236_2 : blockSum (rowCell 1) 236 2 ≤ (975809170625468778170223 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_236) (by simpa only [blockSum_one] using cell_1_237) (by norm_num)

theorem sum_1_238_2 : blockSum (rowCell 1) 238 2 ≤ (803868901883079320045577 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_238) (by simpa only [blockSum_one] using cell_1_239) (by norm_num)

theorem sum_1_236_4 : blockSum (rowCell 1) 236 4 ≤ (8898390362542740491079 / 1000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_236_2 sum_1_238_2 (by norm_num)

theorem sum_1_232_8 : blockSum (rowCell 1) 232 8 ≤ (10992023768505770215858747 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_232_4 sum_1_236_4 (by norm_num)

theorem sum_1_224_16 : blockSum (rowCell 1) 224 16 ≤ (69116611834777651492149541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_224_8 sum_1_232_8 (by norm_num)

theorem sum_1_240_2 : blockSum (rowCell 1) 240 2 ≤ (3308001007341932904951229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_240) (by simpa only [blockSum_one] using cell_1_241) (by norm_num)

theorem sum_1_242_2 : blockSum (rowCell 1) 242 2 ≤ (1360009707864886367628163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_242) (by simpa only [blockSum_one] using cell_1_243) (by norm_num)

theorem sum_1_240_4 : blockSum (rowCell 1) 240 4 ≤ (1205604084614341128041511 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_240_2 sum_1_242_2 (by norm_num)

theorem sum_1_244_2 : blockSum (rowCell 1) 244 2 ≤ (17875990769709039365427 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_244) (by simpa only [blockSum_one] using cell_1_245) (by norm_num)

theorem sum_1_246_2 : blockSum (rowCell 1) 246 2 ≤ (1833984684516409375724409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_246) (by simpa only [blockSum_one] using cell_1_247) (by norm_num)

theorem sum_1_244_4 : blockSum (rowCell 1) 244 4 ≤ (127140110335313728012587 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_244_2 sum_1_246_2 (by norm_num)

theorem sum_1_240_8 : blockSum (rowCell 1) 240 8 ≤ (10096503953801744936610339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_240_4 sum_1_244_4 (by norm_num)

theorem sum_1_248_2 : blockSum (rowCell 1) 248 2 ≤ (300783688813989686289911 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_248) (by simpa only [blockSum_one] using cell_1_249) (by norm_num)

theorem sum_1_250_2 : blockSum (rowCell 1) 250 2 ≤ (616086012874751777587603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_250) (by simpa only [blockSum_one] using cell_1_251) (by norm_num)

theorem sum_1_248_4 : blockSum (rowCell 1) 248 4 ≤ (2736090469819451986624761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_248_2 sum_1_250_2 (by norm_num)

theorem sum_1_252_2 : blockSum (rowCell 1) 252 2 ≤ (1008654072945873620892407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_252) (by simpa only [blockSum_one] using cell_1_253) (by norm_num)

theorem sum_1_254_2 : blockSum (rowCell 1) 254 2 ≤ (412488893961042051670043 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_254) (by simpa only [blockSum_one] using cell_1_255) (by norm_num)

theorem sum_1_252_4 : blockSum (rowCell 1) 252 4 ≤ (1833631860867957724232493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_252_2 sum_1_254_2 (by norm_num)

theorem sum_1_248_8 : blockSum (rowCell 1) 248 8 ≤ (2284861165343704855428627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_248_4 sum_1_252_4 (by norm_num)

theorem sum_1_240_16 : blockSum (rowCell 1) 240 16 ≤ (14666226284489154647467593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_240_8 sum_1_248_8 (by norm_num)

theorem sum_1_224_32 : blockSum (rowCell 1) 224 32 ≤ (41891419059633403069808567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_224_16 sum_1_240_16 (by norm_num)

#print axioms sum_1_224_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
