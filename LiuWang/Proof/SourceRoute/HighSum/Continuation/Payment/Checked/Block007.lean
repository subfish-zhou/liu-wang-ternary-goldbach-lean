import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_224_0 : expNegUpper (6991839536773784329 / 90521295575824000 : ℝ) ≤ (285528745980087998047607151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828389 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_224_1 : expNegUpper (224021513106686038047 / 2896681458426368000 : ℝ) ≤ (129491995359830777504165139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1829783 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_224 : rowCell 0 224 ≤ (2481647373175476005629877 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (285528745980087998047607151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (129491995359830777504165139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_224_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_224_1
  · norm_num [gridPoint]

theorem exp_0_225_0 : expNegUpper (140717605915601181470247 / 1819530961463955968000 : ℝ) ≤ (258983951495592399179365079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1829783 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_225_1 : expNegUpper (70447794384324622594583 / 909765480731977984000 : ℝ) ≤ (234850257995936528459861267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (915591 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_225 : rowCell 0 225 ≤ (2197926894244072231993 / 61035156250000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (258983951495592399179365079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (234850257995936528459861267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_225_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_225_1
  · norm_num [gridPoint]

theorem exp_0_226_0 : expNegUpper (7866800450946730823823 / 101592158317621504000 : ℝ) ≤ (29356277847706855477890307 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (915591 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_226_1 : expNegUpper (3150704937726972088377 / 40636863327048601600 : ℝ) ≤ (212914411540443893435259801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366517 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_226 : rowCell 0 226 ≤ (3265139942330608868146549 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29356277847706855477890307 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (212914411540443893435259801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_226_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_226_1
  · norm_num [gridPoint]

theorem exp_0_227_0 : expNegUpper (28498241466426850676953 / 367561915255234662400 : ℝ) ≤ (10645718996641210877945887 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366517 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_227_1 : expNegUpper (35667963992802729217959 / 459452394069043328000 : ℝ) ≤ (9649076537786631746054547 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1833993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_227 : rowCell 0 227 ≤ (29598294479516824933139383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10645718996641210877945887 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9649076537786631746054547 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_227_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_227_1
  · norm_num [gridPoint]

theorem exp_0_228_0 : expNegUpper (35846003388304780966791 / 461745785285228672000 : ℝ) ≤ (96490751195710753534545713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1833993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_228_1 : expNegUpper (143566000081479410602843 / 1846983141140914688000 : ℝ) ≤ (34974689887497834460417733 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (367081 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_228 : rowCell 0 228 ≤ (536486271640949010533699 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (96490751195710753534545713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34974689887497834460417733 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_228_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_228_1
  · norm_num [gridPoint]

theorem exp_0_229_0 : expNegUpper (641248163433930724467 / 8249686863606272000 : ℝ) ≤ (8743671199453239710052027 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (367081 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_229_1 : expNegUpper (321031476713017493109 / 4124843431803136000 : ℝ) ≤ (7921368451095134542581261 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (918411 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_229 : rowCell 0 229 ≤ (303807415953637122514253 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8743671199453239710052027 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7921368451095134542581261 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_229_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_229_1
  · norm_num [gridPoint]

theorem exp_0_230_0 : expNegUpper (72590843491359383763781 / 932699392893831424000 : ℝ) ≤ (3168546923887925384855441 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (918411 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_230_1 : expNegUpper (145366359281684947489521 / 1865398785787662848000 : ℝ) ≤ (143494581325673509466872027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1838243 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_230 : rowCell 0 230 ≤ (1376026138296577786012441 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3168546923887925384855441 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (143494581325673509466872027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_230_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_230_1
  · norm_num [gridPoint]

theorem exp_0_231_0 : expNegUpper (146086574175810834163689 / 1874640865569669632000 : ℝ) ≤ (28698912170683841412310733 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1838243 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_231_1 : expNegUpper (3656814858907482102583 / 46866021639241740800 : ℝ) ≤ (32484823162982392706314249 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839669 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_231 : rowCell 0 231 ≤ (19939042260837791595298867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28698912170683841412310733 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32484823162982392706314249 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_231_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_231_1
  · norm_num [gridPoint]

theorem exp_0_232_0 : expNegUpper (408320856511803499007 / 5233071621270643200 : ℝ) ≤ (32484818573928227616081927 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839669 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_232_1 : expNegUpper (16353653304115503163279 / 209322864850825728000 : ℝ) ≤ (117637541688050393341468827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1841099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_232 : rowCell 0 232 ≤ (18053523853831630525861947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32484818573928227616081927 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (117637541688050393341468827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_232_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_232_1
  · norm_num [gridPoint]

theorem exp_0_233_0 : expNegUpper (147908499480372690693119 / 1893193540050948608000 : ℝ) ≤ (29409381308131908035849167 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1841099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_233_1 : expNegUpper (74048612708122163658579 / 946596770025474304000 : ℝ) ≤ (53238102070726236586208229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842533 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_233 : rowCell 0 233 ≤ (16342574498129363714879963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29409381308131908035849167 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (53238102070726236586208229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_233_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_233_1
  · norm_num [gridPoint]

theorem exp_0_234_0 : expNegUpper (2976511151530395480891 / 38050082695004416000 : ℝ) ≤ (53238094696407954410750867 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842533 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_234_1 : expNegUpper (5960625655450093095013 / 76100165390008832000 : ℝ) ≤ (96352077548208381912362719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (460993 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_234 : rowCell 0 234 ≤ (14790419453860571106824603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (53238094696407954410750867 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (96352077548208381912362719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_234_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_234_1
  · norm_num [gridPoint]

theorem exp_0_235_0 : expNegUpper (16638521402781017380653 / 212426396417249792000 : ℝ) ≤ (3011002010377337191748781 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (460993 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_235_1 : expNegUpper (4164948267761171538141 / 53106599104312448000 : ℝ) ≤ (17434208029677094993868513 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (369083 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_235 : rowCell 0 235 ≤ (6691334831377172097499083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3011002010377337191748781 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17434208029677094993868513 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_235_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_235_1
  · norm_num [gridPoint]

theorem exp_0_236_0 : expNegUpper (1215096085630963585211 / 15493498702145408000 : ℝ) ≤ (87171028307886922488930143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (369083 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_236_1 : expNegUpper (194664160216816152309 / 2478959792343265280 : ℝ) ≤ (19711819538153146532381413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1846863 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_236 : rowCell 0 236 ≤ (12106204064171834773485071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (87171028307886922488930143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19711819538153146532381413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_236_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_236_1
  · norm_num [gridPoint]

theorem exp_0_237_0 : expNegUpper (6064049341939576207779 / 77222917947302727680 : ℝ) ≤ (3153890701866829299969277 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1846863 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_237_1 : expNegUpper (75897705482241001051793 / 965286474341284096000 : ℝ) ≤ (71302576128003310084608401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (369663 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_237 : rowCell 0 237 ≤ (10949061501007407650173771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3153890701866829299969277 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (71302576128003310084608401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_237_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_237_1
  · norm_num [gridPoint]

theorem exp_0_238_0 : expNegUpper (8474147744895420279993 / 107776383144714496000 : ℝ) ≤ (35651283314885009618028599 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (369663 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_238_1 : expNegUpper (16970023113454363810497 / 215552766289428992000 : ℝ) ≤ (64465665609541994196845879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1849771 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_238 : rowCell 0 238 ≤ (9900341474161784526414361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35651283314885009618028599 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64465665609541994196845879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_238_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_238_1
  · norm_num [gridPoint]

theorem exp_0_239_0 : expNegUpper (6138888087578504433257 / 77975987313316352000 : ℝ) ≤ (64465657104990635482079927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1849771 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_239_1 : expNegUpper (384172813325482453353 / 4873499207082272000 : ℝ) ≤ (14567906849174814755241467 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1851231 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_239 : rowCell 0 239 ≤ (2237528264410567898544173 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (64465657104990635482079927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14567906849174814755241467 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_239_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_239_1
  · norm_num [gridPoint]

theorem exp_0_240_0 : expNegUpper (9650866992803949331137 / 122427956710419488000 : ℝ) ≤ (2330864791334100014362253 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1851231 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_240_1 : expNegUpper (154612172884131769972831 / 1958847307366711808000 : ℝ) ≤ (263306716628382780551593 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (231587 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_240 : rowCell 0 240 ≤ (4044665668122221033019871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2330864791334100014362253 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (263306716628382780551593 / 5000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_240_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_240_1
  · norm_num [gridPoint]

theorem exp_0_241_0 : expNegUpper (17262186498517549685471 / 218701974467363328000 : ℝ) ≤ (5266133651145774982318039 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (231587 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_241_1 : expNegUpper (1728437340836047632427 / 21870197446736332800 : ℝ) ≤ (47580993616532943261524863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (370833 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_241 : rowCell 0 241 ≤ (3654880387200777853187513 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5266133651145774982318039 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47580993616532943261524863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_241_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_241_1
  · norm_num [gridPoint]

theorem exp_0_242_0 : expNegUpper (15630963198718553117363 / 197781107135158323200 : ℝ) ≤ (23790493759364694386905233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (370833 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_242_1 : expNegUpper (156510698695869178907061 / 1977811071351583232000 : ℝ) ≤ (42981596182728948675036817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (927819 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_242 : rowCell 0 242 ≤ (1650976242082909061436249 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23790493759364694386905233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42981596182728948675036817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_242_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_242_1
  · norm_num [gridPoint]

theorem exp_0_243_0 : expNegUpper (157263742378784588040429 / 1987327210802651648000 : ℝ) ≤ (42981590727056395075539259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (927819 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_243_1 : expNegUpper (39366549234586273166947 / 496831802700662912000 : ℝ) ≤ (38818584559495598892538111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (371423 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_243 : rowCell 0 243 ≤ (5964942274240355411709283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42981590727056395075539259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38818584559495598892538111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_243_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_243_1
  · norm_num [gridPoint]

theorem exp_0_244_0 : expNegUpper (175802244059770849443 / 2218740209510528000 : ℝ) ≤ (3881857967925433327307347 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (371423 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_244_1 : expNegUpper (704114957311158555243 / 8874960838042112000 : ℝ) ≤ (17525710679010120524276977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1858597 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_244 : rowCell 0 244 ≤ (5386666843217118885908439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3881857967925433327307347 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17525710679010120524276977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_244_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_244_1
  · norm_num [gridPoint]

theorem exp_0_245_0 : expNegUpper (159184473804551707277507 / 2006428004622053888000 : ℝ) ≤ (3505141699333400370759513 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1858597 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_245_1 : expNegUpper (79694857029102286210893 / 1003214002311026944000 : ℝ) ≤ (15821622192904101976690247 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1860083 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_245 : rowCell 0 245 ≤ (2431717314375941302857769 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3505141699333400370759513 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15821622192904101976690247 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_245_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_245_1
  · norm_num [gridPoint]

theorem exp_0_246_0 : expNegUpper (80075557411698531552957 / 1008006329495193856000 : ℝ) ≤ (1582162024146899323907299 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1860083 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_246_1 : expNegUpper (32071550584053086374637 / 403202531798077542400 : ℝ) ≤ (7140135697689619342248603 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1861573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_246 : rowCell 0 246 ≤ (548764245706810138175027 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1582162024146899323907299 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7140135697689619342248603 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_246_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_246_1
  · norm_num [gridPoint]

theorem exp_0_247_0 : expNegUpper (3580487837837077304733 / 45013781148099481600 : ℝ) ≤ (28560539301484001187530003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1861573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_247_1 : expNegUpper (2240694332965720833513 / 28133613217562176000 : ℝ) ≤ (25772860788464679310930979 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1863067 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_247 : rowCell 0 247 ≤ (3962040349723201095215411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28560539301484001187530003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25772860788464679310930979 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_247_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_247_1
  · norm_num [gridPoint]

theorem exp_0_248_0 : expNegUpper (20262124679338075103473 / 254406310330540096000 : ℝ) ≤ (25772857669527026870329741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1863067 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_248_1 : expNegUpper (162306441210342623570103 / 2035250482644320768000 : ℝ) ≤ (23252526719956531029924209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (932283 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_248 : rowCell 0 248 ≤ (357497507592492846872057 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25772857669527026870329741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23252526719956531029924209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_248_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_248_1
  · norm_num [gridPoint]

theorem exp_0_249_0 : expNegUpper (260922014418950521887 / 3271845843087872000 : ℝ) ≤ (23252523932556015124912237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (932283 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_249_1 : expNegUpper (130629688498428999419 / 1635922921543936000 : ℝ) ≤ (20974405361423979259109111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466517 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_249 : rowCell 0 249 ≤ (1612533709624404375317021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23252523932556015124912237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20974405361423979259109111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_249_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_249_1
  · norm_num [gridPoint]

theorem exp_0_250_0 : expNegUpper (9114430412579197305379 / 114143314417848576000 : ℝ) ≤ (10487201435383946772114579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466517 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_250_1 : expNegUpper (18252445578216824872549 / 228286628835697152000 : ℝ) ≤ (18915671569264056483388651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (74703 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_250 : rowCell 0 250 ≤ (1454410033452942256109497 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10487201435383946772114579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18915671569264056483388651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_250_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_250_1
  · norm_num [gridPoint]

theorem exp_0_251_0 : expNegUpper (165047472670787673509189 / 2064278505418383872000 : ℝ) ≤ (18915669344159456746880641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (74703 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_251_1 : expNegUpper (8263057497271339701837 / 103213925270919193600 : ℝ) ≤ (17055603493864479876733089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (934543 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_251 : rowCell 0 251 ≤ (1311528766644572935362237 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18915669344159456746880641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17055603493864479876733089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_251_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_251_1
  · norm_num [gridPoint]

theorem exp_0_252_0 : expNegUpper (8301972236863454447277 / 103700009481062425600 : ℝ) ≤ (852780075317580286079821 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (934543 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_252_1 : expNegUpper (166254539839801006554211 / 2074000189621248512000 : ℝ) ≤ (3843848433662677822759693 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1870601 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_252 : rowCell 0 252 ≤ (47297946203923515891611 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (852780075317580286079821 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3843848433662677822759693 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_252_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_252_1
  · norm_num [gridPoint]

theorem exp_0_253_0 : expNegUpper (18559519290912049392771 / 231527190236652032000 : ℝ) ≤ (15375391959673075568880173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1870601 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_253_1 : expNegUpper (9291788326634039340801 / 115763595118326016000 : ℝ) ≤ (6928988468898344662794953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (46803 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_253 : rowCell 0 253 ≤ (133232720272397754787291 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15375391959673075568880173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6928988468898344662794953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_253_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_253_1
  · norm_num [gridPoint]

theorem exp_0_254_0 : expNegUpper (3360723386118887740129 / 41870241458884864000 : ℝ) ≤ (69289876764521208825399 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (46803 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_254_1 : expNegUpper (6730164402264021820257 / 83740482917769728000 : ℝ) ≤ (6243936228658013380360673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1873643 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_254 : rowCell 0 254 ≤ (480290723104725993918481 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (69289876764521208825399 / 5000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6243936228658013380360673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_254_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_254_1
  · norm_num [gridPoint]

theorem exp_0_255_0 : expNegUpper (169040941792815563089137 / 2103302272064373248000 : ℝ) ≤ (12487871042398142168804443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1873643 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_255_1 : expNegUpper (661173087358215489841 / 8216024500251458000 : ℝ) ≤ (11251040810654183033868073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1875171 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_255 : rowCell 0 255 ≤ (346212556050638706095461 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12487871042398142168804443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11251040810654183033868073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_255_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_255_1
  · norm_num [gridPoint]

theorem sum_0_224_2 : blockSum (rowCell 0) 224 2 ≤ (4732324512881405971190709 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_224) (by simpa only [blockSum_one] using cell_0_225) (by norm_num)

theorem sum_0_226_2 : blockSum (rowCell 0) 226 2 ≤ (62249693902822913614604873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_226) (by simpa only [blockSum_one] using cell_0_227) (by norm_num)

theorem sum_0_224_4 : blockSum (rowCell 0) 224 4 ≤ (137966886108925409153656217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_224_2 sum_0_226_2 (by norm_num)

theorem sum_0_228_2 : blockSum (rowCell 0) 228 2 ≤ (5112890685833842032782519 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_228) (by simpa only [blockSum_one] using cell_0_229) (by norm_num)

theorem sum_0_230_2 : blockSum (rowCell 0) 230 2 ≤ (41955460473583036171497923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_230) (by simpa only [blockSum_one] using cell_0_231) (by norm_num)

theorem sum_0_228_4 : blockSum (rowCell 0) 228 4 ≤ (93084367331921456499323113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_228_2 sum_0_230_2 (by norm_num)

theorem sum_0_224_8 : blockSum (rowCell 0) 224 8 ≤ (23105125344084686565297933 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_224_4 sum_0_228_4 (by norm_num)

theorem sum_0_232_2 : blockSum (rowCell 0) 232 2 ≤ (3439609835196099424074191 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_232) (by simpa only [blockSum_one] using cell_0_233) (by norm_num)

theorem sum_0_234_2 : blockSum (rowCell 0) 234 2 ≤ (28173089116614915301822769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_234) (by simpa only [blockSum_one] using cell_0_235) (by norm_num)

theorem sum_0_232_4 : blockSum (rowCell 0) 232 4 ≤ (62569187468575909542564679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_232_2 sum_0_234_2 (by norm_num)

theorem sum_0_236_2 : blockSum (rowCell 0) 236 2 ≤ (11527632782589621211829421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_236) (by simpa only [blockSum_one] using cell_0_237) (by norm_num)

theorem sum_0_238_2 : blockSum (rowCell 0) 238 2 ≤ (18850454531804056120591053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_238) (by simpa only [blockSum_one] using cell_0_239) (by norm_num)

theorem sum_0_236_4 : blockSum (rowCell 0) 236 4 ≤ (8381144019396659708849979 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_236_2 sum_0_238_2 (by norm_num)

theorem sum_0_232_8 : blockSum (rowCell 0) 232 8 ≤ (52237453782779604043407287 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_232_4 sum_0_236_4 (by norm_num)

theorem sum_0_224_16 : blockSum (rowCell 0) 224 16 ≤ (20970385062900379608737119 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_224_8 sum_0_232_8 (by norm_num)

theorem sum_0_240_2 : blockSum (rowCell 0) 240 2 ≤ (962443256915374860775923 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_240) (by simpa only [blockSum_one] using cell_0_241) (by norm_num)

theorem sum_0_242_2 : blockSum (rowCell 0) 242 2 ≤ (12568847242571991657454279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_242) (by simpa only [blockSum_one] using cell_0_243) (by norm_num)

theorem sum_0_240_4 : blockSum (rowCell 0) 240 4 ≤ (27967939353217989429869047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_240_2 sum_0_242_2 (by norm_num)

theorem sum_0_244_2 : blockSum (rowCell 0) 244 2 ≤ (10250101471969001491623977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_244) (by simpa only [blockSum_one] using cell_0_245) (by norm_num)

theorem sum_0_246_2 : blockSum (rowCell 0) 246 2 ≤ (8352154315377682200615627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_246) (by simpa only [blockSum_one] using cell_0_247) (by norm_num)

theorem sum_0_244_4 : blockSum (rowCell 0) 244 4 ≤ (4650563946836670923059901 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_244_2 sum_0_246_2 (by norm_num)

theorem sum_0_240_8 : blockSum (rowCell 0) 240 8 ≤ (46570195140564673122108651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_240_4 sum_0_244_4 (by norm_num)

theorem sum_0_248_2 : blockSum (rowCell 0) 248 2 ≤ (1700010623793434304838653 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_248) (by simpa only [blockSum_one] using cell_0_249) (by norm_num)

theorem sum_0_250_2 : blockSum (rowCell 0) 250 2 ≤ (1382969400048757595735867 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_250) (by simpa only [blockSum_one] using cell_0_251) (by norm_num)

theorem sum_0_248_4 : blockSum (rowCell 0) 248 4 ≤ (77074500596054797514363 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_248_2 sum_0_250_2 (by norm_num)

theorem sum_0_252_2 : blockSum (rowCell 0) 252 2 ≤ (2248310417277269935588603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_252) (by simpa only [blockSum_one] using cell_0_253) (by norm_num)

theorem sum_0_254_2 : blockSum (rowCell 0) 254 2 ≤ (3652225672672097506151229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_254) (by simpa only [blockSum_one] using cell_0_255) (by norm_num)

theorem sum_0_252_4 : blockSum (rowCell 0) 252 4 ≤ (1629769301445327475465687 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_252_2 sum_0_254_2 (by norm_num)

theorem sum_0_248_8 : blockSum (rowCell 0) 248 8 ≤ (4096153320519080995925303 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_248_4 sum_0_252_4 (by norm_num)

theorem sum_0_240_16 : blockSum (rowCell 0) 240 16 ≤ (33525480871580039050867583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_240_8 sum_0_248_8 (by norm_num)

theorem sum_0_224_32 : blockSum (rowCell 0) 224 32 ≤ (40257712274956615184152907 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_224_16 sum_0_240_16 (by norm_num)

#print axioms sum_0_224_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
