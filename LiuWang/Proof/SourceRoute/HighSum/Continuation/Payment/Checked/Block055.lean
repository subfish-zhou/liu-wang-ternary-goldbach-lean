import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_224_0 : expNegUpper (7427295796532273929 / 90521295575824000 : ℝ) ≤ (2325193592260088817853721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1898411 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_224_1 : expNegUpper (237921161094221090847 / 2896681458426368000 : ℝ) ≤ (42692593276113932622889 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11873 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_224 : rowCell 3 224 ≤ (325214318704773696545061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2325193592260088817853721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42692593276113932622889 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_224_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_224_1
  · norm_num [gridPoint]

theorem exp_3_225_0 : expNegUpper (149448576313731357470247 / 1819530961463955968000 : ℝ) ≤ (2134629259683902570613749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11873 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_225_1 : expNegUpper (74802356981909518594583 / 909765480731977984000 : ℝ) ≤ (979545852674195492002017 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950477 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_225 : rowCell 3 225 ≤ (29851781072258436720397 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2134629259683902570613749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (979545852674195492002017 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_225_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_225_1
  · norm_num [gridPoint]

theorem exp_3_226_0 : expNegUpper (8353067984340650823823 / 101592158317621504000 : ℝ) ≤ (244886417269617322267933 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950477 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_226_1 : expNegUpper (3344726502129864888377 / 40636863327048601600 : ℝ) ≤ (449362541932543821894137 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1902233 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_226 : rowCell 3 226 ≤ (34241297703380942317771 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (244886417269617322267933 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (449362541932543821894137 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_226_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_226_1
  · norm_num [gridPoint]

theorem exp_3_227_0 : expNegUpper (30253173627237039476953 / 367561915255234662400 : ℝ) ≤ (359489966837163846477911 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1902233 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_227_1 : expNegUpper (37856167893075369217959 / 459452394069043328000 : ℝ) ≤ (824327513860375568202787 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (951759 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_227 : rowCell 3 227 ≤ (251293062640063980476857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (359489966837163846477911 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (824327513860375568202787 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_227_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_227_1
  · norm_num [gridPoint]

theorem exp_3_228_0 : expNegUpper (38045129890057612966791 / 461745785285228672000 : ℝ) ≤ (1648654724822831925614749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (951759 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_228_1 : expNegUpper (152340660885530354602843 / 1846983141140914688000 : ℝ) ≤ (188966377835862539353989 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (238101 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_228 : rowCell 3 228 ≤ (230458168117479703248431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1648654724822831925614749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (188966377835862539353989 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_228_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_228_1
  · norm_num [gridPoint]

theorem exp_3_229_0 : expNegUpper (680440835478249444467 / 8249686863606272000 : ℝ) ≤ (1511730747693955167838509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (238101 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_229_1 : expNegUpper (340579267839709333109 / 4124843431803136000 : ℝ) ≤ (1385772740094759586862421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1906103 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_229 : rowCell 3 229 ≤ (42257711511068578017241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1511730747693955167838509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1385772740094759586862421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_229_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_229_1
  · norm_num [gridPoint]

theorem exp_3_230_0 : expNegUpper (77010941697825431763781 / 932699392893831424000 : ℝ) ≤ (692886245251488508406451 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1906103 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_230_1 : expNegUpper (154184710491656659489521 / 1865398785787662848000 : ℝ) ≤ (634969996415033671602523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1907403 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_230 : rowCell 3 230 ≤ (193656940276329839264551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (692886245251488508406451 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (634969996415033671602523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_230_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_230_1
  · norm_num [gridPoint]

theorem exp_3_231_0 : expNegUpper (154948615791703314163689 / 1874640865569669632000 : ℝ) ≤ (79371235397090565225951 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1907403 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_231_1 : expNegUpper (3877819769230784502583 / 46866021639241740800 : ℝ) ≤ (581726733486153272268769 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1908709 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_231 : rowCell 3 231 ≤ (44361305206461790899159 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (79371235397090565225951 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (581726733486153272268769 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_231_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_231_1
  · norm_num [gridPoint]

theorem exp_3_232_0 : expNegUpper (432998319897505899007 / 5233071621270643200 : ℝ) ≤ (1163453261524409482374663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1908709 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_232_1 : expNegUpper (17338324594770223163279 / 209322864850825728000 : ℝ) ≤ (266397657245454316254979 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1910019 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_232 : rowCell 3 232 ≤ (162543883152334431108107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1163453261524409482374663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (266397657245454316254979 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_232_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_232_1
  · norm_num [gridPoint]

theorem exp_3_233_0 : expNegUpper (156814231502185938693119 / 1893193540050948608000 : ℝ) ≤ (1065590442658957539419771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1910019 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_233_1 : expNegUpper (78490556117548595658579 / 946596770025474304000 : ℝ) ≤ (975681879606183708439477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (382267 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_233 : rowCell 3 233 ≤ (148851411695176134881737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1065590442658957539419771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (975681879606183708439477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_233_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_233_1
  · norm_num [gridPoint]

theorem exp_3_234_0 : expNegUpper (3155062696025868120891 / 38050082695004416000 : ℝ) ≤ (121960213833998986317043 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (382267 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_234_1 : expNegUpper (6316854936322623015013 / 76100165390008832000 : ℝ) ≤ (178621388435812303533661 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (119541 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_234 : rowCell 3 234 ≤ (6813687377785205519729 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (121960213833998986317043 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (178621388435812303533661 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_234_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_234_1
  · norm_num [gridPoint]

theorem exp_3_235_0 : expNegUpper (17632901672529241380653 / 212426396417249792000 : ℝ) ≤ (22327669726257171285251 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (119541 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_235_1 : expNegUpper (4412936524004883538141 / 53106599104312448000 : ℝ) ≤ (817291473367048130400059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (956991 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_235 : rowCell 3 235 ≤ (124723777981410957447991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22327669726257171285251 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (817291473367048130400059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_235_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_235_1
  · norm_num [gridPoint]

theorem exp_3_236_0 : expNegUpper (1287445018136563585211 / 15493498702145408000 : ℝ) ≤ (817291334600516169529421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (956991 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_236_1 : expNegUpper (206211802059053592309 / 2478959792343265280 : ℝ) ≤ (747703884814536395227221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1915313 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_236 : rowCell 3 236 ≤ (114120857450138076233343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (817291334600516169529421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (747703884814536395227221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_236_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_236_1
  · norm_num [gridPoint]

theorem exp_3_237_0 : expNegUpper (6423773855285767567779 / 77222917947302727680 : ℝ) ≤ (93462969886896425038809 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1915313 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_237_1 : expNegUpper (80383339297588201051793 / 965286474341284096000 : ℝ) ≤ (683852364539410256597741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1916649 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_237 : rowCell 3 237 ≤ (20878071739827704473241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (93462969886896425038809 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (683852364539410256597741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_237_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_237_1
  · norm_num [gridPoint]

theorem exp_3_238_0 : expNegUpper (8974978746929596279993 / 107776383144714496000 : ℝ) ≤ (683852250669240000116243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1916649 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_238_1 : expNegUpper (17969257872749339810497 / 215552766289428992000 : ℝ) ≤ (312641043670478040605623 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (191799 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_238 : rowCell 3 238 ≤ (95463252103085304285943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (683852250669240000116243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (312641043670478040605623 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_238_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_238_1
  · norm_num [gridPoint]

theorem exp_3_239_0 : expNegUpper (6500360217161526513257 / 77975987313316352000 : ℝ) ≤ (625281984229022629841969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (191799 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_239_1 : expNegUpper (406710208417020373353 / 4873499207082272000 : ℝ) ≤ (285786301946401175259719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1919337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_239 : rowCell 3 239 ≤ (17455142372977498654017 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (625281984229022629841969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (285786301946401175259719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_239_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_239_1
  · norm_num [gridPoint]

theorem exp_3_240_0 : expNegUpper (10217032520462445331137 / 122427956710419488000 : ℝ) ≤ (571572510545907932793893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1919337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_240_1 : expNegUpper (163648976123707321972831 / 1958847307366711808000 : ℝ) ≤ (522335398605684622021217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (120043 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_240 : rowCell 3 240 ≤ (39884373771610628740527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (571572510545907932793893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (522335398605684622021217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_240_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_240_1
  · norm_num [gridPoint]

theorem exp_3_241_0 : expNegUpper (18271130236906029685471 / 218701974467363328000 : ℝ) ≤ (522335314119906866935889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (120043 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_241_1 : expNegUpper (1829088990197558032427 / 21870197446736332800 : ℝ) ≤ (238605803377627367927951 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (480511 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_241 : rowCell 3 241 ≤ (3644392975032675392679 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (522335314119906866935889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (238605803377627367927951 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_241_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_241_1
  · norm_num [gridPoint]

theorem exp_3_242_0 : expNegUpper (16541197083564223517363 / 197781107135158323200 : ℝ) ≤ (477211530308170403427813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (480511 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_242_1 : expNegUpper (165591192341365498907061 / 1977811071351583232000 : ℝ) ≤ (108967470444289694247113 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (384681 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_242 : rowCell 3 242 ≤ (6658271691584337424889 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (477211530308170403427813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (108967470444289694247113 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_242_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_242_1
  · norm_num [gridPoint]

theorem exp_3_243_0 : expNegUpper (166387926430201676040429 / 1987327210802651648000 : ℝ) ≤ (87173962524143922848931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (384681 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_243_1 : expNegUpper (41642133946700449166947 / 496831802700662912000 : ℝ) ≤ (398004404033576726731937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1924771 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_243 : rowCell 3 243 ≤ (30403428531148907264191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (87173962524143922848931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (398004404033576726731937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_243_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_243_1
  · norm_num [gridPoint]

theorem exp_3_244_0 : expNegUpper (185964498786856929443 / 2218740209510528000 : ℝ) ≤ (398004341487585290528873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1924771 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_244_1 : expNegUpper (744666886428567835243 / 8874960838042112000 : ℝ) ≤ (363333022750943271913869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (963071 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_244 : rowCell 3 244 ≤ (55517404614311685826331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (398004341487585290528873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (363333022750943271913869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_244_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_244_1
  · norm_num [gridPoint]

theorem exp_3_245_0 : expNegUpper (168352348261889563277507 / 2006428004622053888000 : ℝ) ≤ (36333296619708048092311 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (963071 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_245_1 : expNegUpper (84267871656291022210893 / 1003214002311026944000 : ℝ) ≤ (20724720201027975922731 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (963759 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_245 : rowCell 3 245 ≤ (50674809797849176204131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36333296619708048092311 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20724720201027975922731 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_245_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_245_1
  · norm_num [gridPoint]

theorem exp_3_246_0 : expNegUpper (84670417241847651552957 / 1008006329495193856000 : ℝ) ≤ (331595472092807443833329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (963759 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_246_1 : expNegUpper (33905125475520657574637 / 403202531798077542400 : ℝ) ≤ (60510402340023221570103 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1928899 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_246 : rowCell 3 246 ≤ (2312130213002997779677 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (331595472092807443833329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (60510402340023221570103 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_246_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_246_1
  · norm_num [gridPoint]

theorem exp_3_247_0 : expNegUpper (3785189279242824504733 / 45013781148099481600 : ℝ) ≤ (6051039309924124698563 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1928899 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_247_1 : expNegUpper (2368329328247640833513 / 28133613217562176000 : ℝ) ≤ (275981410938957287456357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (386057 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_247 : rowCell 3 247 ≤ (21093586792866257509753 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6051039309924124698563 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (275981410938957287456357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_247_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_247_1
  · norm_num [gridPoint]

theorem exp_3_248_0 : expNegUpper (21416300937615451103473 / 254406310330540096000 : ℝ) ≤ (275981369191127661788277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (386057 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_248_1 : expNegUpper (171518006073601247570103 / 2035250482644320768000 : ℝ) ≤ (12584002968954407238297 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (77267 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_248 : rowCell 3 248 ≤ (19238772721077433833599 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (275981369191127661788277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12584002968954407238297 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_248_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_248_1
  · norm_num [gridPoint]

theorem exp_3_249_0 : expNegUpper (275730422849637549087 / 3271845843087872000 : ℝ) ≤ (251680021666352379896803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (77267 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_249_1 : expNegUpper (138016416551404205819 / 1635922921543936000 : ℝ) ≤ (57365101930098655279077 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1933071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_249 : rowCell 3 249 ≤ (7017038477097223693877 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (251680021666352379896803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (57365101930098655279077 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_249_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_249_1
  · norm_num [gridPoint]

theorem exp_3_250_0 : expNegUpper (9629824883253629305379 / 114143314417848576000 : ℝ) ≤ (45892074732122368265181 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1933071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_250_1 : expNegUpper (19280807274792312872549 / 228286628835697152000 : ℝ) ≤ (10457490332283208715809 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1934471 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_250 : rowCell 3 250 ≤ (31983848411767515980479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45892074732122368265181 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10457490332283208715809 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_250_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_250_1
  · norm_num [gridPoint]

theorem exp_3_251_0 : expNegUpper (174346418345887833509189 / 2064278505418383872000 : ℝ) ≤ (104574887946025735934587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1934471 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_251_1 : expNegUpper (8726912520878328501837 / 103213925270919193600 : ℝ) ≤ (38117875988386361855291 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (483969 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_251 : rowCell 3 251 ≤ (14574669192030940227747 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (104574887946025735934587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38117875988386361855291 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_251_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_251_1
  · norm_num [gridPoint]

theorem exp_3_252_0 : expNegUpper (8768011780766481647277 / 103700009481062425600 : ℝ) ≤ (190589352179879814871937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (483969 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_252_1 : expNegUpper (175553485514901166554211 / 2074000189621248512000 : ℝ) ≤ (173632977535771775697293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (968643 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_252 : rowCell 3 252 ≤ (5311883902772933578007 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (190589352179879814871937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (173632977535771775697293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_252_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_252_1
  · norm_num [gridPoint]

theorem exp_3_253_0 : expNegUpper (19597589966581041392771 / 231527190236652032000 : ℝ) ≤ (173632952479938017768363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (968643 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_253_1 : expNegUpper (9809610042081847340801 / 115763595118326016000 : ℝ) ≤ (158146203266303637813867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (19387 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_253 : rowCell 3 253 ≤ (6048408529962795572261 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (173632952479938017768363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (158146203266303637813867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_253_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_253_1
  · norm_num [gridPoint]

theorem exp_3_254_0 : expNegUpper (3548013011798513980129 / 41870241458884864000 : ℝ) ≤ (158146180657960379179729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (19387 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_254_1 : expNegUpper (7103869845504858940257 / 83740482917769728000 : ℝ) ≤ (28801102501940379349439 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1940119 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_254 : rowCell 3 254 ≤ (2754146616274720435271 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (158146180657960379179729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28801102501940379349439 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_254_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_254_1
  · norm_num [gridPoint]

theorem exp_3_255_0 : expNegUpper (178427268279757259089137 / 2103302272064373248000 : ℝ) ≤ (144005492114317000273889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1940119 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_255_1 : expNegUpper (697753092373767489841 / 8216024500251458000 : ℝ) ≤ (131097375047011653472459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1941543 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_255 : rowCell 3 255 ≤ (20060748236136300687397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (144005492114317000273889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (131097375047011653472459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_255_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_255_1
  · norm_num [gridPoint]

theorem sum_3_224_2 : blockSum (rowCell 3) 224 2 ≤ (623732129427358063749031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_224) (by simpa only [blockSum_one] using cell_3_225) (by norm_num)

theorem sum_3_226_2 : blockSum (rowCell 3) 226 2 ≤ (21008937770684460760761 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_226) (by simpa only [blockSum_one] using cell_3_227) (by norm_num)

theorem sum_3_224_4 : blockSum (rowCell 3) 224 4 ≤ (143619446711808697846007 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_224_2 sum_3_226_2 (by norm_num)

theorem sum_3_228_2 : blockSum (rowCell 3) 228 2 ≤ (110436681418205648333659 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_228) (by simpa only [blockSum_one] using cell_3_229) (by norm_num)

theorem sum_3_230_2 : blockSum (rowCell 3) 230 2 ≤ (371102161102177002861187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_230) (by simpa only [blockSum_one] using cell_3_231) (by norm_num)

theorem sum_3_228_4 : blockSum (rowCell 3) 228 4 ≤ (812848886774999596195823 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_228_2 sum_3_230_2 (by norm_num)

theorem sum_3_224_8 : blockSum (rowCell 3) 224 8 ≤ (1961804460469469178963879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_224_4 sum_3_228_4 (by norm_num)

theorem sum_3_232_2 : blockSum (rowCell 3) 232 2 ≤ (77848823711877641497461 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_232) (by simpa only [blockSum_one] using cell_3_233) (by norm_num)

theorem sum_3_234_2 : blockSum (rowCell 3) 234 2 ≤ (260997525537115067842571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_234) (by simpa only [blockSum_one] using cell_3_235) (by norm_num)

theorem sum_3_232_4 : blockSum (rowCell 3) 232 4 ≤ (114478564076925126766483 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_232_2 sum_3_234_2 (by norm_num)

theorem sum_3_236_2 : blockSum (rowCell 3) 236 2 ≤ (54627804037319149649887 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_236) (by simpa only [blockSum_one] using cell_3_237) (by norm_num)

theorem sum_3_238_2 : blockSum (rowCell 3) 238 2 ≤ (45684740991993199389007 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_238) (by simpa only [blockSum_one] using cell_3_239) (by norm_num)

theorem sum_3_236_4 : blockSum (rowCell 3) 236 4 ≤ (50156272514656174519447 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_236_2 sum_3_238_2 (by norm_num)

theorem sum_3_232_8 : blockSum (rowCell 3) 232 8 ≤ (973643000501875029987991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_232_4 sum_3_236_4 (by norm_num)

theorem sum_3_224_16 : blockSum (rowCell 3) 224 16 ≤ (293544746097134420895187 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_224_8 sum_3_232_8 (by norm_num)

theorem sum_3_240_2 : blockSum (rowCell 3) 240 2 ≤ (76328303521937382667317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_240) (by simpa only [blockSum_one] using cell_3_241) (by norm_num)

theorem sum_3_242_2 : blockSum (rowCell 3) 242 2 ≤ (15923696747267648597159 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_242) (by simpa only [blockSum_one] using cell_3_243) (by norm_num)

theorem sum_3_240_4 : blockSum (rowCell 3) 240 4 ≤ (140023090511007977055953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_240_2 sum_3_242_2 (by norm_num)

theorem sum_3_244_2 : blockSum (rowCell 3) 244 2 ≤ (53096107206080431015231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_244) (by simpa only [blockSum_one] using cell_3_245) (by norm_num)

theorem sum_3_246_2 : blockSum (rowCell 3) 246 2 ≤ (44214888922896235306523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_246) (by simpa only [blockSum_one] using cell_3_247) (by norm_num)

theorem sum_3_244_4 : blockSum (rowCell 3) 244 4 ≤ (48655498064488333160877 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_244_2 sum_3_246_2 (by norm_num)

theorem sum_3_240_8 : blockSum (rowCell 3) 240 8 ≤ (237334086639984643377707 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_240_4 sum_3_244_4 (by norm_num)

theorem sum_3_248_2 : blockSum (rowCell 3) 248 2 ≤ (73562737827640986136583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_248) (by simpa only [blockSum_one] using cell_3_249) (by norm_num)

theorem sum_3_250_2 : blockSum (rowCell 3) 250 2 ≤ (61133186795829396435973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_250) (by simpa only [blockSum_one] using cell_3_251) (by norm_num)

theorem sum_3_248_4 : blockSum (rowCell 3) 248 4 ≤ (33673981155867595643139 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_248_2 sum_3_250_2 (by norm_num)

theorem sum_3_252_2 : blockSum (rowCell 3) 252 2 ≤ (50753053633715850179079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_252) (by simpa only [blockSum_one] using cell_3_253) (by norm_num)

theorem sum_3_254_2 : blockSum (rowCell 3) 254 2 ≤ (8418784233266812833913 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_254) (by simpa only [blockSum_one] using cell_3_255) (by norm_num)

theorem sum_3_252_4 : blockSum (rowCell 3) 252 4 ≤ (23211743700012478587161 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_252_2 sum_3_254_2 (by norm_num)

theorem sum_3_248_8 : blockSum (rowCell 3) 248 8 ≤ (568857248558800742303 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_248_4 sum_3_252_4 (by norm_num)

theorem sum_3_240_16 : blockSum (rowCell 3) 240 16 ≤ (351105536351744791838307 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_240_8 sum_3_248_8 (by norm_num)

theorem sum_3_224_32 : blockSum (rowCell 3) 224 32 ≤ (909414633418708448157121 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_224_16 sum_3_240_16 (by norm_num)

#print axioms sum_3_224_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
