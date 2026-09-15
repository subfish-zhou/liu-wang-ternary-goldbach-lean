import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_192_0 : (5704435505321528855006303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (194143200797604256049 / 2392375131012096000 : ℝ) := by
  apply lower_of_taylor (t := (1885119 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_192 : (20798628106341009820907 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 192 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5704435505321528855006303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_192_0
  · norm_num [gridPoint]

theorem exp_7_193_0 : (212693398957159313239431 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (31259851672815619903053 / 384873577002763264000 : ℝ) := by
  apply lower_of_taylor (t := (943077 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_193 : (775489687184084134711989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 193 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (212693398957159313239431 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_193_0
  · norm_num [gridPoint]

theorem exp_7_194_0 : (4954468620558388474524279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6291541690196289647309 / 77394568524005990400 : ℝ) := by
  apply lower_of_taylor (t := (471799 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_194 : (722568606183037940978911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 194 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (4954468620558388474524279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_194_0
  · norm_num [gridPoint]

theorem exp_7_195_0 : (2307242872803743654219503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (15828242480099413825291 / 194538908906867712000 : ℝ) := by
  apply lower_of_taylor (t := (377649 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_195 : (672984892793470087516501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 195 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2307242872803743654219503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_195_0
  · norm_num [gridPoint]

theorem exp_7_196_0 : (4296097541355362244897201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3185618369855241982743 / 39118850258387968000 : ℝ) := by
  apply lower_of_taylor (t := (18893 / 10000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_196 : (626550584981535652712341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 196 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (4296097541355362244897201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_196_0
  · norm_num [gridPoint]

theorem exp_7_197_0 : (3998075337178234190475811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6411361432825377289871 / 78660979386092544000 : ℝ) := by
  apply lower_of_taylor (t := (1890361 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_197 : (583086491215695166478553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 197 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3998075337178234190475811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_197_0
  · norm_num [gridPoint]

theorem exp_7_198_0 : (1859624400120494686891183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (32258357855006889198623 / 395427000853484544000 : ℝ) := by
  apply lower_of_taylor (t := (1891429 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_198 : (542421928052333823300201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 198 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1859624400120494686891183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_198_0
  · norm_num [gridPoint]

theorem exp_7_199_0 : (3458504102720112232172991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (64921676538554179515 / 795109628705890304 : ℝ) := by
  apply lower_of_taylor (t := (1892503 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_199 : (31524653302516296446361 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 199 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3458504102720112232172991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_199_0
  · norm_num [gridPoint]

theorem exp_7_200_0 : (642956413145696671098161 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8166062726255537452063 / 99922084357211136000 : ℝ) := by
  apply lower_of_taylor (t := (118349 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_200 : (117212398256841592108327 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 200 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (642956413145696671098161 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_200_0
  · norm_num [gridPoint]

theorem exp_7_201_0 : (149353814463035618592091 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6573719652065346206629 / 80365514016236544000 : ℝ) := by
  apply lower_of_taylor (t := (1894671 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_201 : (217820286714244778825977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 201 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (149353814463035618592091 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_201_0
  · norm_num [gridPoint]

theorem exp_7_202_0 : (2774431276660906573823381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6614776566655099022889 / 80794502461991936000 : ℝ) := by
  apply lower_of_taylor (t := (379153 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_202 : (404628042694426864792901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 202 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2774431276660906573823381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_202_0
  · norm_num [gridPoint]

theorem exp_7_203_0 : (1287970280667114224876213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (16640053560976551867209 / 203061582057587712000 : ℝ) := by
  apply lower_of_taylor (t := (59277 / 31250 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_203 : (375679800108180024553639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 203 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1287970280667114224876213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_203_0
  · norm_num [gridPoint]

theorem exp_7_204_0 : (1195372421340055129060663 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3348727362444421857533 / 40827952549682995200 : ℝ) := by
  apply lower_of_taylor (t := (189797 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_204 : (174335261863053235433767 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 204 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1195372421340055129060663 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_204_0
  · norm_num [gridPoint]

theorem exp_7_205_0 : (2218030137519085825258131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (33695384838833501319447 / 410441596454923264000 : ℝ) := by
  apply lower_of_taylor (t := (1899083 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_205 : (80870375194671707840747 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 205 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2218030137519085825258131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_205_0
  · norm_num [gridPoint]

theorem exp_7_206_0 : (1028512976308544257626487 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6780888652641122729807 / 82521875397891072000 : ℝ) := by
  apply lower_of_taylor (t := (1900201 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_206 : (300000361148184797895419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 206 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1028512976308544257626487 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_206_0
  · norm_num [gridPoint]

theorem exp_7_207_0 : (953501741640352627467741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (852861284891130431159 / 10369571677510656000 : ℝ) := by
  apply lower_of_taylor (t := (950663 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_207 : (55624162929708414879409 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 207 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (953501741640352627467741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_207_0
  · norm_num [gridPoint]

theorem exp_7_208_0 : (88363692120199498683541 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4290676466779621724211 / 52120258348479488000 : ℝ) := by
  apply lower_of_taylor (t := (237807 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_208 : (64435598186595866857409 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 208 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (88363692120199498683541 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_208_0
  · norm_num [gridPoint]

theorem exp_7_209_0 : (1637186323791538827814237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6907465355413108994657 / 83829395210336870400 : ℝ) := by
  apply lower_of_taylor (t := (1903593 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_209 : (238770195280933585569759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 209 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1637186323791538827814237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_209_0
  · norm_num [gridPoint]

theorem exp_7_210_0 : (2961184966919816104529 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (34750199022215592467417 / 421337594891971584000 : ℝ) := by
  apply lower_of_taylor (t := (59523 / 31250 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_210 : (55278660666217397085321 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 210 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2961184966919816104529 / 1953125000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_210_0
  · norm_num [gridPoint]

theorem exp_7_211_0 : (1403515578959666143667707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (699280619355435559167 / 8470678466173952000 : ℝ) := by
  apply lower_of_taylor (t := (381177 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_211 : (1023456169887668267713 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 211 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1403515578959666143667707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_211_0
  · norm_num [gridPoint]

theorem exp_7_212_0 : (649403378712877920444201 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (703576502236375262567 / 8514719226037248000 : ℝ) := by
  apply lower_of_taylor (t := (1907039 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_212 : (189420311296364481240191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 212 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (649403378712877920444201 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_212_0
  · norm_num [gridPoint]

theorem exp_7_213_0 : (600742840208930988206491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (35394583952441209659683 / 427943708871465984000 : ℝ) := by
  apply lower_of_taylor (t := (9541 / 5000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_213 : (10951676909482686967863 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 213 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (600742840208930988206491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_213_0
  · norm_num [gridPoint]

theorem exp_7_214_0 : (555533950508019103720453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7122261997544755846923 / 86031433203501670400 : ℝ) := by
  apply lower_of_taylor (t := (1909367 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_214 : (32408027826862730073367 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 214 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (555533950508019103720453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_214_0
  · norm_num [gridPoint]

theorem exp_7_215_0 : (1027097606054224361534437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8957251428937783383853 / 108094083184997376000 : ℝ) := by
  apply lower_of_taylor (t := (1910539 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_215 : (149793760432958959570581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 215 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1027097606054224361534437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_215_0
  · norm_num [gridPoint]

theorem exp_7_216_0 : (949146187166253800643529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1802383681730396712217 / 21730060451945472000 : ℝ) := by
  apply lower_of_taylor (t := (955859 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_216 : (2768503708667630372963 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 216 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (949146187166253800643529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_216_0
  · norm_num [gridPoint]

theorem exp_7_217_0 : (109601357606087888593833 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7253463248475768608733 / 87366358982853632000 : ℝ) := by
  apply lower_of_taylor (t := (956451 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_217 : (25575134293138089778719 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 217 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (109601357606087888593833 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_217_0
  · norm_num [gridPoint]

theorem exp_7_218_0 : (161942667574881215122721 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (36487936037148521615653 / 439068090366065664000 : ℝ) := by
  apply lower_of_taylor (t := (478523 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_218 : (23618009629851475028181 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 218 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (161942667574881215122721 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_218_0
  · norm_num [gridPoint]

theorem exp_7_219_0 : (46718658884289629647027 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3670953551700163164257 / 44131009539430195200 : ℝ) := by
  apply lower_of_taylor (t := (239411 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_219 : (109016530548399716730411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 219 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (46718658884289629647027 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_219_0
  · norm_num [gridPoint]

theorem exp_7_220_0 : (137966675776481621030797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (595679309355207013011 / 7154158225789952000 : ℝ) := by
  apply lower_of_taylor (t := (191649 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_220 : (100606539520563077382721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 220 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (137966675776481621030797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_220_0
  · norm_num [gridPoint]

theorem exp_7_221_0 : (636405551762768867402941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (239714087253527695421 / 2876201510839296000 : ℝ) := by
  apply lower_of_taylor (t := (1917697 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_221 : (92814529210308035347353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 221 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (636405551762768867402941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_221_0
  · norm_num [gridPoint]

theorem exp_7_222_0 : (586922428626718264175843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7476047409581633455111 / 89614073587528704000 : ℝ) := by
  apply lower_of_taylor (t := (191891 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_222 : (17119564323431906056357 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 222 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (586922428626718264175843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_222_0
  · norm_num [gridPoint]

theorem exp_7_223_0 : (541109954992607531760613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2350361265558851246553 / 28145950704477184000 : ℝ) := by
  apply lower_of_taylor (t := (1920129 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_223 : (39458224071536129886813 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 223 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (541109954992607531760613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_223_0
  · norm_num [gridPoint]

theorem sum_7_192_2 : (1607434811437724527548269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 192 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_192) (by simpa only [blockSum_one] using cell_7_193) (by norm_num)

theorem sum_7_194_2 : (348888374744127007123853 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 194 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_194) (by simpa only [blockSum_one] using cell_7_195) (by norm_num)

theorem sum_7_192_4 : (3002988310414232556043681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 192 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_192_2 sum_7_194_2 (by norm_num)

theorem sum_7_196_2 : (604818538098615409595447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 196 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_196) (by simpa only [blockSum_one] using cell_7_197) (by norm_num)

theorem sum_7_198_2 : (1046816380892594566441977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 198 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_198) (by simpa only [blockSum_one] using cell_7_199) (by norm_num)

theorem sum_7_196_4 : (2256453457089825385632871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 196 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_196_2 sum_7_198_2 (by norm_num)

theorem sum_7_192_8 : (657430220938007242709569 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 192 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_192_4 sum_7_196_4 (by norm_num)

theorem sum_7_200_2 : (452245083227927963042631 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 200 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_200) (by simpa only [blockSum_one] using cell_7_201) (by norm_num)

theorem sum_7_202_2 : (39015392140130344467327 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 202 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_202) (by simpa only [blockSum_one] using cell_7_203) (by norm_num)

theorem sum_7_200_4 : (842399004629231407715901 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 200 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_200_2 sum_7_202_2 (by norm_num)

theorem sum_7_204_2 : (336076012252396651115261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 204 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_204) (by simpa only [blockSum_one] using cell_7_205) (by norm_num)

theorem sum_7_206_2 : (36132573487295429518279 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 206 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_206) (by simpa only [blockSum_one] using cell_7_207) (by norm_num)

theorem sum_7_204_4 : (625136600150760087261493 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 204 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_204_2 sum_7_206_2 (by norm_num)

theorem sum_7_200_8 : (733767802389995747488697 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 200 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_200_4 sum_7_204_4 (by norm_num)

theorem sum_7_192_16 : (409725648853202046581567 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 192 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_192_8 sum_7_200_8 (by norm_num)

theorem sum_7_208_2 : (99302517605463410599879 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 208 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_208) (by simpa only [blockSum_one] using cell_7_209) (by norm_num)

theorem sum_7_210_2 : (106451469160600810470971 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 210 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_210) (by simpa only [blockSum_one] using cell_7_211) (by norm_num)

theorem sum_7_208_4 : (922318464669720294883279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 208 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_208_2 sum_7_210_2 (by norm_num)

theorem sum_7_212_2 : (364647141848087472725999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 212 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_212) (by simpa only [blockSum_one] using cell_7_213) (by norm_num)

theorem sum_7_214_2 : (38979237445909076242177 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 214 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_214) (by simpa only [blockSum_one] using cell_7_215) (by norm_num)

theorem sum_7_212_4 : (135296208283072016532683 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 212 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_212_2 sum_7_214_2 (by norm_num)

theorem sum_7_208_8 : (799399753042540188773347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 208 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_208_4 sum_7_212_4 (by norm_num)

theorem sum_7_216_2 : (53260171379814393508349 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 216 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_216) (by simpa only [blockSum_one] using cell_7_217) (by norm_num)

theorem sum_7_218_2 : (56776644674414272967829 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 218 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_218) (by simpa only [blockSum_one] using cell_7_219) (by norm_num)

theorem sum_7_216_4 : (493407435596729059413061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 216 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_216_2 sum_7_218_2 (by norm_num)

theorem sum_7_220_2 : (96710534365435556365037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 220 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_220) (by simpa only [blockSum_one] using cell_7_221) (by norm_num)

theorem sum_7_222_2 : (164514269760231790055411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 222 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_222) (by simpa only [blockSum_one] using cell_7_223) (by norm_num)

theorem sum_7_220_4 : (71587067698220580557097 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 220 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_220_2 sum_7_222_2 (by norm_num)

theorem sum_7_216_8 : (425671387043915981099273 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 216 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_216_4 sum_7_220_4 (by norm_num)

theorem sum_7_208_16 : (61253557004322808493631 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 208 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_208_8 sum_7_216_8 (by norm_num)

theorem sum_7_192_32 : (532232762861847663568829 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 192 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_192_16 sum_7_208_16 (by norm_num)

#print axioms sum_7_192_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
