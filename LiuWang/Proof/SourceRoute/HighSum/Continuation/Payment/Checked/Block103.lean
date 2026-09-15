import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_224_0 : expNegUpper (7548255868687409929 / 90521295575824000 : ℝ) ≤ (611122624003007347830429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (959167 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_224_1 : expNegUpper (241782174424091938847 / 2896681458426368000 : ℝ) ≤ (281460490073014751390779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (383913 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_224 : rowCell 6 224 ≤ (42806157209674184898461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (611122624003007347830429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (281460490073014751390779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_224_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_224_1
  · norm_num [gridPoint]

theorem exp_6_225_0 : expNegUpper (151873845868767517470247 / 1819530961463955968000 : ℝ) ≤ (140730216913726080411781 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (383913 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_225_1 : expNegUpper (76011957703460878594583 / 909765480731977984000 : ℝ) ≤ (518355871935022288665279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1920803 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_225 : rowCell 6 225 ≤ (7884767131046817374867 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (140730216913726080411781 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (518355871935022288665279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_225_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_225_1
  · norm_num [gridPoint]

theorem exp_6_226_0 : expNegUpper (76393280692550657414407 / 914329424858593536000 : ℝ) ≤ (64794471172795764415877 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1920803 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_226_1 : expNegUpper (30587592430176015995393 / 365731769943437414400 : ℝ) ≤ (477167930470659419732193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (384409 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_226 : rowCell 6 226 ≤ (72594482609106708719147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (64794471172795764415877 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (477167930470659419732193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_226_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_226_1
  · norm_num [gridPoint]

theorem exp_6_227_0 : expNegUpper (30740654783017647476953 / 367561915255234662400 : ℝ) ≤ (477167837005644657776221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (384409 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_227_1 : expNegUpper (38464002309817769217959 / 459452394069043328000 : ℝ) ≤ (219557431404691672770417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (961647 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_227 : rowCell 6 227 ≤ (33408078846624978533051 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (477167837005644657776221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (219557431404691672770417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_227_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_227_1
  · norm_num [gridPoint]

theorem exp_6_228_0 : expNegUpper (38655998362766732966791 / 461745785285228672000 : ℝ) ≤ (439114777651329215838671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (961647 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_228_1 : expNegUpper (154778066664433394602843 / 1846983141140914688000 : ℝ) ≤ (100992637511029581860301 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (481137 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_228 : rowCell 6 228 ≤ (61478539555026136234621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (439114777651329215838671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (100992637511029581860301 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_228_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_228_1
  · norm_num [gridPoint]

theorem exp_6_229_0 : expNegUpper (6221949199415041800203 / 74247181772456448000 : ℝ) ≤ (403970472476969860789407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (481137 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_229_1 : expNegUpper (3114082888374113597981 / 37123590886228224000 : ℝ) ≤ (92881018307111344044047 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1925807 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_229 : rowCell 6 229 ≤ (28274879503109893144267 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (403970472476969860789407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (92881018307111344044047 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_229_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_229_1
  · norm_num [gridPoint]

theorem exp_6_230_0 : expNegUpper (78238746755177111763781 / 932699392893831424000 : ℝ) ≤ (371524002595661763429537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1925807 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_230_1 : expNegUpper (156634252494426579489521 / 1865398785787662848000 : ℝ) ≤ (42697348601844848209789 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (60221 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_230 : rowCell 6 230 ≤ (52000096227937024240657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (371524002595661763429537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42697348601844848209789 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_230_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_230_1
  · norm_num [gridPoint]

theorem exp_6_231_0 : expNegUpper (157410294018340114163689 / 1874640865569669632000 : ℝ) ≤ (85394681128645780123999 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (60221 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_231_1 : expNegUpper (3939210022098368502583 / 46866021639241740800 : ℝ) ≤ (78487862973188944731171 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (964171 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_231 : rowCell 6 231 ≤ (47801849416516018514299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (85394681128645780123999 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (78487862973188944731171 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_231_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_231_1
  · norm_num [gridPoint]

theorem exp_6_232_0 : expNegUpper (3958678537541809091063 / 47097644591435788800 : ℝ) ≤ (78487848343459978497811 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (964171 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_232_1 : expNegUpper (158506599579568808469511 / 1883905783657431552000 : ℝ) ≤ (144235692748885554386921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1929617 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_232 : rowCell 6 232 ≤ (43929210274533268243059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (78487848343459978497811 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (144235692748885554386921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_232_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_232_1
  · norm_num [gridPoint]

theorem exp_6_233_0 : expNegUpper (159288045952689618693119 / 1893193540050948608000 : ℝ) ≤ (144235666127565475886931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1929617 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_233_1 : expNegUpper (79724429286833715658579 / 946596770025474304000 : ℝ) ≤ (264979694251343344946383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (965449 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_233 : rowCell 6 233 ≤ (20179073047004366313671 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (144235666127565475886931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (264979694251343344946383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_233_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_233_1
  · norm_num [gridPoint]

theorem exp_6_234_0 : expNegUpper (3204660347274610520891 / 38050082695004416000 : ℝ) ≤ (66244911455655361844903 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (965449 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_234_1 : expNegUpper (6415807514342770215013 / 76100165390008832000 : ℝ) ≤ (121664260298984651715989 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (386437 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_234 : rowCell 6 234 ≤ (9266572044626936512171 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (66244911455655361844903 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (121664260298984651715989 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_234_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_234_1
  · norm_num [gridPoint]

theorem exp_6_235_0 : expNegUpper (161182065727133732425877 / 1911837567755248128000 : ℝ) ≤ (60832119139995761369813 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (386437 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_235_1 : expNegUpper (40336399356653231843269 / 477959391938812032000 : ℝ) ≤ (44676068382262472604007 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (483369 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_235 : rowCell 6 235 ≤ (34032826351630956492237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (60832119139995761369813 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44676068382262472604007 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_235_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_235_1
  · norm_num [gridPoint]

theorem exp_6_236_0 : expNegUpper (1307541943832563585211 / 15493498702145408000 : ℝ) ≤ (11169015093843370660433 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (483369 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_236_1 : expNegUpper (209419480348563992309 / 2478959792343265280 : ℝ) ≤ (51251826689821755218981 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1934773 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_236 : rowCell 6 236 ≤ (1952400581327532211153 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11169015093843370660433 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51251826689821755218981 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_236_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_236_1
  · norm_num [gridPoint]

theorem exp_6_237_0 : expNegUpper (6523697331215265167779 / 77222917947302727680 : ℝ) ≤ (102503635187118526242487 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1934773 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_237_1 : expNegUpper (81629348690740201051793 / 965286474341284096000 : ℝ) ≤ (37618121727923013016243 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (77443 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_237 : rowCell 6 237 ≤ (28665050511565772920689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (102503635187118526242487 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37618121727923013016243 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_237_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_237_1
  · norm_num [gridPoint]

theorem exp_6_238_0 : expNegUpper (82026886227451806519937 / 969987448302430464000 : ℝ) ≤ (23511321947518743052701 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (77443 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_238_1 : expNegUpper (164221407752981498294473 / 1939974896604860928000 : ℝ) ≤ (17251989552486672794701 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1937383 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_238 : rowCell 6 238 ≤ (26296039538947949162537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23511321947518743052701 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17251989552486672794701 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_238_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_238_1
  · norm_num [gridPoint]

theorem exp_6_239_0 : expNegUpper (347408902212931542803 / 4103999332279808000 : ℝ) ≤ (172519865495012555280549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1937383 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_239_1 : expNegUpper (21735294523286714387 / 256499958267488000 : ℝ) ≤ (39548178396987257673273 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (242337 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_239 : rowCell 6 239 ≤ (12057929195656164348749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (172519865495012555280549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39548178396987257673273 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_239_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_239_1
  · norm_num [gridPoint]

theorem exp_6_240_0 : expNegUpper (10374300722589805331137 / 122427956710419488000 : ℝ) ≤ (158192686317264515110617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (242337 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_240_1 : expNegUpper (166159199245811641972831 / 1958847307366711808000 : ℝ) ≤ (36253495878706069083763 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (970007 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_240 : rowCell 6 240 ≤ (5527525694099585484873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (158192686317264515110617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36253495878706069083763 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_240_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_240_1
  · norm_num [gridPoint]

theorem exp_6_241_0 : expNegUpper (166962531478125467169239 / 1968317770206269952000 : ℝ) ≤ (145013958756278963925801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (970007 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_241_1 : expNegUpper (16713430035181798291843 / 196831777020626995200 : ℝ) ≤ (132895507850328139627173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1941337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_241 : rowCell 6 241 ≤ (20265407989240194364653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (145013958756278963925801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (132895507850328139627173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_241_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_241_1
  · norm_num [gridPoint]

theorem exp_6_242_0 : expNegUpper (16794039829354687517363 / 197781107135158323200 : ℝ) ≤ (66447742689174496143837 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1941337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_242_1 : expNegUpper (168113551687336698907061 / 1977811071351583232000 : ℝ) ≤ (60877753932376643702463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (388533 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_242 : rowCell 6 242 ≤ (18569379215288760084889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (66447742689174496143837 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (60877753932376643702463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_242_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_242_1
  · norm_num [gridPoint]

theorem exp_6_243_0 : expNegUpper (168922422000039756040429 / 1987327210802651648000 : ℝ) ≤ (30438871868356757551619 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (388533 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_243_1 : expNegUpper (42274240811176609166947 / 496831802700662912000 : ℝ) ≤ (13939773559107891138763 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (971999 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_243 : rowCell 6 243 ≤ (17010526031821711412431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30438871868356757551619 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13939773559107891138763 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_243_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_243_1
  · norm_num [gridPoint]

theorem exp_6_244_0 : expNegUpper (1699086125899427564987 / 19968661885594752000 : ℝ) ≤ (11151816997428264980679 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (971999 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_244_1 : expNegUpper (6803381800650633717187 / 79874647542379008000 : ℝ) ≤ (102113329782738793640633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1945337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_244 : rowCell 6 244 ≤ (778910044841628330257 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11151816997428264980679 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (102113329782738793640633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_244_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_244_1
  · norm_num [gridPoint]

theorem exp_6_245_0 : expNegUpper (170898980055594523277507 / 2006428004622053888000 : ℝ) ≤ (3191041031421334098977 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1945337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_245_1 : expNegUpper (85538153497176782210893 / 1003214002311026944000 : ℝ) ≤ (93475903898921371964761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1946681 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_245 : rowCell 6 245 ≤ (14262541421356206834113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3191041031421334098977 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (93475903898921371964761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_245_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_245_1
  · norm_num [gridPoint]

theorem exp_6_246_0 : expNegUpper (85946767194666851552957 / 1008006329495193856000 : ℝ) ≤ (93475888686656514121923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1946681 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_246_1 : expNegUpper (34414451834261649574637 / 403202531798077542400 : ℝ) ≤ (85545715652311965027141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1948029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_246 : rowCell 6 246 ≤ (13054416228120229791543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (93475888686656514121923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (85545715652311965027141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_246_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_246_1
  · norm_num [gridPoint]

theorem exp_6_247_0 : expNegUpper (34578457116699788542597 / 405124030332895334400 : ℝ) ≤ (85545701862509631409071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1948029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_247_1 : expNegUpper (21634051442433567501617 / 253202518958059584000 : ℝ) ≤ (39133532988946644612407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1949383 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_247 : rowCell 6 247 ≤ (5972687103227893792311 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (85545701862509631409071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39133532988946644612407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_247_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_247_1
  · norm_num [gridPoint]

theorem exp_6_248_0 : expNegUpper (21736905453803611103473 / 254406310330540096000 : ℝ) ≤ (78267053480650146191491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1949383 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_248_1 : expNegUpper (174076774091173087570103 / 2035250482644320768000 : ℝ) ≤ (2863537468409332619777 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (975371 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_248 : rowCell 6 248 ≤ (5463798490255595198999 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (78267053480650146191491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2863537468409332619777 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_248_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_248_1
  · norm_num [gridPoint]

theorem exp_6_249_0 : expNegUpper (279843869635939501087 / 3271845843087872000 : ℝ) ≤ (7158842538718909793853 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (975371 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_249_1 : expNegUpper (140068285455008429819 / 1635922921543936000 : ℝ) ≤ (16365548903912936291881 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (976053 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_249 : rowCell 6 249 ≤ (4996927207472230759557 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7158842538718909793853 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16365548903912936291881 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_249_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_249_1
  · norm_num [gridPoint]

theorem exp_6_250_0 : expNegUpper (87956910125968743748411 / 1027289829760637184000 : ℝ) ≤ (13092437071799221446047 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (976053 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_250_1 : expNegUpper (176098169714569535852941 / 2054579659521274368000 : ℝ) ≤ (14961080132158289749281 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (78139 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_250 : rowCell 6 250 ≤ (4568731494694904755109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13092437071799221446047 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14961080132158289749281 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_250_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_250_1
  · norm_num [gridPoint]

theorem exp_6_251_0 : expNegUpper (176929458811193433509189 / 2064278505418383872000 : ℝ) ≤ (59844311240194704924897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (78139 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_251_1 : expNegUpper (8855761138546936501837 / 103213925270919193600 : ℝ) ≤ (27347070754172158939583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1954849 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_251 : rowCell 6 251 ≤ (8352246880064606808401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (59844311240194704924897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27347070754172158939583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_251_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_251_1
  · norm_num [gridPoint]

theorem exp_6_252_0 : expNegUpper (8897467209628433647277 / 103700009481062425600 : ℝ) ≤ (54694133098755336993867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1954849 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_252_1 : expNegUpper (178136525980206766554211 / 2074000189621248512000 : ℝ) ≤ (49974099978771916649163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1956227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_252 : rowCell 6 252 ≤ (3816250796939471463271 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (54694133098755336993867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (49974099978771916649163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_252_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_252_1
  · norm_num [gridPoint]

theorem exp_6_253_0 : expNegUpper (178973486388401852534939 / 2083744712129868288000 : ℝ) ≤ (4997409236670282495781 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1956227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_253_1 : expNegUpper (89581044667356146067209 / 1041872356064934144000 : ℝ) ≤ (22824761931440145407281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1957611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_253 : rowCell 6 253 ≤ (3486480003651953534101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4997409236670282495781 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22824761931440145407281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_253_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_253_1
  · norm_num [gridPoint]

theorem exp_6_254_0 : expNegUpper (3600037907820632380129 / 41870241458884864000 : ℝ) ≤ (45649516974338228066287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1957611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_254_1 : expNegUpper (7207676913071758140257 / 83740482917769728000 : ℝ) ≤ (10422104441789502647131 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1959 / 1000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_254 : rowCell 6 254 ≤ (796095083628206254467 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45649516974338228066287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10422104441789502647131 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_254_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_254_1
  · norm_num [gridPoint]

theorem exp_6_255_0 : expNegUpper (181034581192796619089137 / 2103302272064373248000 : ℝ) ≤ (41688411534844457470773 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1959 / 1000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_255_1 : expNegUpper (707914204878087489841 / 8216024500251458000 : ℝ) ≤ (761225346357212535819 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (980197 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_255 : rowCell 6 255 ≤ (5815418232041348971589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (41688411534844457470773 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (761225346357212535819 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_255_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_255_1
  · norm_num [gridPoint]

theorem sum_6_224_2 : blockSum (rowCell 6) 224 2 ≤ (20557498216227067943199 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_224) (by simpa only [blockSum_one] using cell_6_225) (by norm_num)

theorem sum_6_226_2 : blockSum (rowCell 6) 226 2 ≤ (139410640302356665785249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_226) (by simpa only [blockSum_one] using cell_6_227) (by norm_num)

theorem sum_6_224_4 : blockSum (rowCell 6) 224 4 ≤ (303870626032173209330841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_224_2 sum_6_226_2 (by norm_num)

theorem sum_6_228_2 : blockSum (rowCell 6) 228 2 ≤ (23605659712249184504631 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_228) (by simpa only [blockSum_one] using cell_6_229) (by norm_num)

theorem sum_6_230_2 : blockSum (rowCell 6) 230 2 ≤ (24950486411113260688739 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_230) (by simpa only [blockSum_one] using cell_6_231) (by norm_num)

theorem sum_6_228_4 : blockSum (rowCell 6) 228 4 ≤ (217830244205698965278111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_228_2 sum_6_230_2 (by norm_num)

theorem sum_6_224_8 : blockSum (rowCell 6) 224 8 ≤ (65212608779734021826119 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_224_4 sum_6_228_4 (by norm_num)

theorem sum_6_232_2 : blockSum (rowCell 6) 232 2 ≤ (84287356368542000870401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_232) (by simpa only [blockSum_one] using cell_6_233) (by norm_num)

theorem sum_6_234_2 : blockSum (rowCell 6) 234 2 ≤ (71099114530138702540921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_234) (by simpa only [blockSum_one] using cell_6_235) (by norm_num)

theorem sum_6_232_4 : blockSum (rowCell 6) 232 4 ≤ (77693235449340351705661 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_232_2 sum_6_234_2 (by norm_num)

theorem sum_6_236_2 : blockSum (rowCell 6) 236 2 ≤ (59903459812806288299137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_236) (by simpa only [blockSum_one] using cell_6_237) (by norm_num)

theorem sum_6_238_2 : blockSum (rowCell 6) 238 2 ≤ (10082379586052055572007 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_238) (by simpa only [blockSum_one] using cell_6_239) (by norm_num)

theorem sum_6_236_4 : blockSum (rowCell 6) 236 4 ≤ (27578839435766641539793 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_236_2 sum_6_238_2 (by norm_num)

theorem sum_6_232_8 : blockSum (rowCell 6) 232 8 ≤ (132850914320873634785247 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_232_4 sum_6_236_4 (by norm_num)

theorem sum_6_224_16 : blockSum (rowCell 6) 224 16 ≤ (393701349439809722089723 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_224_8 sum_6_232_8 (by norm_num)

theorem sum_6_240_2 : blockSum (rowCell 6) 240 2 ≤ (8475102153127707260829 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_240) (by simpa only [blockSum_one] using cell_6_241) (by norm_num)

theorem sum_6_242_2 : blockSum (rowCell 6) 242 2 ≤ (889497631177761787433 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_242) (by simpa only [blockSum_one] using cell_6_243) (by norm_num)

theorem sum_6_240_4 : blockSum (rowCell 6) 240 4 ≤ (15591083202549801560293 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_240_2 sum_6_242_2 (by norm_num)

theorem sum_6_244_2 : blockSum (rowCell 6) 244 2 ≤ (29840742318188773439253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_244) (by simpa only [blockSum_one] using cell_6_245) (by norm_num)

theorem sum_6_246_2 : blockSum (rowCell 6) 246 2 ≤ (4999958086915203475233 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_246) (by simpa only [blockSum_one] using cell_6_247) (by norm_num)

theorem sum_6_244_4 : blockSum (rowCell 6) 244 4 ≤ (27420266376382395407709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_244_2 sum_6_246_2 (by norm_num)

theorem sum_6_240_8 : blockSum (rowCell 6) 240 8 ≤ (132795948765513798616883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_240_4 sum_6_244_4 (by norm_num)

theorem sum_6_248_2 : blockSum (rowCell 6) 248 2 ≤ (2615181424431956489639 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_248) (by simpa only [blockSum_one] using cell_6_249) (by norm_num)

theorem sum_6_250_2 : blockSum (rowCell 6) 250 2 ≤ (17489709869454416318619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_250) (by simpa only [blockSum_one] using cell_6_251) (by norm_num)

theorem sum_6_248_4 : blockSum (rowCell 6) 248 4 ≤ (38411161264910068235731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_248_2 sum_6_250_2 (by norm_num)

theorem sum_6_252_2 : blockSum (rowCell 6) 252 2 ≤ (1825682700147856249343 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_252) (by simpa only [blockSum_one] using cell_6_253) (by norm_num)

theorem sum_6_254_2 : blockSum (rowCell 6) 254 2 ≤ (487367156042679960293 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_254) (by simpa only [blockSum_one] using cell_6_255) (by norm_num)

theorem sum_6_252_4 : blockSum (rowCell 6) 252 4 ≤ (26789640502249849002069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_252_2 sum_6_254_2 (by norm_num)

theorem sum_6_248_8 : blockSum (rowCell 6) 248 8 ≤ (326004008835799586189 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_248_4 sum_6_252_4 (by norm_num)

theorem sum_6_240_16 : blockSum (rowCell 6) 240 16 ≤ (197996750532673715854683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_240_8 sum_6_248_8 (by norm_num)

theorem sum_6_224_32 : blockSum (rowCell 6) 224 32 ≤ (985399449412293160034129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_224_16 sum_6_240_16 (by norm_num)

#print axioms sum_6_224_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
