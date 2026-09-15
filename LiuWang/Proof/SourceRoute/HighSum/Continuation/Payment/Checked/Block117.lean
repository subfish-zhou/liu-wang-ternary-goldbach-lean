import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_160_0 : (8513890466469254938667733 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1576887321822045665787 / 19925055250945024000 : ℝ) := by
  apply lower_of_taylor (t := (7423 / 4000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_160 : (124168108402680807719777 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 160 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (8513890466469254938667733 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_160_0
  · norm_num [gridPoint]

theorem exp_7_161_0 : (40286137600469349415624119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1015964169124503083173 / 12828469344396288000 : ℝ) := by
  apply lower_of_taylor (t := (1856549 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_161 : (1468850674201487690534213 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 161 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (40286137600469349415624119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_161_0
  · norm_num [gridPoint]

theorem exp_7_162_0 : (7620944823771194577520017 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1022753944053205562873 / 12905131711245312000 : ℝ) := by
  apply lower_of_taylor (t := (1857357 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_162 : (2778630717460053077626939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 162 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (7620944823771194577520017 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_162_0
  · norm_num [gridPoint]

theorem exp_7_163_0 : (4502769658243798541504483 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (12869716383445039156179 / 162275280764398592000 : ℝ) := by
  apply lower_of_taylor (t := (464543 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_163 : (328346008936252618059259 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 163 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (4502769658243798541504483 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_163_0
  · norm_num [gridPoint]

theorem exp_7_164_0 : (34035362568528046722455389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2591085922287705648319 / 32647853985290035200 : ℝ) := by
  apply lower_of_taylor (t := (464749 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_164 : (310236152142890353614803 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 164 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (34035362568528046722455389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_164_0
  · norm_num [gridPoint]

theorem exp_7_165_0 : (6428251266249339385737279 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (26083130467375735266587 / 328412227753442304000 : ℝ) := by
  apply lower_of_taylor (t := (464957 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_165 : (4687538577168988488988167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 165 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (6428251266249339385737279 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_165_0
  · norm_num [gridPoint]

theorem exp_7_166_0 : (30336755504641008911556321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5251249799694155268963 / 66070325046084608000 : ℝ) := by
  apply lower_of_taylor (t := (465167 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_166 : (4424366934154392141474261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 166 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (30336755504641008911556321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_166_0
  · norm_num [gridPoint]

theorem exp_7_167_0 : (28618786807521088924234391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1321510865712342070007 / 16614836614192128000 : ℝ) := by
  apply lower_of_taylor (t := (372303 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_167 : (1043453823097855093291751 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 167 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (28618786807521088924234391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_167_0
  · norm_num [gridPoint]

theorem exp_7_168_0 : (13492147561150387717758237 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6651259478197148028707 / 83561887228425216000 : ℝ) := by
  apply lower_of_taylor (t := (1862371 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_168 : (3935438088041642973721583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 168 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (13492147561150387717758237 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_168_0
  · norm_num [gridPoint]

theorem exp_7_169_0 : (3178781398001590935683991 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5356142658436138034229 / 67240815023999590400 : ℝ) := by
  apply lower_of_taylor (t := (931617 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_169 : (1854396763829506224675463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 169 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3178781398001590935683991 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_169_0
  · norm_num [gridPoint]

theorem exp_7_170_0 : (11976829292839839667104639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (26957245950507797251357 / 338166310902733824000 : ℝ) := by
  apply lower_of_taylor (t := (372821 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_170 : (873361152466448894318721 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 170 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (11976829292839839667104639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_170_0
  · norm_num [gridPoint]

theorem exp_7_171_0 : (902062404972854149218981 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2713463838585457503773 / 34013425626190848000 : ℝ) := by
  apply lower_of_taylor (t := (233123 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_171 : (3288960050865624617984889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 171 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (902062404972854149218981 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_171_0
  · norm_num [gridPoint]

theorem exp_7_172_0 : (1061052175660078400475289 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2731289309630568521253 / 34210791119752192000 : ℝ) := by
  apply lower_of_taylor (t := (186587 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_172 : (38686438969098493282173 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 172 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1061052175660078400475289 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_172_0
  · norm_num [gridPoint]

theorem exp_7_173_0 : (9979623243488822709080293 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (27492012579945789458023 / 344087275709574144000 : ℝ) := by
  apply lower_of_taylor (t := (466691 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_173 : (58217847438637021914823 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 173 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (9979623243488822709080293 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_173_0
  · norm_num [gridPoint]

theorem exp_7_174_0 : (18763361327222230348186079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1106879973394381978259 / 13842893991922606080 : ℝ) := by
  apply lower_of_taylor (t := (373533 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_174 : (1368241165688487463212307 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 174 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (18763361327222230348186079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_174_0
  · norm_num [gridPoint]

theorem exp_7_175_0 : (17630638836363961522462029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3481606982391453361269 / 43507891682874368000 : ℝ) := by
  apply lower_of_taylor (t := (934287 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_175 : (1285642023974739619964611 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 175 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (17630638836363961522462029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_175_0
  · norm_num [gridPoint]

theorem exp_7_176_0 : (3311678357691215810505111 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (700864616271167086033 / 8751490667609088000 : ℝ) := by
  apply lower_of_taylor (t := (186949 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_176 : (1207452805894339725518687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 176 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3311678357691215810505111 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_176_0
  · norm_num [gridPoint]

theorem exp_7_177_0 : (15543997885348627335626829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (23612709797564335391 / 294612409641984000 : ℝ) := by
  apply lower_of_taylor (t := (935207 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_177 : (7084264319438887645133 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 177 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (15543997885348627335626829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_177_0
  · norm_num [gridPoint]

theorem exp_7_178_0 : (14584902246827843727504457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (118831251167131299687 / 1481463355298816000 : ℝ) := by
  apply lower_of_taylor (t := (116959 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_178 : (2127088350923597498000947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 178 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (14584902246827843727504457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_178_0
  · norm_num [gridPoint]

theorem exp_7_179_0 : (2735723892622509176979687 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2858502961149634462243 / 35608336388710195200 : ℝ) := by
  apply lower_of_taylor (t := (1872283 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_179 : (997457220634840736104737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 179 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2735723892622509176979687 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_179_0
  · norm_num [gridPoint]

theorem exp_7_180_0 : (6411367618889143496051309 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (14385136226914967233111 / 179051347717112832000 : ℝ) := by
  apply lower_of_taylor (t := (468307 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_180 : (467522686982491439446921 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 180 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (6411367618889143496051309 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_180_0
  · norm_num [gridPoint]

theorem exp_7_181_0 : (6007453824365792676729987 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5791280010805962367767 / 72025547311557632000 : ℝ) := by
  apply lower_of_taylor (t := (93709 / 50000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_181 : (876137860389097861258017 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 181 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (6007453824365792676729987 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_181_0
  · norm_num [gridPoint]

theorem exp_7_182_0 : (1125286805429384687361717 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5828682982036127684507 / 72431697451557888000 : ℝ) := by
  apply lower_of_taylor (t := (93757 / 50000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_182 : (1641138497035499687304429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 182 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1125286805429384687361717 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_182_0
  · norm_num [gridPoint]

theorem exp_7_183_0 : (2633605417698043776681471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7332829880091768974897 / 91048736883557376000 : ℝ) := by
  apply lower_of_taylor (t := (1876107 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_183 : (1536358985507270522254547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 183 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2633605417698043776681471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_183_0
  · norm_num [gridPoint]

theorem exp_7_184_0 : (1232180980913231169333933 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1476005819133689297613 / 18311855869355417600 : ℝ) := by
  apply lower_of_taylor (t := (1877081 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_184 : (287525581330537139516669 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 184 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1232180980913231169333933 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_184_0
  · norm_num [gridPoint]

theorem exp_7_185_0 : (230497501559895488715723 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (29709807995185430262817 / 368284996816425984000 : ℝ) := by
  apply lower_of_taylor (t := (1878061 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_185 : (1344646792107730940460293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 185 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (230497501559895488715723 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_185_0
  · norm_num [gridPoint]

theorem exp_7_186_0 : (4309902833381149083526071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1196015874239466820541 / 14813543432887296000 : ℝ) := by
  apply lower_of_taylor (t := (1879049 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_186 : (1257127947153921028187403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 186 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (4309902833381149083526071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_186_0
  · norm_num [gridPoint]

theorem exp_7_187_0 : (8055265394843802413802771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (601837709263243367733 / 7447957688087552000 : ℝ) := by
  apply lower_of_taylor (t := (470011 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_187 : (587397189744513251993229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 187 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (8055265394843802413802771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_187_0
  · norm_num [gridPoint]

theorem exp_7_188_0 : (3762226333700193534043797 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (15142138157398292782229 / 187231446281505792000 : ℝ) := by
  apply lower_of_taylor (t := (376209 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_188 : (1097379697514559185080407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 188 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3762226333700193534043797 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_188_0
  · norm_num [gridPoint]

theorem exp_7_189_0 : (1756403176531020334225391 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (196629496186932798253 / 2429249098697318400 : ℝ) := by
  apply lower_of_taylor (t := (941027 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_189 : (128078497651120917360297 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 189 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1756403176531020334225391 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_189_0
  · norm_num [gridPoint]

theorem exp_7_190_0 : (655706148029968227541221 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (989412088509058856877 / 12213227019664384000 : ℝ) := by
  apply lower_of_taylor (t := (1883069 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_190 : (191258725701350615307541 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 190 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (655706148029968227541221 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_190_0
  · norm_num [gridPoint]

theorem exp_7_191_0 : (3058592252253634120649153 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (192918045733124810929 / 2379326090609664000 : ℝ) := by
  apply lower_of_taylor (t := (1884091 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_191 : (446070589976623268404283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 191 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3058592252253634120649153 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_191_0
  · norm_num [gridPoint]

theorem sum_7_160_2 : (6041904058469995574062851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 160 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_160) (by simpa only [blockSum_one] using cell_7_161) (by norm_num)

theorem sum_7_162_2 : (5405398788950074022101011 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 162 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_162) (by simpa only [blockSum_one] using cell_7_163) (by norm_num)

theorem sum_7_160_4 : (5723651423710034798081931 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 160 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_160_2 sum_7_162_2 (by norm_num)

theorem sum_7_164_2 : (1930263402291046829365003 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 164 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_164) (by simpa only [blockSum_one] using cell_7_165) (by norm_num)

theorem sum_7_166_2 : (1719636445309162502928253 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 166 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_166) (by simpa only [blockSum_one] using cell_7_167) (by norm_num)

theorem sum_7_164_4 : (456237480950026166536657 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 164 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_164_2 sum_7_166_2 (by norm_num)

theorem sum_7_160_8 : (10286026233210296463448501 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 160 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_160_4 sum_7_164_4 (by norm_num)

theorem sum_7_168_2 : (7644231615700655423072509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 168 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_168) (by simpa only [blockSum_one] using cell_7_169) (by norm_num)

theorem sum_7_170_2 : (6782404660731420195259773 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 170 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_170) (by simpa only [blockSum_one] using cell_7_171) (by norm_num)

theorem sum_7_168_4 : (7213318138216037809166141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 168 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_168_2 sum_7_170_2 (by norm_num)

theorem sum_7_172_2 : (600580748945973055831499 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 172 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_172) (by simpa only [blockSum_one] using cell_7_173) (by norm_num)

theorem sum_7_174_2 : (1326941594831613541588459 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 174 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_174) (by simpa only [blockSum_one] using cell_7_175) (by norm_num)

theorem sum_7_172_4 : (5656786934393092362334413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 172 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_172_2 sum_7_174_2 (by norm_num)

theorem sum_7_168_8 : (6435052536304565085750277 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 168 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_168_4 sum_7_172_4 (by norm_num)

theorem sum_7_160_16 : (8360539384757430774599389 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 160 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_160_8 sum_7_168_8 (by norm_num)

theorem sum_7_176_2 : (2340935097004561748739967 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 176 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_176) (by simpa only [blockSum_one] using cell_7_177) (by norm_num)

theorem sum_7_178_2 : (4122002792193278970210421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 178 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_178) (by simpa only [blockSum_one] using cell_7_179) (by norm_num)

theorem sum_7_176_4 : (1760774597240480493538071 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 176 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_176_2 sum_7_178_2 (by norm_num)

theorem sum_7_180_2 : (1811183234354080740151859 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 180 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_180) (by simpa only [blockSum_one] using cell_7_181) (by norm_num)

theorem sum_7_182_2 : (49648398164730784524359 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 182 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_182) (by simpa only [blockSum_one] using cell_7_183) (by norm_num)

theorem sum_7_180_4 : (3399931975625465844931347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 180 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_180_2 sum_7_182_2 (by norm_num)

theorem sum_7_176_8 : (15603736937453334157553049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 176 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_176_4 sum_7_180_4 (by norm_num)

theorem sum_7_184_2 : (1391137349380208319021819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 184 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_184) (by simpa only [blockSum_one] using cell_7_185) (by norm_num)

theorem sum_7_186_2 : (2431922326642947532173861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 186 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_186) (by simpa only [blockSum_one] using cell_7_187) (by norm_num)

theorem sum_7_184_4 : (5214197025403364170217499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 184 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_184_2 sum_7_186_2 (by norm_num)

theorem sum_7_188_2 : (2122007678723526523962783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 188 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_188) (by simpa only [blockSum_one] using cell_7_189) (by norm_num)

theorem sum_7_190_2 : (1848434808459999613346271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 190 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_190) (by simpa only [blockSum_one] using cell_7_191) (by norm_num)

theorem sum_7_188_4 : (1985221243591763068654527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 188 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_188_2 sum_7_190_2 (by norm_num)

theorem sum_7_184_8 : (9184639512586890307526553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 184 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_184_4 sum_7_188_4 (by norm_num)

theorem sum_7_176_16 : (12394188225020112232539801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 176 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_176_8 sum_7_184_8 (by norm_num)

theorem sum_7_160_32 : (45836345764049835330937357 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 160 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_160_16 sum_7_176_16 (by norm_num)

#print axioms sum_7_160_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
