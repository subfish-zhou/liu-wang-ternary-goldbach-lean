import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_224_0 : (498711614668659839907149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (94580789063704531201 / 1131514410455162880 : ℝ) := by
  apply lower_of_taylor (t := (1921353 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_224 : (4545812375356872425013 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 224 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (498711614668659839907149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_224_0
  · norm_num [gridPoint]

theorem exp_7_225_0 : (1794872798991358479967 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (38059845675613406564477 / 454882026668934144000 : ℝ) := by
  apply lower_of_taylor (t := (1922583 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_225 : (67012473386741864528807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 225 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1794872798991358479967 / 3906250000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_225_0
  · norm_num [gridPoint]

theorem exp_7_226_0 : (52901630818705656254509 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7657674579484212775869 / 91432799746448384000 : ℝ) := by
  apply lower_of_taylor (t := (1923819 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_226 : (61722151169743282159069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 226 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (52901630818705656254509 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_226_0
  · norm_num [gridPoint]

theorem exp_7_227_0 : (24354922734607969545989 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3851789978898944610727 / 45945168037198848000 : ℝ) := by
  apply lower_of_taylor (t := (96253 / 50000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_227 : (56831451109872240436517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 227 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (24354922734607969545989 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_227_0
  · norm_num [gridPoint]

theorem exp_7_228_0 : (35868873936013450194491 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (19374214424201607465259 / 230872535794086912000 : ℝ) := by
  apply lower_of_taylor (t := (1926307 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_228 : (3269488141694409594083 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 228 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (35868873936013450194491 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_228_0
  · norm_num [gridPoint]

theorem exp_7_229_0 : (330060137476222827859871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7795992514749406406271 / 92808834476159590400 : ℝ) := by
  apply lower_of_taylor (t := (1927559 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_229 : (48136563526341864802977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 229 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (330060137476222827859871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_229_0
  · norm_num [gridPoint]

theorem exp_7_230_0 : (303622356344718238711657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (39212503463105559092047 / 466348982749860864000 : ℝ) := by
  apply lower_of_taylor (t := (1928817 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_230 : (44280830020735264849293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 230 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (303622356344718238711657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_230_0
  · norm_num [gridPoint]

theorem exp_7_231_0 : (13960814438046196257571 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1972302700728172889743 / 23432975134768128000 : ℝ) := by
  apply lower_of_taylor (t := (12063 / 6250 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_231 : (40721405269662012529261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 231 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (13960814438046196257571 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_231_0
  · norm_num [gridPoint]

theorem exp_7_232_0 : (256693620352470485516689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1984030836310269491103 / 23548786610865152000 : ℝ) := by
  apply lower_of_taylor (t := (1931349 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_232 : (37436658838553366453157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 232 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (256693620352470485516689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_232_0
  · norm_num [gridPoint]

theorem exp_7_233_0 : (235916164383693036743519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (39916194096116016855913 / 473297671315682304000 : ℝ) := by
  apply lower_of_taylor (t := (1932623 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_233 : (344064373255756694271 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 233 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (235916164383693036743519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_233_0
  · norm_num [gridPoint]

theorem exp_7_234_0 : (108377615868661585819859 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8030557724476000115737 / 95125063998100070400 : ℝ) := by
  apply lower_of_taylor (t := (966951 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_234 : (3161197247862823935451 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 234 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (108377615868661585819859 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_234_0
  · norm_num [gridPoint]

theorem exp_7_235_0 : (199091034723932622730307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (20195201401541001336321 / 238979339120878592000 : ℝ) := by
  apply lower_of_taylor (t := (1935187 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_235 : (29035794245841353265419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 235 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (199091034723932622730307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_235_0
  · norm_num [gridPoint]

theorem exp_7_236_0 : (182812123373696250306219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (812580782726133696401 / 9605954921389056000 : ℝ) := by
  apply lower_of_taylor (t := (1936477 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_236 : (6665412140838512063777 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 236 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (182812123373696250306219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_236_0
  · norm_num [gridPoint]

theorem exp_7_237_0 : (167814852874838280219347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1634748004805548348127 / 19305700938943488000 : ℝ) := by
  apply lower_of_taylor (t := (484443 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_237 : (1529651230348760891389 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 237 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (167814852874838280219347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_237_0
  · norm_num [gridPoint]

theorem exp_7_238_0 : (38500720209479908119643 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (41109388252662736004283 / 484993010454160384000 : ℝ) := by
  apply lower_of_taylor (t := (1939073 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_238 : (11230028432664352418757 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 238 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (38500720209479908119643 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_238_0
  · norm_num [gridPoint]

theorem exp_7_239_0 : (141286693084294486094093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1033777650799085710141 / 12183730175279308800 : ℝ) := by
  apply lower_of_taylor (t := (1940379 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_239 : (20605505193940143693617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 239 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (141286693084294486094093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_239_0
  · norm_num [gridPoint]

theorem exp_7_240_0 : (64791578340017445058643 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5199231994515680948689 / 61213889143077888000 : ℝ) := by
  apply lower_of_taylor (t := (194169 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_240 : (9449320207475473906199 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 240 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (64791578340017445058643 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_240_0
  · norm_num [gridPoint]

theorem exp_7_241_0 : (14851887370357594809509 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8367528104646691047633 / 98415745770902528000 : ℝ) := by
  apply lower_of_taylor (t := (1943007 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_241 : (693128301144982476263 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 241 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (14851887370357594809509 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_241_0
  · norm_num [gridPoint]

theorem exp_7_242_0 : (54455455669314128538163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8416492446274422606773 / 98890410828168192000 : ℝ) := by
  apply lower_of_taylor (t := (243041 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_242 : (794188150445967830483 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 242 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (54455455669314128538163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_242_0
  · norm_num [gridPoint]

theorem exp_7_243_0 : (6237761040954477244657 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (21164161789313041329439 / 248415544501804032000 : ℝ) := by
  apply lower_of_taylor (t := (389131 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_243 : (14555620459034742822993 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 243 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (6237761040954477244657 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_243_0
  · norm_num [gridPoint]

theorem exp_7_244_0 : (91433318995349280015249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4257522706308002579547 / 49921583344281395200 : ℝ) := by
  apply lower_of_taylor (t := (1946987 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_244 : (13334799536526808765661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 244 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (91433318995349280015249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_244_0
  · norm_num [gridPoint]

theorem exp_7_245_0 : (41870637381568810113873 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (42823175182818604125907 / 501606287458458624000 : ℝ) := by
  apply lower_of_taylor (t := (487081 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_245 : (488519119362363221877 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 245 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (41870637381568810113873 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_245_0
  · norm_num [gridPoint]

theorem exp_7_246_0 : (76675183978204273536269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (8614434087185295866491 / 100800490210108416000 : ℝ) := by
  apply lower_of_taylor (t := (1949667 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_246 : (11182446607102522088333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 246 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (76675183978204273536269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_246_0
  · norm_num [gridPoint]

theorem exp_7_247_0 : (70186100724264416165997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2166110766024415654869 / 25320216210953216000 : ℝ) := by
  apply lower_of_taylor (t := (975507 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_247 : (10236067045276461366271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 247 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (70186100724264416165997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_247_0
  · norm_num [gridPoint]

theorem exp_7_248_0 : (12845744347920480358671 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (10893328083647191775737 / 127202976741006336000 : ℝ) := by
  apply lower_of_taylor (t := (976183 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_248 : (1170904023685998765701 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 248 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (12845744347920480358671 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_248_0
  · norm_num [gridPoint]

theorem exp_7_249_0 : (29380566086586522411149 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1753018559052500121257 / 20449007971417006080 : ℝ) := by
  apply lower_of_taylor (t := (488431 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_249 : (4284914551272465263599 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 249 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (29380566086586522411149 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_249_0
  · norm_num [gridPoint]

theorem exp_7_250_0 : (13436141892114883648809 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (44078672743744182565077 / 513644201183263744000 : ℝ) := by
  apply lower_of_taylor (t := (1955087 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_250 : (1567640861290797620219 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 250 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (13436141892114883648809 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_250_0
  · norm_num [gridPoint]

theorem exp_7_251_0 : (23995698815946433663 / 488281250000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (143009487532156346407 / 1664738427927552000 : ℝ) := by
  apply lower_of_taylor (t := (978227 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_251 : (7167131305142144592199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 251 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (23995698815946433663 / 488281250000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_251_0
  · norm_num [gridPoint]

theorem exp_7_252_0 : (44923885725609120635503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (143833134348612965087 / 1672578495833088000 : ℝ) := by
  apply lower_of_taylor (t := (1957827 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_252 : (655178021682999735737 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 252 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (44923885725609120635503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_252_0
  · norm_num [gridPoint]

theorem exp_7_253_0 : (41056058852936917721943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (44844666781133499619743 / 520935464335412224000 : ℝ) := by
  apply lower_of_taylor (t := (489801 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_253 : (748461174464758931449 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 253 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (41056058852936917721943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_253_0
  · norm_num [gridPoint]

theorem exp_7_254_0 : (1172233167468273433317 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (9020425806448714079351 / 104675460907801190400 : ℝ) := by
  apply lower_of_taylor (t := (1960587 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_254 : (27353694640007326731 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 254 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1172233167468273433317 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_254_0
  · norm_num [gridPoint]

theorem exp_7_255_0 : (6692190934214843447 / 195312500000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (354380163277225728049 / 4108006674367488000 : ℝ) := by
  apply lower_of_taylor (t := (980987 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_255 : (4997125892487565750309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 255 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (6692190934214843447 / 195312500000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_255_0
  · norm_num [gridPoint]

theorem sum_7_224_2 : (27949094278490364665803 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 224 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_224) (by simpa only [blockSum_one] using cell_7_225) (by norm_num)

theorem sum_7_226_2 : (59276801139807761297793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 226 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_226) (by simpa only [blockSum_one] using cell_7_227) (by norm_num)

theorem sum_7_224_4 : (258299073672067345924601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 224 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_224_2 sum_7_226_2 (by norm_num)

theorem sum_7_228_2 : (20089674758690483661661 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 228 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_228) (by simpa only [blockSum_one] using cell_7_229) (by norm_num)

theorem sum_7_230_2 : (42501117645198638689277 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 230 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_230) (by simpa only [blockSum_one] using cell_7_231) (by norm_num)

theorem sum_7_228_4 : (185450609083849695686859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 228 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_228_2 sum_7_230_2 (by norm_num)

theorem sum_7_224_8 : (22187484137795852080573 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 224 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_224_4 sum_7_228_4 (by norm_num)

theorem sum_7_232_2 : (71843096164129035880257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 232 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_232) (by simpa only [blockSum_one] using cell_7_233) (by norm_num)

theorem sum_7_234_2 : (60647766724469592619929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 234 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_234) (by simpa only [blockSum_one] using cell_7_235) (by norm_num)

theorem sum_7_232_4 : (66245431444299314250093 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 232 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_232_2 sum_7_234_2 (by norm_num)

theorem sum_7_236_2 : (12784017062233555629333 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 236 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_236) (by simpa only [blockSum_one] using cell_7_237) (by norm_num)

theorem sum_7_238_2 : (43065562059268848531131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 238 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_238) (by simpa only [blockSum_one] using cell_7_239) (by norm_num)

theorem sum_7_236_4 : (94201630308203071048463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 236 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_236_2 sum_7_238_2 (by norm_num)

theorem sum_7_232_8 : (226692493196801699548649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 232 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_232_4 sum_7_236_4 (by norm_num)

theorem sum_7_224_16 : (670442175952718741160109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 224 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_224_8 sum_7_232_8 (by norm_num)

theorem sum_7_240_2 : (36226847943575509718973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 240 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_240) (by simpa only [blockSum_one] using cell_7_241) (by norm_num)

theorem sum_7_242_2 : (30439383467954099432653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 242 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_242) (by simpa only [blockSum_one] using cell_7_243) (by norm_num)

theorem sum_7_240_4 : (33333115705764804575813 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 240 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_240_2 sum_7_242_2 (by norm_num)

theorem sum_7_244_2 : (12773888760292944656293 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 244 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_244) (by simpa only [blockSum_one] using cell_7_245) (by norm_num)

theorem sum_7_246_2 : (5354628413094745863651 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 246 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_246) (by simpa only [blockSum_one] using cell_7_247) (by norm_num)

theorem sum_7_244_4 : (4696629117296487276719 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 244 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_244_2 sum_7_246_2 (by norm_num)

theorem sum_7_240_8 : (3551016330765452559963 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 240 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_240_4 sum_7_244_4 (by norm_num)

theorem sum_7_248_2 : (8968530646016460326403 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 248 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_248) (by simpa only [blockSum_one] using cell_7_249) (by norm_num)

theorem sum_7_250_2 : (7502667805798066346647 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 250 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_250) (by simpa only [blockSum_one] using cell_7_251) (by norm_num)

theorem sum_7_248_4 : (329423969036290533461 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 248 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_248_2 sum_7_250_2 (by norm_num)

theorem sum_7_252_2 : (6269734806274034404481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 252 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_252) (by simpa only [blockSum_one] using cell_7_253) (by norm_num)

theorem sum_7_254_2 : (10467864820489031096509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 254 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_254) (by simpa only [blockSum_one] using cell_7_255) (by norm_num)

theorem sum_7_252_4 : (23007334433037099905471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 252 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_252_2 sum_7_254_2 (by norm_num)

theorem sum_7_248_8 : (55949731336666153251571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 248 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_248_4 sum_7_252_4 (by norm_num)

theorem sum_7_240_16 : (169582253921160635170387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 240 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_240_8 sum_7_248_8 (by norm_num)

theorem sum_7_224_32 : (3281345429194841313791 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 224 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_224_16 sum_7_240_16 (by norm_num)

#print axioms sum_7_224_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
