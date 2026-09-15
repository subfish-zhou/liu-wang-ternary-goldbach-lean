import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_288_0 : (754685015008802549459 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3406788570761977316663 / 38112316840141824000 : ℝ) := by
  apply lower_of_taylor (t := (2010423 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_288 : (22012923732704021551 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 288 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (754685015008802549459 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_288_0
  · norm_num [gridPoint]

theorem exp_7_289_0 : (136795090497713009697 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (10961000461653845873913 / 122487748964244070400 : ℝ) := by
  apply lower_of_taylor (t := (31437 / 15625 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_289 : (99752209009323517061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 289 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (136795090497713009697 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_289_0
  · norm_num [gridPoint]

theorem exp_7_290_0 : (1239528404577162847841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (55102544533441232568337 / 615086129776610304000 : ℝ) := by
  apply lower_of_taylor (t := (2013519 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_290 : (90387524900567702159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 290 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1239528404577162847841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_290_0
  · norm_num [gridPoint]

theorem exp_7_291_0 : (1122933949650481257907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5540124630579230834519 / 61773922430843904000 : ℝ) := by
  apply lower_of_taylor (t := (2015073 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_291 : (163770704988966964861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 291 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1122933949650481257907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_291_0
  · norm_num [gridPoint]

theorem exp_7_292_0 : (1017101430342024095689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5570111012340711838239 / 62039802841670656000 : ℝ) := by
  apply lower_of_taylor (t := (252079 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_292 : (148335900205213439939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 292 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1017101430342024095689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_292_0
  · norm_num [gridPoint]

theorem exp_7_293_0 : (921058480027866751139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (56002138484370324362203 / 623062542101412864000 : ℝ) := by
  apply lower_of_taylor (t := (403639 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_293 : (134328823754220387059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 293 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (921058480027866751139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_293_0
  · norm_num [gridPoint]

theorem exp_7_294_0 : (208479616707023765643 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11260866777353317593379 / 125146553072511590400 : ℝ) := by
  apply lower_of_taylor (t := (2019763 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_294 : (60810083824727232829 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 294 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (208479616707023765643 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_294_0
  · norm_num [gridPoint]

theorem exp_7_295_0 : (377436573090919463989 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (14151924707170142719683 / 157102174550035456000 : ℝ) := by
  apply lower_of_taylor (t := (404267 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_295 : (27523014012960983687 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 295 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (377436573090919463989 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_295_0
  · norm_num [gridPoint]

theorem exp_7_296_0 : (17079648054192667323 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2845611790409846738999 / 31554517030708224000 : ℝ) := by
  apply lower_of_taylor (t := (2022911 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_296 : (99637062488642239193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 296 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (17079648054192667323 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_296_0
  · norm_num [gridPoint]

theorem exp_7_297_0 : (123637133835267190337 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11443589464680068270581 / 126755538520925184000 : ℝ) := by
  apply lower_of_taylor (t := (506123 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_297 : (45078654397525568211 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 297 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (123637133835267190337 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_297_0
  · norm_num [gridPoint]

theorem exp_7_298_0 : (559261069191738821021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (57524835872375452279773 / 636470754171526144000 : ℝ) := by
  apply lower_of_taylor (t := (2026077 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_298 : (81563639253156893563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 298 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (559261069191738821021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_298_0
  · norm_num [gridPoint]

theorem exp_7_299_0 : (505855423331660970957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1156658079064138584857 / 12783390506297303040 : ℝ) := by
  apply lower_of_taylor (t := (1013833 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_299 : (36887431948826617541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 299 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (505855423331660970957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_299_0
  · norm_num [gridPoint]

theorem exp_7_300_0 : (457461899450507327439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (29071077031989716962201 / 320937003017321472000 : ℝ) := by
  apply lower_of_taylor (t := (101463 / 50000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_300 : (16679266354428140941 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 300 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (457461899450507327439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_300_0
  · norm_num [gridPoint]

theorem exp_7_301_0 : (41361918053687540047 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11690517740555525601339 / 128916839266171904000 : ℝ) := by
  apply lower_of_taylor (t := (1015429 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_301 : (30161482255731467801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 301 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (41361918053687540047 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_301_0
  · norm_num [gridPoint]

theorem exp_7_302_0 : (373907481355917333231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11752842073537234634399 / 129460019240702976000 : ℝ) := by
  apply lower_of_taylor (t := (101623 / 50000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_302 : (13632834736488136323 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 302 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (373907481355917333231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_302_0
  · norm_num [gridPoint]

theorem exp_7_303_0 : (67588980661673159823 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7384627694598716387821 / 81252713206576128000 : ℝ) := by
  apply lower_of_taylor (t := (1017033 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_303 : (24643245971620100181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 303 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (67588980661673159823 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_303_0
  · norm_num [gridPoint]

theorem exp_7_304_0 : (76346024954020469267 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1484775619204324087017 / 16318725616953548800 : ℝ) := by
  apply lower_of_taylor (t := (2035677 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_304 : (44537765854231737973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 304 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (76346024954020469267 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_304_0
  · norm_num [gridPoint]

theorem exp_7_305_0 : (275909226710653114557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (59706222499920531988597 / 655482053280113664000 : ℝ) := by
  apply lower_of_taylor (t := (509323 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_305 : (40239097397873395931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 305 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (275909226710653114557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_305_0
  · norm_num [gridPoint]

theorem exp_7_306_0 : (249233154108418270621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (12004523450023419661717 / 131644158291704832000 : ℝ) := by
  apply lower_of_taylor (t := (2038911 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_306 : (36348611035995509151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 306 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (249233154108418270621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_306_0
  · norm_num [gridPoint]

theorem exp_7_307_0 : (112547459056587971061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6034021151684732412291 / 66096523921337344000 : ℝ) := by
  apply lower_of_taylor (t := (1020267 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_307 : (8207061831264141003 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 307 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (112547459056587971061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_307_0
  · norm_num [gridPoint]

theorem exp_7_308_0 : (50814348101738670063 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (30329503899097935556919 / 331857698272330752000 : ℝ) := by
  apply lower_of_taylor (t := (1021081 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_308 : (14821711668378625907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 308 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (50814348101738670063 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_308_0
  · norm_num [gridPoint]

theorem exp_7_309_0 : (36701032275834455117 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (12195801718449480192727 / 133294252690477670400 : ℝ) := by
  apply lower_of_taylor (t := (2043793 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_309 : (26762722471375337871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 309 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (36701032275834455117 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_309_0
  · norm_num [gridPoint]

theorem exp_7_310_0 : (33128515582858711347 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (61300216397086575354567 / 669232839936553984000 : ℝ) := by
  apply lower_of_taylor (t := (2045429 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_310 : (1207880560101388103 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 310 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (33128515582858711347 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_310_0
  · norm_num [gridPoint]

theorem exp_7_311_0 : (149491990316151901469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (616226337107980559689 / 6720001259971584000 : ℝ) := by
  apply lower_of_taylor (t := (2047069 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_311 : (4360436097225538529 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 311 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (149491990316151901469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_311_0
  · norm_num [gridPoint]

theorem exp_7_312_0 : (134892124101341028283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (619462630314665044889 / 6747731216342016000 : ℝ) := by
  apply lower_of_taylor (t := (2048713 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_312 : (19672909763225070161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 312 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (134892124101341028283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_312_0
  · norm_num [gridPoint]

theorem exp_7_313_0 : (121696605551917943973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2008745382489567180543 / 21856510543473664000 : ℝ) := by
  apply lower_of_taylor (t := (1025181 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_313 : (17748451627279814051 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 313 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (121696605551917943973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_313_0
  · norm_num [gridPoint]

theorem exp_7_314_0 : (109772614986015260903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (403852694748470657903 / 4389266075081318400 : ℝ) := by
  apply lower_of_taylor (t := (1026007 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_314 : (8004717708614009323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 314 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (109772614986015260903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_314_0
  · norm_num [gridPoint]

theorem exp_7_315_0 : (6187478668144998037 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (31462224008030137152781 / 341563183001981952000 : ℝ) := by
  apply lower_of_taylor (t := (2053671 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_315 : (3609572028351993347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 315 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (6187478668144998037 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_315_0
  · norm_num [gridPoint]

theorem exp_7_316_0 : (44634224683393962319 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6325295034540321127089 / 68592219994676224000 : ℝ) := by
  apply lower_of_taylor (t := (513833 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_316 : (3254767764974326719 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 316 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (44634224683393962319 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_316_0
  · norm_num [gridPoint]

theorem exp_7_317_0 : (16095977156615566363 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (12716535434425284910643 / 137744748693199872000 : ℝ) := by
  apply lower_of_taylor (t := (514249 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_317 : (11737331154898837459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 317 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (16095977156615566363 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_317_0
  · norm_num [gridPoint]

theorem exp_7_318_0 : (14508824617454914893 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (63913630994314575834803 / 691530996561675264000 : ℝ) := by
  apply lower_of_taylor (t := (411733 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_318 : (5289982631884648193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 318 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (14508824617454914893 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_318_0
  · norm_num [gridPoint]

theorem exp_7_319_0 : (32689862978720575743 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (401536339437827042487 / 4339649745211187200 : ℝ) := by
  apply lower_of_taylor (t := (1030169 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_319 : (9535096712828297309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 319 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (32689862978720575743 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_319_0
  · norm_num [gridPoint]

theorem sum_7_288_2 : (13113551729552726551 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 288 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_288) (by simpa only [blockSum_one] using cell_7_289) (by norm_num)

theorem sum_7_290_2 : (344545754790102369179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 290 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_290) (by simpa only [blockSum_one] using cell_7_291) (by norm_num)

theorem sum_7_288_4 : (764179410135789618811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 288 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_288_2 sum_7_290_2 (by norm_num)

theorem sum_7_292_2 : (141332361979716913499 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 292 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_292) (by simpa only [blockSum_one] using cell_7_293) (by norm_num)

theorem sum_7_294_2 : (115856111850649200203 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 294 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_294) (by simpa only [blockSum_one] using cell_7_295) (by norm_num)

theorem sum_7_292_4 : (128594236915183056851 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 292 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_292_2 sum_7_294_2 (by norm_num)

theorem sum_7_288_8 : (255711271559304369243 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 288 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_288_4 sum_7_292_4 (by norm_num)

theorem sum_7_296_2 : (37958874256738675123 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 296 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_296) (by simpa only [blockSum_one] using cell_7_297) (by norm_num)

theorem sum_7_298_2 : (31067700630162025729 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 298 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_298) (by simpa only [blockSum_one] using cell_7_299) (by norm_num)

theorem sum_7_296_4 : (17256643721725175213 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 296 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_296_2 sum_7_298_2 (by norm_num)

theorem sum_7_300_2 : (63520014964587749683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 300 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_300) (by simpa only [blockSum_one] using cell_7_301) (by norm_num)

theorem sum_7_302_2 : (51908915444596372827 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 302 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_302) (by simpa only [blockSum_one] using cell_7_303) (by norm_num)

theorem sum_7_300_4 : (11542893040918412251 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 300 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_300_2 sum_7_302_2 (by norm_num)

theorem sum_7_296_8 : (3599942095330448433 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 296 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_296_4 sum_7_300_4 (by norm_num)

theorem sum_7_288_16 : (370909418609878719099 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 288 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_288_8 sum_7_296_8 (by norm_num)

theorem sum_7_304_2 : (5298553953256570869 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 304 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_304) (by simpa only [blockSum_one] using cell_7_305) (by norm_num)

theorem sum_7_306_2 : (69176858361052073163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 306 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_306) (by simpa only [blockSum_one] using cell_7_307) (by norm_num)

theorem sum_7_304_4 : (153953721613157207067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 304 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_304_2 sum_7_306_2 (by norm_num)

theorem sum_7_308_2 : (11281229161626517937 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 308 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_308) (by simpa only [blockSum_one] using cell_7_309) (by norm_num)

theorem sum_7_310_2 : (9191958337631090941 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 310 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_310) (by simpa only [blockSum_one] using cell_7_311) (by norm_num)

theorem sum_7_308_4 : (10236593749628804439 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 308 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_308_2 sum_7_310_2 (by norm_num)

theorem sum_7_304_8 : (256319659109445251457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 304 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_304_4 sum_7_308_4 (by norm_num)

theorem sum_7_312_2 : (9355340347626221053 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 312 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_312) (by simpa only [blockSum_one] using cell_7_313) (by norm_num)

theorem sum_7_314_2 : (15223861765317996017 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 314 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_314) (by simpa only [blockSum_one] using cell_7_315) (by norm_num)

theorem sum_7_312_4 : (33934542460570438123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 312 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_312_2 sum_7_314_2 (by norm_num)

theorem sum_7_316_2 : (4951280442959228867 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 316 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_316) (by simpa only [blockSum_one] using cell_7_317) (by norm_num)

theorem sum_7_318_2 : (4023012395319518739 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 318 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_318) (by simpa only [blockSum_one] using cell_7_319) (by norm_num)

theorem sum_7_316_4 : (4487146419139373803 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 316 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_316_2 sum_7_318_2 (by norm_num)

theorem sum_7_312_8 : (28185137278133653569 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 312 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_312_4 sum_7_316_4 (by norm_num)

theorem sum_7_304_16 : (369060208221979865733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 304 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_304_8 sum_7_312_8 (by norm_num)

theorem sum_7_288_32 : (555901825317843365307 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 288 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_288_16 sum_7_304_16 (by norm_num)

#print axioms sum_7_288_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
