import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_288_0 : expNegUpper (6746667514320149731607 / 76224722892415504000 : ℝ) ≤ (3638571949896730532833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (49917 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_288_1 : expNegUpper (216137443216363217792623 / 2439191132557296128000 : ℝ) ≤ (3292095175043100510461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (999121 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_288 : rowCell 4 288 ≤ (505390473521857542807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3638571949896730532833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3292095175043100510461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_288_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_288_1
  · norm_num [gridPoint]

theorem exp_4_289_0 : expNegUpper (8682950480197698962687 / 97990313362924032000 : ℝ) ≤ (1646047411911780462591 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (999121 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_289_1 : expNegUpper (4346387716595940143759 / 48995156681462016000 : ℝ) ≤ (595604538250083647037 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (31247 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_289 : rowCell 4 289 ≤ (457222602507899509653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1646047411911780462591 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (595604538250083647037 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_289_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_289_1
  · norm_num [gridPoint]

theorem exp_4_290_0 : expNegUpper (109129395041314012925671 / 1230173686947330304000 : ℝ) ≤ (2978022376269899956657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (31247 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_290_1 : expNegUpper (218505958304998214621381 / 2460347373894660608000 : ℝ) ≤ (2693384946254621934273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1000689 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_290 : rowCell 4 290 ≤ (12923878667609514591 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2978022376269899956657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2693384946254621934273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_290_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_290_1
  · norm_num [gridPoint]

theorem exp_4_291_0 : expNegUpper (219448454683640093492989 / 2470959752021975552000 : ℝ) ≤ (168336541489007290061 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1000689 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_291_1 : expNegUpper (10984858531715274341099 / 123547987601098777600 : ℝ) ≤ (1217738994028240735283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (250369 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_291 : rowCell 4 291 ≤ (374001272537672013269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (168336541489007290061 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1217738994028240735283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_291_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_291_1
  · norm_num [gridPoint]

theorem exp_4_292_0 : expNegUpper (11032138290015866186059 / 124079748422752281600 : ℝ) ≤ (304434716857117663609 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (250369 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_292_1 : expNegUpper (220893032810057470518811 / 2481594968455045632000 : ℝ) ≤ (1100920330781288575559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2004531 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_292 : rowCell 4 292 ≤ (21134838987978629329 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (304434716857117663609 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1100920330781288575559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_292_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_292_1
  · norm_num [gridPoint]

theorem exp_4_293_0 : expNegUpper (221841733424998363264979 / 2492253023193870848000 : ℝ) ≤ (440368086921685097877 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2004531 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_293_1 : expNegUpper (111046777412296406220469 / 1246126511596935424000 : ℝ) ≤ (1990233373567905052509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1003057 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_293 : rowCell 4 293 ≤ (305689788408530056537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (440368086921685097877 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1990233373567905052509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_293_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_293_1
  · norm_num [gridPoint]

theorem exp_4_294_0 : expNegUpper (4460907351000437177069 / 50058678324769024000 : ℝ) ≤ (1990233170174079252311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1003057 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_294_1 : expNegUpper (8931949866810006372697 / 100117356649538048000 : ℝ) ≤ (359723731646448478713 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2007701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_294 : rowCell 4 294 ≤ (138143239686976779111 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1990233170174079252311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (359723731646448478713 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_294_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_294_1
  · norm_num [gridPoint]

theorem exp_4_295_0 : expNegUpper (224253678167726457215657 / 2513637647588786688000 : ℝ) ≤ (899309237992216976001 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2007701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_295_1 : expNegUpper (28063577292421019734667 / 314204705948598336000 : ℝ) ≤ (812571698001713414901 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2009293 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_295 : rowCell 4 295 ≤ (249663791741411672303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (899309237992216976001 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (812571698001713414901 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_295_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_295_1
  · norm_num [gridPoint]

theorem exp_4_296_0 : expNegUpper (28183334408806350635083 / 315545527155609664000 : ℝ) ≤ (406285808182803794363 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2009293 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_296_1 : expNegUpper (45144635964857090969947 / 504872843448975462400 : ℝ) ≤ (734061275200082893567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (251361 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_296 : rowCell 4 296 ≤ (112781860005958666019 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (406285808182803794363 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (734061275200082893567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_296_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_296_1
  · norm_num [gridPoint]

theorem exp_4_297_0 : expNegUpper (45336873770106709835507 / 507022725041344614400 : ℝ) ≤ (367030601038192545091 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (251361 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_297_1 : expNegUpper (113471220558670348481843 / 1267556812603361536000 : ℝ) ≤ (331506074421694012421 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (251561 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_297 : rowCell 4 297 ≤ (203751687864317145063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (367030601038192545091 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (331506074421694012421 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_297_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_297_1
  · norm_num [gridPoint]

theorem exp_4_298_0 : expNegUpper (3675915627424408648957 / 41062675346360064000 : ℝ) ≤ (663012083355587807139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (251561 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_298_1 : expNegUpper (7360206845512017127363 / 82125350692720128000 : ℝ) ≤ (598728217154366445223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (503523 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_298 : rowCell 4 298 ≤ (184014472615974206989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (663012083355587807139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (598728217154366445223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_298_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_298_1
  · norm_num [gridPoint]

theorem exp_4_299_0 : expNegUpper (366614216659406100773 / 4090689529676288000 : ℝ) ≤ (299364079257482044111 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (503523 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_299_1 : expNegUpper (91758041238887841413 / 1022672382419072000 : ℝ) ≤ (1081153956064170331891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2015701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_299 : rowCell 4 299 ≤ (166158308302938896207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (299364079257482044111 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1081153956064170331891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_299_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_299_1
  · norm_num [gridPoint]

theorem exp_4_300_0 : expNegUpper (57591432094579656537493 / 641874719731697792000 : ℝ) ≤ (540576925533690464739 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2015701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_300_1 : expNegUpper (230628523768720561445491 / 2567498878926791168000 : ℝ) ≤ (15249495490819760427 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2017313 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_300 : rowCell 4 300 ≤ (75003576265592065703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (540576925533690464739 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15249495490819760427 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_300_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_300_1
  · norm_num [gridPoint]

theorem exp_4_301_0 : expNegUpper (231602307791221422464939 / 2578339640111657472000 : ℝ) ≤ (975967617427076695753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2017313 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_301_1 : expNegUpper (23186668421771405141629 / 257833964011165747200 : ℝ) ≤ (220213509778423716919 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (201893 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_301 : rowCell 4 301 ≤ (27080220686632022151 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (975967617427076695753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (220213509778423716919 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_301_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_301_1
  · norm_num [gridPoint]

theorem exp_4_302_0 : expNegUpper (23284363364317584865709 / 258920323960227891200 : ℝ) ≤ (880853954998789653361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (201893 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_302_1 : expNegUpper (233109594436538720173961 / 2589203239602278912000 : ℝ) ≤ (794865307596185764349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2020551 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_302 : rowCell 4 302 ≤ (122194954157450595133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (880853954998789653361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (794865307596185764349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_302_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_302_1
  · norm_num [gridPoint]

theorem exp_4_303_0 : expNegUpper (234089715926520551455489 / 2600089677398655488000 : ℝ) ≤ (397432616163748462929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2020551 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_303_1 : expNegUpper (14647329026095825902973 / 162505604837415968000 : ℝ) ≤ (179285320026214298077 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (63193 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_303 : rowCell 4 303 ≤ (5512843666495913787 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (397432616163748462929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (179285320026214298077 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_303_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_303_1
  · norm_num [gridPoint]

theorem exp_4_304_0 : expNegUpper (588351411583985443973 / 6527497383751968000 : ℝ) ≤ (44821325797688611931 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (63193 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_304_1 : expNegUpper (9424388166121447238647 / 104439958140031488000 : ℝ) ≤ (1010783180983574921 / 1562500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (404761 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_304 : rowCell 4 304 ≤ (19893440171650585183 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (44821325797688611931 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1010783180983574921 / 1562500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_304_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_304_1
  · norm_num [gridPoint]

theorem exp_4_305_0 : expNegUpper (236596189756735373787287 / 2621931067908674048000 : ℝ) ≤ (323450587794721237253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (404761 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_305_1 : expNegUpper (118433461817693133229423 / 1310965533954337024000 : ℝ) ≤ (291718391442780742563 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1012719 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_305 : rowCell 4 305 ≤ (89717349313756856123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (323450587794721237253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (291718391442780742563 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_305_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_305_1
  · norm_num [gridPoint]

theorem exp_4_306_0 : expNegUpper (118928300644141393389407 / 1316443010311158016000 : ℝ) ≤ (23337469160281173719 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1012719 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_306_1 : expNegUpper (47625786571384423530929 / 526577204124463206400 : ℝ) ≤ (526105304255063416953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (81083 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_306 : rowCell 4 306 ≤ (40454400959821156483 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23337469160281173719 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (526105304255063416953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_306_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_306_1
  · norm_num [gridPoint]

theorem exp_4_307_0 : expNegUpper (47824361844115012658569 / 528772762328342630400 : ℝ) ≤ (526105256073951387443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (81083 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_307_1 : expNegUpper (59848935452495595320659 / 660965952910428288000 : ℝ) ≤ (474323982622215084209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2028717 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_307 : rowCell 4 307 ≤ (364760994544343001 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (526105256073951387443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (474323982622215084209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_307_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_307_1
  · norm_num [gridPoint]

theorem exp_4_308_0 : expNegUpper (60097955886487712514611 / 663716110241716352000 : ℝ) ≤ (474323939542886002463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2028717 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_308_1 : expNegUpper (240667360486905704071883 / 2654864440966865408000 : ℝ) ≤ (213782177244665762749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2030363 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_308 : rowCell 4 308 ≤ (6576650469109347171 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (474323939542886002463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (213782177244665762749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_308_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_308_1
  · norm_num [gridPoint]

theorem exp_4_309_0 : expNegUpper (420289833489997902269 / 4636326797561344000 : ℝ) ≤ (213782157988822662707 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2030363 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_309_1 : expNegUpper (210385912069591941523 / 2318163398780672000 : ℝ) ≤ (385347348058495125571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (508003 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_309 : rowCell 4 309 ≤ (14819562222959629789 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (213782157988822662707 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (385347348058495125571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_309_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_309_1
  · norm_num [gridPoint]

theorem exp_4_310_0 : expNegUpper (121473155672653770630301 / 1338467107267217664000 : ℝ) ≤ (385347313635546431237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (508003 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_310_1 : expNegUpper (243225066981696114050401 / 2676934214534435328000 : ℝ) ≤ (173619381570693792747 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1016833 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_310 : rowCell 4 310 ≤ (53420834901377382777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (385347313635546431237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (173619381570693792747 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_310_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_310_1
  · norm_num [gridPoint]

theorem exp_4_311_0 : expNegUpper (244230804803965739155289 / 2688003358776852992000 : ℝ) ≤ (10851210386808479099 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1016833 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_311_1 : expNegUpper (1222555873921202473489 / 13440016793884264960 : ℝ) ≤ (312845154836521359777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (508831 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_311 : rowCell 4 311 ≤ (9626782019958186841 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10851210386808479099 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (312845154836521359777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_311_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_311_1
  · norm_num [gridPoint]

theorem exp_4_312_0 : expNegUpper (1227600723125310171089 / 13495476706625128960 : ℝ) ≤ (312845127347664527851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (508831 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_312_1 : expNegUpper (245802132280002521422711 / 2699095341325025792000 : ℝ) ≤ (140905042956353705037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1018493 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_312 : rowCell 4 312 ≤ (43362792411489485329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (312845127347664527851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (140905042956353705037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_312_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_312_1
  · norm_num [gridPoint]

theorem exp_4_313_0 : expNegUpper (246814340800935073177199 / 2710210162178953728000 : ℝ) ≤ (28181006135371096193 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1018493 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_313_1 : expNegUpper (123548974730660420477099 / 1355105081089476864000 : ℝ) ≤ (31726339472598659793 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (509663 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_313 : rowCell 4 313 ≤ (39057948290439714299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28181006135371096193 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31726339472598659793 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_313_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_313_1
  · norm_num [gridPoint]

theorem exp_4_314_0 : expNegUpper (4962268066478470055251 / 54426956426772736000 : ℝ) ≤ (50762138768545954551 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (509663 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_314_1 : expNegUpper (9935945452821364000853 / 108853912853545472000 : ℝ) ≤ (28569337080238557233 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1020161 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_314 : rowCell 4 314 ≤ (35174517649295333319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (50762138768545954551 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28569337080238557233 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_314_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_314_1
  · norm_num [gridPoint]

theorem exp_4_315_0 : expNegUpper (249417342186365969702917 / 2732508318804075008000 : ℝ) ≤ (57138669262013439351 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1020161 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_315_1 : expNegUpper (62426050712495236338289 / 683127079701018752000 : ℝ) ≤ (643054218399753137 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (510499 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_315 : rowCell 4 315 ≤ (791797040608793247 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (57138669262013439351 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (643054218399753137 / 3125000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_315_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_315_1
  · norm_num [gridPoint]

theorem exp_4_316_0 : expNegUpper (62681541845150280181841 / 685922913643817088000 : ℝ) ≤ (205777332390418909413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (510499 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_316_1 : expNegUpper (50202931808400004735751 / 548738330915053670400 : ℝ) ≤ (92619549057428773717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1021837 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_316 : rowCell 4 316 ≤ (14256634708134520659 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (205777332390418909413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (92619549057428773717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_316_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_316_1
  · norm_num [gridPoint]

theorem exp_4_317_0 : expNegUpper (50407977779793520512991 / 550979565730443366400 : ℝ) ≤ (23154885311470027181 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1021837 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_317_1 : expNegUpper (126165007444464990863593 / 1377448914326108416000 : ℝ) ≤ (83361565104552895969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (511339 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_317 : rowCell 4 317 ≤ (25665400766197622839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23154885311470027181 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (83361565104552895969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_317_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_317_1
  · norm_num [gridPoint]

theorem exp_4_318_0 : expNegUpper (126679258366902030972377 / 1383063420517460224000 : ℝ) ≤ (166723116261696435409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (511339 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_318_1 : expNegUpper (253650280383109466227513 / 2766126841034920448000 : ℝ) ≤ (30006655778554135971 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1023521 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_318 : rowCell 4 318 ≤ (23098160920487513637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (166723116261696435409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (30006655778554135971 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_318_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_318_1
  · norm_num [gridPoint]

theorem exp_4_319_0 : expNegUpper (10187282435097965823833 / 111095147668935168000 : ℝ) ≤ (75016633221581148727 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1023521 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_319_1 : expNegUpper (159359665948048202443 / 1735861682327112000 : ℝ) ≤ (134992091882857151141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (512183 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_319 : rowCell 4 319 ≤ (831372208264148369 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (75016633221581148727 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (134992091882857151141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_319_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_319_1
  · norm_num [gridPoint]

theorem sum_4_288_2 : blockSum (rowCell 4) 288 2 ≤ (48130653801487852623 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_288) (by simpa only [blockSum_one] using cell_4_289) (by norm_num)

theorem sum_4_290_2 : blockSum (rowCell 4) 290 2 ≤ (787565389901176480181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_290) (by simpa only [blockSum_one] using cell_4_291) (by norm_num)

theorem sum_4_288_4 : blockSum (rowCell 4) 288 4 ≤ (1750178465930933532641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_288_2 sum_4_290_2 (by norm_num)

theorem sum_4_292_2 : blockSum (rowCell 4) 292 2 ≤ (643847212216188125801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_292) (by simpa only [blockSum_one] using cell_4_293) (by norm_num)

theorem sum_4_294_2 : blockSum (rowCell 4) 294 2 ≤ (21038010844614609221 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_294) (by simpa only [blockSum_one] using cell_4_295) (by norm_num)

theorem sum_4_292_4 : blockSum (rowCell 4) 292 4 ≤ (584898741665776678163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_292_2 sum_4_294_2 (by norm_num)

theorem sum_4_288_8 : blockSum (rowCell 4) 288 8 ≤ (2919975949262486888967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_288_4 sum_4_292_4 (by norm_num)

theorem sum_4_296_2 : blockSum (rowCell 4) 296 2 ≤ (429315407876234477101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_296) (by simpa only [blockSum_one] using cell_4_297) (by norm_num)

theorem sum_4_298_2 : blockSum (rowCell 4) 298 2 ≤ (87543195229728275799 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_298) (by simpa only [blockSum_one] using cell_4_299) (by norm_num)

theorem sum_4_296_4 : blockSum (rowCell 4) 296 4 ≤ (779488188795147580297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_296_2 sum_4_298_2 (by norm_num)

theorem sum_4_300_2 : blockSum (rowCell 4) 300 2 ≤ (285408255964344242161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_300) (by simpa only [blockSum_one] using cell_4_301) (by norm_num)

theorem sum_4_302_2 : blockSum (rowCell 4) 302 2 ≤ (232451827487368870873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_302) (by simpa only [blockSum_one] using cell_4_303) (by norm_num)

theorem sum_4_300_4 : blockSum (rowCell 4) 300 4 ≤ (258930041725856556517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_300_2 sum_4_302_2 (by norm_num)

theorem sum_4_296_8 : blockSum (rowCell 4) 296 8 ≤ (1297348272246860693331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_296_4 sum_4_300_4 (by norm_num)

theorem sum_4_288_16 : blockSum (rowCell 4) 288 16 ≤ (2108662110754673791149 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_288_8 sum_4_296_8 (by norm_num)

theorem sum_4_304_2 : blockSum (rowCell 4) 304 2 ≤ (94592275086004891019 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_304) (by simpa only [blockSum_one] using cell_4_305) (by norm_num)

theorem sum_4_306_2 : blockSum (rowCell 4) 306 2 ≤ (76930500414255456583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_306) (by simpa only [blockSum_one] using cell_4_307) (by norm_num)

theorem sum_4_304_4 : blockSum (rowCell 4) 304 4 ≤ (85761387750130173801 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_304_2 sum_4_306_2 (by norm_num)

theorem sum_4_308_2 : blockSum (rowCell 4) 308 2 ≤ (62522376791465995433 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_308) (by simpa only [blockSum_one] using cell_4_309) (by norm_num)

theorem sum_4_310_2 : blockSum (rowCell 4) 310 2 ≤ (50777372500584158491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_310) (by simpa only [blockSum_one] using cell_4_311) (by norm_num)

theorem sum_4_308_4 : blockSum (rowCell 4) 308 4 ≤ (28324937323012538481 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_308_2 sum_4_310_2 (by norm_num)

theorem sum_4_304_8 : blockSum (rowCell 4) 304 8 ≤ (142411262396155250763 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_304_4 sum_4_308_4 (by norm_num)

theorem sum_4_312_2 : blockSum (rowCell 4) 312 2 ≤ (20605185175482299907 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_312) (by simpa only [blockSum_one] using cell_4_313) (by norm_num)

theorem sum_4_314_2 : blockSum (rowCell 4) 314 2 ≤ (66846399273647063199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_314) (by simpa only [blockSum_one] using cell_4_315) (by norm_num)

theorem sum_4_312_4 : blockSum (rowCell 4) 312 4 ≤ (149267139975576262827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_312_2 sum_4_314_2 (by norm_num)

theorem sum_4_316_2 : blockSum (rowCell 4) 316 2 ≤ (54178670182466664157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_316) (by simpa only [blockSum_one] using cell_4_317) (by norm_num)

theorem sum_4_318_2 : blockSum (rowCell 4) 318 2 ≤ (21941233063545611431 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_318) (by simpa only [blockSum_one] using cell_4_319) (by norm_num)

theorem sum_4_316_4 : blockSum (rowCell 4) 316 4 ≤ (98061136309557887019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_316_2 sum_4_318_2 (by norm_num)

theorem sum_4_312_8 : blockSum (rowCell 4) 312 8 ≤ (123664138142567074923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_312_4 sum_4_316_4 (by norm_num)

theorem sum_4_304_16 : blockSum (rowCell 4) 304 16 ≤ (408486662934877576449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_304_8 sum_4_312_8 (by norm_num)

theorem sum_4_288_32 : blockSum (rowCell 4) 288 32 ≤ (1258574386844775683799 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_288_16 sum_4_304_16 (by norm_num)

#print axioms sum_4_288_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
