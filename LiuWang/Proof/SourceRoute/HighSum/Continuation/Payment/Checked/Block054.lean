import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_192_0 : expNegUpper (380331677410874870769 / 4784759183237377600 : ℝ) ≤ (15070830551136612278945119 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (186079 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_192_1 : expNegUpper (121820212477285237535311 / 1531122938635960832000 : ℝ) ≤ (27977586350672839185511393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1861873 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_192 : rowCell 3 192 ≤ (529763467597526309299749 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15070830551136612278945119 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27977586350672839185511393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_192_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_192_1
  · norm_num [gridPoint]

theorem exp_3_193_0 : expNegUpper (13609609825256444388431 / 171055240311030272000 : ℝ) ≤ (27977578948636523112516769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1861873 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_193_1 : expNegUpper (6811210302500704988591 / 85527620155515136000 : ℝ) ≤ (12979401618206364105479997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1862963 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_193 : rowCell 3 193 ≤ (1966544723701080393347331 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27977578948636523112516769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12979401618206364105479997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_193_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_193_1
  · norm_num [gridPoint]

theorem exp_3_194_0 : expNegUpper (2465410146992276469679 / 30957884505366784000 : ℝ) ≤ (12979398221449817161190343 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1862963 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_194_1 : expNegUpper (4935481160399898964077 / 61915769010733568000 : ℝ) ≤ (601910533916645218392487 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1864059 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_194 : rowCell 3 194 ≤ (1824306517730151952436477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12979398221449817161190343 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (601910533916645218392487 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_194_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_194_1
  · norm_num [gridPoint]

theorem exp_3_195_0 : expNegUpper (124058203530736077339357 / 1556314126043161088000 : ℝ) ≤ (2407641512386396877727851 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1864059 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_195_1 : expNegUpper (31043988291144559296559 / 389078531510790272000 : ℝ) ≤ (22322015598368511977589281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1865161 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_195 : rowCell 3 195 ≤ (845853813588823625597347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2407641512386396877727851 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22322015598368511977589281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_195_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_195_1
  · norm_num [gridPoint]

theorem exp_3_196_0 : expNegUpper (3468044082305927994199 / 43465468475659392000 : ℝ) ≤ (22322009882013316256701639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1865161 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_196_1 : expNegUpper (2777079286690969461703 / 34772374780527513600 : ℝ) ≤ (20687614964754455617956577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1866269 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_196 : rowCell 3 196 ≤ (3136300485286129193020121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22322009882013316256701639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20687614964754455617956577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_196_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_196_1
  · norm_num [gridPoint]

theorem exp_3_197_0 : expNegUpper (25128933527756892313687 / 314644488502014054400 : ℝ) ≤ (20687609723884894665860231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1866269 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_197_1 : expNegUpper (62882441605941143301093 / 786611221255035136000 : ℝ) ≤ (19165683612087441901537577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (233423 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_197 : rowCell 3 197 ≤ (2906137955752334320140783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20687609723884894665860231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19165683612087441901537577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_197_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_197_1
  · norm_num [gridPoint]

theorem exp_3_198_0 : expNegUpper (63221727775193942700117 / 790855429101078784000 : ℝ) ≤ (19165678808817318440598737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (233423 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_198_1 : expNegUpper (126564909089282866391953 / 1581710858202157568000 : ℝ) ≤ (17749102206445443811248139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (233563 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_198 : rowCell 3 198 ≤ (538371799451305804708527 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19165678808817318440598737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17749102206445443811248139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_198_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_198_1
  · norm_num [gridPoint]

theorem exp_3_199_0 : expNegUpper (180972032981564197 / 2261649226240000 : ℝ) ≤ (443727445143719945503737 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (233563 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_199_1 : expNegUpper (22643316537890491 / 282706153280000 : ℝ) ≤ (8215574821069487575441011 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1869631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_199 : rowCell 3 199 ≤ (1246227176358021433359323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (443727445143719945503737 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8215574821069487575441011 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_199_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_199_1
  · norm_num [gridPoint]

theorem exp_3_200_0 : expNegUpper (16006524131305803767959 / 199844525562949696000 : ℝ) ≤ (3286229122329797602912511 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1869631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_200_1 : expNegUpper (128176132513274369780391 / 1598756204503597568000 : ℝ) ≤ (7602742578829866154344061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (467691 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_200 : rowCell 3 200 ≤ (461394307846689737354971 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3286229122329797602912511 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7602742578829866154344061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_200_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_200_1
  · norm_num [gridPoint]

theorem exp_3_201_0 : expNegUpper (128862162623578844513439 / 1607313135112950272000 : ℝ) ≤ (950342591717525005204621 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (467691 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_201_1 : expNegUpper (12898735004454258683719 / 160731313511295027200 : ℝ) ≤ (7033065439880469381839743 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (935951 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_201 : rowCell 3 201 ≤ (1067256135537528326680107 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (950342591717525005204621 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7033065439880469381839743 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_201_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_201_1
  · norm_num [gridPoint]

theorem exp_3_202_0 : expNegUpper (1440843104465535731711 / 17954365600311756800 : ℝ) ≤ (7033063751145414630123613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (935951 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_202_1 : expNegUpper (14422479790197478863829 / 179543656003117568000 : ℝ) ≤ (6503727410679289935466301 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1873047 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_202 : rowCell 3 202 ≤ (39484598939242676352233 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7033063751145414630123613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6503727410679289935466301 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_202_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_202_1
  · norm_num [gridPoint]

theorem exp_3_203_0 : expNegUpper (130493353377743190894389 / 1624495511248921088000 : ℝ) ≤ (13007451731126013367444353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1873047 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_203_1 : expNegUpper (32655261676829296330317 / 406123877812230272000 : ℝ) ≤ (60120771772002935902627 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1874197 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_203 : rowCell 3 203 ≤ (365065441018038435452627 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13007451731126013367444353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (60120771772002935902627 / 5000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_203_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_203_1
  · norm_num [gridPoint]

theorem exp_3_204_0 : expNegUpper (1313145945434524163637 / 16331209567755392000 : ℝ) ≤ (2404830305581921186160593 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1874197 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_204_1 : expNegUpper (5257741832940034408267 / 65324838271021568000 : ℝ) ≤ (173613127729154477854269 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (937677 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_204 : rowCell 3 204 ≤ (1687053548655287696751739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2404830305581921186160593 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (173613127729154477854269 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_204_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_204_1
  · norm_num [gridPoint]

theorem exp_3_205_0 : expNegUpper (473618684198439207853 / 5884477564902912000 : ℝ) ≤ (11111237590252403745982923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (937677 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_205_1 : expNegUpper (237042697943847636487 / 2942238782451456000 : ℝ) ≤ (5132010385806552307139869 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (469129 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_205 : rowCell 3 205 ≤ (1558703044080917358173021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11111237590252403745982923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5132010385806552307139869 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_205_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_205_1
  · norm_num [gridPoint]

theorem exp_3_206_0 : expNegUpper (66484209206909102752657 / 825220181373020416000 : ℝ) ≤ (2052803681862129727580709 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (469129 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_206_1 : expNegUpper (26619979117430838981909 / 330088072549208166400 : ℝ) ≤ (9478087412885037448974181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (375537 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_206 : rowCell 3 206 ≤ (1439612093602709058391843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2052803681862129727580709 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9478087412885037448974181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_206_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_206_1
  · norm_num [gridPoint]

theorem exp_3_207_0 : expNegUpper (26760204220630412527149 / 331826864637984870400 : ℝ) ≤ (9478085254299533174552891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (375537 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_207_1 : expNegUpper (8370860388706321761571 / 103695895199370272000 : ℝ) ≤ (1749859929974933733986893 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1878859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_207 : rowCell 3 207 ≤ (83072330211156727656843 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9478085254299533174552891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1749859929974933733986893 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_207_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_207_1
  · norm_num [gridPoint]

theorem exp_3_208_0 : expNegUpper (934982159386838591051 / 11582299457913632000 : ℝ) ≤ (546831104879232587080283 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1878859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_208_1 : expNegUpper (14974605260160720857287 / 185316791326618112000 : ℝ) ≤ (8073771347856208345513787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (940019 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_208 : rowCell 3 208 ≤ (613376653923225467541899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (546831104879232587080283 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8073771347856208345513787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_208_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_208_1
  · norm_num [gridPoint]

theorem exp_3_209_0 : expNegUpper (5419106318072597426447 / 67063630359798272000 : ℝ) ≤ (1009221193404547705524363 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (940019 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_209_1 : expNegUpper (2712258978918577204599 / 33531815179899136000 : ℝ) ≤ (1861964310391195776667527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (235153 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_209 : rowCell 3 209 ≤ (1131850970650948997179533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1009221193404547705524363 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1861964310391195776667527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_209_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_209_1
  · norm_num [gridPoint]

theorem exp_3_210_0 : expNegUpper (68160856047910622507151 / 842676617178052864000 : ℝ) ≤ (1489571119557277075624549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (235153 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_210_1 : expNegUpper (136458281025086912457301 / 1685353234356105728000 : ℝ) ≤ (1373628002951091681374613 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376483 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_210 : rowCell 3 210 ≤ (1043935262093859391864671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1489571119557277075624549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1373628002951091681374613 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_210_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_210_1
  · norm_num [gridPoint]

theorem exp_3_211_0 : expNegUpper (15241067041784703544421 / 188237616447001088000 : ℝ) ≤ (686813851462437666285293 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376483 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_211_1 : expNegUpper (152563837301399212363 / 1882376164470010880 : ℝ) ≤ (6331417900170711981897141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470903 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_211 : rowCell 3 211 ≤ (96252351274332428143763 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (686813851462437666285293 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6331417900170711981897141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_211_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_211_1
  · norm_num [gridPoint]

theorem exp_3_212_0 : expNegUpper (1380213417848768430467 / 17029466999956689920 : ℝ) ≤ (1582854132889213615922347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470903 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_212_1 : expNegUpper (138160476576784642967211 / 1702946699995668992000 : ℝ) ≤ (2917346397239979845291349 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376963 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_212 : rowCell 3 212 ≤ (443581811271726049664869 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1582854132889213615922347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2917346397239979845291349 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_212_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_212_1
  · norm_num [gridPoint]

theorem exp_3_213_0 : expNegUpper (138876937314603425184099 / 1711777690274083328000 : ℝ) ≤ (5834691546235891255682307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376963 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_213_1 : expNegUpper (69508680017000807353949 / 855888845137041664000 : ℝ) ≤ (5375158881110170082539177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1886023 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_213 : rowCell 3 213 ≤ (163486472902413622302019 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5834691546235891255682307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5375158881110170082539177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_213_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_213_1
  · norm_num [gridPoint]

theorem exp_3_214_0 : expNegUpper (310525333239068277869 / 3823625597462784000 : ℝ) ≤ (5375157742995546027939741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1886023 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_214_1 : expNegUpper (621680506378883791457 / 7647251194925568000 : ℝ) ≤ (154693492264007018098139 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1887237 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_214 : rowCell 3 214 ≤ (752933761888947065430943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5375157742995546027939741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (154693492264007018098139 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_214_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_214_1
  · norm_num [gridPoint]

theorem exp_3_215_0 : expNegUpper (140599739706147389346617 / 1729508185748177408000 : ℝ) ≤ (4950190715059649578225453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1887237 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_215_1 : expNegUpper (17592843534108125600757 / 216188523218522176000 : ℝ) ≤ (4557338021649104196795567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1888457 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_215 : rowCell 3 215 ≤ (693297537401151712045503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4950190715059649578225453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4557338021649104196795567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_215_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_215_1
  · norm_num [gridPoint]

theorem exp_3_216_0 : expNegUpper (17683370819080258103733 / 217300961367982144000 : ℝ) ≤ (4557337076355063312743489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1888457 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_216_1 : expNegUpper (28322254607837743324331 / 347681538188771430400 : ℝ) ≤ (1048576353303816775736537 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (944841 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_216 : rowCell 3 216 ≤ (319088816571633858627911 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4557337076355063312743489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1048576353303816775736537 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_216_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_216_1
  · norm_num [gridPoint]

theorem exp_3_217_0 : expNegUpper (3163068677542297738219 / 38829556321006489600 : ℝ) ≤ (6553600862649680289021 / 1562500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (944841 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_217_1 : expNegUpper (7915761012586590847427 / 97073890802516224000 : ℝ) ≤ (3858953320608260117066637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1890913 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_217 : rowCell 3 217 ≤ (146812699856612433689657 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6553600862649680289021 / 1562500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3858953320608260117066637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_217_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_217_1
  · norm_num [gridPoint]

theorem exp_3_218_0 : expNegUpper (71606560754385018122827 / 878137608126241024000 : ℝ) ≤ (1929476268199518038108227 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1890913 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_218_1 : expNegUpper (143360033827313407431213 / 1756275216252482048000 : ℝ) ≤ (3549283818400732141665577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1892149 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_218 : rowCell 3 218 ≤ (135053812707337278466179 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1929476268199518038108227 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3549283818400732141665577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_218_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_218_1
  · norm_num [gridPoint]

theorem exp_3_219_0 : expNegUpper (5763682784123225025453 / 70609729454617088000 : ℝ) ≤ (3549283104441298435058073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1892149 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_219_1 : expNegUpper (1442402898337916798833 / 17652432363654272000 : ℝ) ≤ (326343311586317984914493 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (189339 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_219 : rowCell 3 219 ≤ (62098673448041467036099 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3549283104441298435058073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (326343311586317984914493 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_219_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_219_1
  · norm_num [gridPoint]

theorem exp_3_220_0 : expNegUpper (4027081799018717031137 / 49284280410670208000 : ℝ) ≤ (3263432466049011775247903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (189339 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_220_1 : expNegUpper (16124941804259122148779 / 197137121642680832000 : ℝ) ≤ (2999663438393107369338087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (947319 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_220 : rowCell 3 220 ≤ (45671058035214597523963 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3263432466049011775247903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2999663438393107369338087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_220_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_220_1
  · norm_num [gridPoint]

theorem exp_3_221_0 : expNegUpper (145861756985888245428539 / 1783247791508582912000 : ℝ) ≤ (749915711782816573921837 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (947319 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_221_1 : expNegUpper (14601260303327331252741 / 178324779150858291200 : ℝ) ≤ (2756355322823547078660377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (189589 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_221 : rowCell 3 221 ≤ (209867008187839780017539 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (749915711782816573921837 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2756355322823547078660377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_221_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_221_1
  · norm_num [gridPoint]

theorem exp_3_222_0 : expNegUpper (14675251625906256928821 / 179228432653879347200 : ℝ) ≤ (5383505439436858779299 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (189589 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_222_1 : expNegUpper (146904680210953966177561 / 1792284326538793472000 : ℝ) ≤ (2532000312382373406978897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (474287 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_222 : rowCell 3 222 ≤ (385631604957048165830027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5383505439436858779299 / 1953125000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2532000312382373406978897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_222_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_222_1
  · norm_num [gridPoint]

theorem exp_3_223_0 : expNegUpper (16405248064059492381001 / 200149299986084352000 : ℝ) ≤ (20255998586326213852941 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (474287 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_223_1 : expNegUpper (513196936679558010481 / 6254665624565136000 : ℝ) ≤ (2325194036903434439283697 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1898411 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_223 : rowCell 3 223 ≤ (88547735042617661704681 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20255998586326213852941 / 8000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2325194036903434439283697 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_223_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_223_1
  · norm_num [gridPoint]

theorem sum_3_192_2 : blockSum (rowCell 3) 192 2 ≤ (4085598594091185630546327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_192) (by simpa only [blockSum_one] using cell_3_193) (by norm_num)

theorem sum_3_194_2 : blockSum (rowCell 3) 194 2 ≤ (3516014144907799203631171 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_194) (by simpa only [blockSum_one] using cell_3_195) (by norm_num)

theorem sum_3_192_4 : blockSum (rowCell 3) 192 4 ≤ (3800806369499492417088749 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_192_2 sum_3_194_2 (by norm_num)

theorem sum_3_196_2 : blockSum (rowCell 3) 196 2 ≤ (755304805129807939145113 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_196) (by simpa only [blockSum_one] using cell_3_197) (by norm_num)

theorem sum_3_198_2 : blockSum (rowCell 3) 198 2 ≤ (5184313349972571890261281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_198) (by simpa only [blockSum_one] using cell_3_199) (by norm_num)

theorem sum_3_196_4 : blockSum (rowCell 3) 196 4 ≤ (2245350358202207080684437 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_196_2 sum_3_198_2 (by norm_num)

theorem sum_3_192_8 : blockSum (rowCell 3) 192 8 ≤ (26429977269009005071777181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_192_4 sum_3_196_4 (by norm_num)

theorem sum_3_200_2 : blockSum (rowCell 3) 200 2 ≤ (4441483810308505340135069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_200) (by simpa only [blockSum_one] using cell_3_201) (by norm_num)

theorem sum_3_202_2 : blockSum (rowCell 3) 202 2 ≤ (759911430410465198974957 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_202) (by simpa only [blockSum_one] using cell_3_203) (by norm_num)

theorem sum_3_200_4 : blockSum (rowCell 3) 200 4 ≤ (4120520481180415667504927 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_200_2 sum_3_202_2 (by norm_num)

theorem sum_3_204_2 : blockSum (rowCell 3) 204 2 ≤ (81143914818405126373119 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_204) (by simpa only [blockSum_one] using cell_3_205) (by norm_num)

theorem sum_3_206_2 : blockSum (rowCell 3) 206 2 ≤ (2768769376981216700901331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_206) (by simpa only [blockSum_one] using cell_3_207) (by norm_num)

theorem sum_3_204_4 : blockSum (rowCell 3) 204 4 ≤ (6014525969717421755826091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_204_2 sum_3_206_2 (by norm_num)

theorem sum_3_200_8 : blockSum (rowCell 3) 200 8 ≤ (2851113386415650618167189 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_200_4 sum_3_204_4 (by norm_num)

theorem sum_3_192_16 : blockSum (rowCell 3) 192 16 ≤ (20342772100543629081306563 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_192_8 sum_3_200_8 (by norm_num)

theorem sum_3_208_2 : blockSum (rowCell 3) 208 2 ≤ (2358604278497399932263331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_208) (by simpa only [blockSum_one] using cell_3_209) (by norm_num)

theorem sum_3_210_2 : blockSum (rowCell 3) 210 2 ≤ (2006458774837183673302301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_210) (by simpa only [blockSum_one] using cell_3_211) (by norm_num)

theorem sum_3_208_4 : blockSum (rowCell 3) 208 4 ≤ (68204110208352868836963 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_208_2 sum_3_210_2 (by norm_num)

theorem sum_3_212_2 : blockSum (rowCell 3) 212 2 ≤ (1704595987055520210839833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_212) (by simpa only [blockSum_one] using cell_3_213) (by norm_num)

theorem sum_3_214_2 : blockSum (rowCell 3) 214 2 ≤ (723115649645049388738223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_214) (by simpa only [blockSum_one] using cell_3_215) (by norm_num)

theorem sum_3_212_4 : blockSum (rowCell 3) 212 4 ≤ (3150827286345618988316279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_212_2 sum_3_214_2 (by norm_num)

theorem sum_3_208_8 : blockSum (rowCell 3) 208 8 ≤ (7515890339680202593881911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_208_4 sum_3_212_4 (by norm_num)

theorem sum_3_216_2 : blockSum (rowCell 3) 216 2 ≤ (24508568651394349040289 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_216) (by simpa only [blockSum_one] using cell_3_217) (by norm_num)

theorem sum_3_218_2 : blockSum (rowCell 3) 218 2 ≤ (259251159603420212538377 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_218) (by simpa only [blockSum_one] using cell_3_219) (by norm_num)

theorem sum_3_216_4 : blockSum (rowCell 3) 216 4 ≤ (1131216535491699151083979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_216_2 sum_3_218_2 (by norm_num)

theorem sum_3_220_2 : blockSum (rowCell 3) 220 2 ≤ (219111149181956383818677 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_220) (by simpa only [blockSum_one] using cell_3_221) (by norm_num)

theorem sum_3_222_2 : blockSum (rowCell 3) 222 2 ≤ (739822545127518812648751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_222) (by simpa only [blockSum_one] using cell_3_223) (by norm_num)

theorem sum_3_220_4 : blockSum (rowCell 3) 220 4 ≤ (1616267141855344347923459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_220_2 sum_3_222_2 (by norm_num)

theorem sum_3_216_8 : blockSum (rowCell 3) 216 8 ≤ (3878700212838742650091417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_216_4 sum_3_220_4 (by norm_num)

theorem sum_3_208_16 : blockSum (rowCell 3) 208 16 ≤ (712161909532434077748333 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_208_8 sum_3_216_8 (by norm_num)

theorem sum_3_192_32 : blockSum (rowCell 3) 192 32 ≤ (26040067376803101703293227 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_192_16 sum_3_208_16 (by norm_num)

#print axioms sum_3_192_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
