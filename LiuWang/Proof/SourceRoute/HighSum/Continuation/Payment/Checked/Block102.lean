import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_192_0 : expNegUpper (387284870727226870769 / 4784759183237377600 : ℝ) ≤ (3523888397303873342212553 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470509 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_192_1 : expNegUpper (124039166226584437535311 / 1531122938635960832000 : ℝ) ≤ (65677466226411561893197 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1883073 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_192 : rowCell 6 192 ≤ (992856200282610182114647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3523888397303873342212553 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (65677466226411561893197 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_192_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_192_1
  · norm_num [gridPoint]

theorem exp_6_193_0 : expNegUpper (124717578400474079495879 / 1539497162799272448000 : ℝ) ≤ (41048404927974729309599 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1883073 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_193_1 : expNegUpper (62413403653122664897319 / 769748581399636224000 : ℝ) ≤ (6117903588439246263684043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1884117 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_193 : rowCell 6 193 ≤ (115631109613358779262681 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (41048404927974729309599 / 6250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6117903588439246263684043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_193_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_193_1
  · norm_num [gridPoint]

theorem exp_6_194_0 : expNegUpper (2510153308694266869679 / 30957884505366784000 : ℝ) ≤ (152947547460322828396653 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1884117 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_194_1 : expNegUpper (5024724759326542164077 / 61915769010733568000 : ℝ) ≤ (113931135000724432050399 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (117823 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_194 : rowCell 6 194 ≤ (215380234799400717785651 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (152947547460322828396653 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (113931135000724432050399 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_194_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_194_1
  · norm_num [gridPoint]

theorem exp_6_195_0 : expNegUpper (126301429727769037339357 / 1556314126043161088000 : ℝ) ≤ (5696555193407980720414243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (117823 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_195_1 : expNegUpper (31603277812419439296559 / 389078531510790272000 : ℝ) ≤ (2651045762575835028736407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (75449 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_195 : rowCell 6 195 ≤ (80203120031403094065977 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5696555193407980720414243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2651045762575835028736407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_195_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_195_1
  · norm_num [gridPoint]

theorem exp_6_196_0 : expNegUpper (31774720317994951947791 / 391189216280934528000 : ℝ) ≤ (5302090091927536870175349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (75449 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_196_1 : expNegUpper (25442358819625317155327 / 312951373024747622400 : ℝ) ≤ (4932969396861132865988587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1887289 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_196 : rowCell 6 196 ≤ (746349733483729255731541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5302090091927536870175349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4932969396861132865988587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_196_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_196_1
  · norm_num [gridPoint]

theorem exp_6_197_0 : expNegUpper (25580006011936860313687 / 314644488502014054400 : ℝ) ≤ (986593615549359410374941 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1887289 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_197_1 : expNegUpper (64007088760424343301093 / 786611221255035136000 : ℝ) ≤ (917545115836942624269797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1888359 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_197 : rowCell 6 197 ≤ (694257535211653121235143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (986593615549359410374941 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (917545115836942624269797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_197_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_197_1
  · norm_num [gridPoint]

theorem exp_6_198_0 : expNegUpper (64352443041610582700117 / 790855429101078784000 : ℝ) ≤ (229386218277048487436339 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1888359 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_198_1 : expNegUpper (128820271510182706391953 / 1581710858202157568000 : ℝ) ≤ (852993329223466124642311 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (377887 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_198 : rowCell 6 198 ≤ (40346636384981503117249 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (229386218277048487436339 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (852993329223466124642311 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_198_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_198_1
  · norm_num [gridPoint]

theorem exp_6_199_0 : expNegUpper (1657772279487091789 / 20354843036160000 : ℝ) ≤ (4264965529917958089160029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (377887 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_199_1 : expNegUpper (207408137693547667 / 2544355379520000 : ℝ) ≤ (1981684068330796341982007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (945259 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_199 : rowCell 6 199 ≤ (600017483610509409941353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4264965529917958089160029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1981684068330796341982007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_199_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_199_1
  · norm_num [gridPoint]

theorem exp_6_200_0 : expNegUpper (16290719975893323767959 / 199844525562949696000 : ℝ) ≤ (1981683555226789022719277 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (945259 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_200_1 : expNegUpper (130443631158041089780391 / 1598756204503597568000 : ℝ) ≤ (73633442946945673662237 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (236451 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_200 : rowCell 6 200 ≤ (111496626253759403541521 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1981683555226789022719277 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (73633442946945673662237 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_200_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_200_1
  · norm_num [gridPoint]

theorem exp_6_201_0 : expNegUpper (6902199868011181290181 / 84595428163839488000 : ℝ) ≤ (920417801053324190099159 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (236451 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_201_1 : expNegUpper (690846930532856562301 / 8459542816383948800 : ℝ) ≤ (3418684922690593291598077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1892703 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_201 : rowCell 6 201 ≤ (258882174000019713902587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (920417801053324190099159 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3418684922690593291598077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_201_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_201_1
  · norm_num [gridPoint]

theorem exp_6_202_0 : expNegUpper (13196158238246525585399 / 161589290402805811200 : ℝ) ≤ (854671014053403015953693 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1892703 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_202_1 : expNegUpper (132081952980410909774461 / 1615892904028058112000 : ℝ) ≤ (3173274453062719487128269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (378761 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_202 : rowCell 6 202 ≤ (96138307391830654929779 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (854671014053403015953693 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3173274453062719487128269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_202_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_202_1
  · norm_num [gridPoint]

theorem exp_6_203_0 : expNegUpper (132785124470243670894389 / 1624495511248921088000 : ℝ) ≤ (3173273657292710766365731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (378761 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_203_1 : expNegUpper (33226687421971056330317 / 406123877812230272000 : ℝ) ≤ (2944368088502268522409309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1894913 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_203 : rowCell 6 203 ≤ (446103932422125877414181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3173273657292710766365731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2944368088502268522409309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_203_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_203_1
  · norm_num [gridPoint]

theorem exp_6_204_0 : expNegUpper (1336124337478863363637 / 16331209567755392000 : ℝ) ≤ (92011479935150926374039 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1894913 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_204_1 : expNegUpper (5349412676640053608267 / 65324838271021568000 : ℝ) ≤ (2730950176119398446083671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1896027 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_204 : rowCell 6 204 ≤ (206924626750301052593917 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (92011479935150926374039 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2730950176119398446083671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_204_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_204_1
  · norm_num [gridPoint]

theorem exp_6_205_0 : expNegUpper (4336887748636512870677 / 52960298084126208000 : ℝ) ≤ (341368688203283463419319 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1896027 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_205_1 : expNegUpper (2170446204146788728383 / 26480149042063104000 : ℝ) ≤ (2532059727902022487320747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (474287 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_205 : rowCell 6 205 ≤ (76756672358748233813789 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (341368688203283463419319 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2532059727902022487320747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_205_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_205_1
  · norm_num [gridPoint]

theorem exp_6_206_0 : expNegUpper (67639196921059502752657 / 825220181373020416000 : ℝ) ≤ (1266029556381684134983783 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (474287 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_206_1 : expNegUpper (27080760580704310981909 / 330088072549208166400 : ℝ) ≤ (117339406247269377721419 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (949137 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_206 : rowCell 6 206 ≤ (2779452530570606278713 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1266029556381684134983783 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (117339406247269377721419 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_206_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_206_1
  · norm_num [gridPoint]

theorem exp_6_207_0 : expNegUpper (27223412928677260527149 / 331826864637984870400 : ℝ) ≤ (1173393780391894219967239 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (949137 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_207_1 : expNegUpper (8515233852975121761571 / 103695895199370272000 : ℝ) ≤ (2174276863385469160908747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1899407 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_207 : rowCell 6 207 ≤ (5151251245378763340951 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1173393780391894219967239 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2174276863385469160908747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_207_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_207_1
  · norm_num [gridPoint]

theorem exp_6_208_0 : expNegUpper (8559971412742027319459 / 104240695121222688000 : ℝ) ≤ (2174276346151499866865277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1899407 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_208_1 : expNegUpper (137087490881680727715583 / 1667851121939563008000 : ℝ) ≤ (1006857673311561997961473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950273 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_208 : rowCell 6 208 ≤ (76348029221478012318911 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2174276346151499866865277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1006857673311561997961473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_208_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_208_1
  · norm_num [gridPoint]

theorem exp_6_209_0 : expNegUpper (5512233508636642226447 / 67063630359798272000 : ℝ) ≤ (1006857436286232295682703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950273 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_209_1 : expNegUpper (2758701211961930804599 / 33531815179899136000 : ℝ) ≤ (932169363889421740460419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (190169 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_209 : rowCell 6 209 ≤ (14139557636319947512973 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1006857436286232295682703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (932169363889421740460419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_209_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_209_1
  · norm_num [gridPoint]

theorem exp_6_210_0 : expNegUpper (69327979985927902507151 / 842676617178052864000 : ℝ) ≤ (1864338293450832057558329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (190169 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_210_1 : expNegUpper (138786460789188032457301 / 1685353234356105728000 : ℝ) ≤ (1725425805716096816930481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1902841 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_210 : rowCell 6 210 ≤ (52353764657987059763077 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1864338293450832057558329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1725425805716096816930481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_210_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_210_1
  · norm_num [gridPoint]

theorem exp_6_211_0 : expNegUpper (139509919364030331899789 / 1694138548023009792000 : ℝ) ≤ (862712703956824287915639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1902841 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_211_1 : expNegUpper (1396417014472938511267 / 16941385480230097920 : ℝ) ≤ (798148488706661085772801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (951999 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_211 : rowCell 6 211 ≤ (242222980697998274099003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (862712703956824287915639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (798148488706661085772801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_211_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_211_1
  · norm_num [gridPoint]

theorem exp_6_212_0 : expNegUpper (1403677258847782830467 / 17029466999956689920 : ℝ) ≤ (1596296613184140710558431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (951999 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_212_1 : expNegUpper (140500792564752642967211 / 1702946699995668992000 : ℝ) ≤ (59052489957966778879241 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1905161 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_212 : rowCell 6 212 ≤ (44811479754757110281329 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1596296613184140710558431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (59052489957966778879241 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_212_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_212_1
  · norm_num [gridPoint]

theorem exp_6_213_0 : expNegUpper (141229389526438305184099 / 1711777690274083328000 : ℝ) ≤ (369077978892044727218467 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1905161 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_213_1 : expNegUpper (70681872066951527353949 / 855888845137041664000 : ℝ) ≤ (1364869306891059773913287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1906329 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_213 : rowCell 6 213 ≤ (103590743682741118985547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (369077978892044727218467 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1364869306891059773913287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_213_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_213_1
  · norm_num [gridPoint]

theorem exp_6_214_0 : expNegUpper (2841898405626980900821 / 34412630377165056000 : ℝ) ≤ (341217250460997299229609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1906329 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_214_1 : expNegUpper (5689222645883349323113 / 68825260754330112000 : ℝ) ≤ (1261401651441861272109967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (119219 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_214 : rowCell 6 214 ≤ (23938751947205534713479 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (341217250460997299229609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1261401651441861272109967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_214_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_214_1
  · norm_num [gridPoint]

theorem exp_6_215_0 : expNegUpper (142964328141849149346617 / 1729508185748177408000 : ℝ) ≤ (630700686204957929095841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (119219 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_215_1 : expNegUpper (17887658574579165600757 / 216188523218522176000 : ℝ) ≤ (116537679230178313008457 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (477171 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_215 : rowCell 6 215 ≤ (35392568815856889678433 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (630700686204957929095841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (116537679230178313008457 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_215_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_215_1
  · norm_num [gridPoint]

theorem exp_6_216_0 : expNegUpper (17979702887534658103733 / 217300961367982144000 : ℝ) ≤ (1165376537147339098479463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (477171 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_216_1 : expNegUpper (28795172294978095324331 / 347681538188771430400 : ℝ) ≤ (1076294507840702104662669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (190987 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_216 : rowCell 6 216 ≤ (163464666601857445976393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1165376537147339098479463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1076294507840702104662669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_216_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_216_1
  · norm_num [gridPoint]

theorem exp_6_217_0 : expNegUpper (28942963029794407643971 / 349466006889058406400 : ℝ) ≤ (1076294274593965467413021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (190987 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_217_1 : expNegUpper (72427177387096917626843 / 873665017222646016000 : ℝ) ≤ (39747406713931250891267 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (955531 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_217 : rowCell 6 217 ≤ (150944760690043951464593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1076294274593965467413021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39747406713931250891267 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_217_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_217_1
  · norm_num [gridPoint]

theorem exp_6_218_0 : expNegUpper (72797957140136058122827 / 878137608126241024000 : ℝ) ≤ (993684954694853094441347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (955531 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_218_1 : expNegUpper (145736758486882047431213 / 1756275216252482048000 : ℝ) ≤ (917108119833619232233563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (95613 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_218 : rowCell 6 218 ≤ (139336747722769098735491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (993684954694853094441347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (917108119833619232233563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_218_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_218_1
  · norm_num [gridPoint]

theorem exp_6_219_0 : expNegUpper (5859237219460645825453 / 70609729454617088000 : ℝ) ≤ (917107925102912813434201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (95613 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_219_1 : expNegUpper (1466230826052937598833 / 17652432363654272000 : ℝ) ≤ (846150138580986071781009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1913463 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_219 : rowCell 6 219 ≤ (64289181090498248856399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (917107925102912813434201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (846150138580986071781009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_219_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_219_1
  · norm_num [gridPoint]

theorem exp_6_220_0 : expNegUpper (1939077286316352277907 / 23345185457685888000 : ℝ) ≤ (33845998429417764018241 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1913463 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_220_1 : expNegUpper (7763859848514085228369 / 93380741830743552000 : ℝ) ≤ (780423938431675109104361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (119667 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_220 : rowCell 6 220 ≤ (118611230102253865719809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33845998429417764018241 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (780423938431675109104361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_220_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_220_1
  · norm_num [gridPoint]

theorem exp_6_221_0 : expNegUpper (148262754093190645428539 / 1783247791508582912000 : ℝ) ≤ (31216951042269496584761 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (119667 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_221_1 : expNegUpper (14840753202864227252741 / 178324779150858291200 : ℝ) ≤ (89945843444045668204257 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1915887 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_221 : rowCell 6 221 ≤ (27345164157327957082729 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31216951042269496584761 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (89945843444045668204257 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_221_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_221_1
  · norm_num [gridPoint]

theorem exp_6_222_0 : expNegUpper (14915958147829840928821 / 179228432653879347200 : ℝ) ≤ (359783299673570188342649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1915887 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_222_1 : expNegUpper (149305677318256366177561 / 1792284326538793472000 : ℝ) ≤ (663238943265918535360973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (479277 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_222 : rowCell 6 222 ≤ (100835422531698947286531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (359783299673570188342649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (663238943265918535360973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_222_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_222_1
  · norm_num [gridPoint]

theorem exp_6_223_0 : expNegUpper (150060365907704711429009 / 1801343699874759168000 : ℝ) ≤ (663238808034514121100391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (479277 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_223_1 : expNegUpper (4693993218217142094329 / 56291990621086224000 : ℝ) ≤ (305561373679768023863751 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (959167 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_223 : rowCell 6 223 ≤ (92927589553544062652879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (663238808034514121100391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (305561373679768023863751 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_223_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_223_1
  · norm_num [gridPoint]

theorem sum_6_192_2 : blockSum (rowCell 6) 192 2 ≤ (383581015437896083243219 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_192) (by simpa only [blockSum_one] using cell_6_193) (by norm_num)

theorem sum_6_194_2 : blockSum (rowCell 6) 194 2 ≤ (831776069755816905901187 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_194) (by simpa only [blockSum_one] using cell_6_195) (by norm_num)

theorem sum_6_192_4 : blockSum (rowCell 6) 192 4 ≤ (3581457216701114228018469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_192_2 sum_6_194_2 (by norm_num)

theorem sum_6_196_2 : blockSum (rowCell 6) 196 2 ≤ (360151817173845594241671 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_196) (by simpa only [blockSum_one] using cell_6_197) (by norm_num)

theorem sum_6_198_2 : blockSum (rowCell 6) 198 2 ≤ (1245563665770213459817337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_198) (by simpa only [blockSum_one] using cell_6_199) (by norm_num)

theorem sum_6_196_4 : blockSum (rowCell 6) 196 4 ≤ (2686170934465595836784021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_196_2 sum_6_198_2 (by norm_num)

theorem sum_6_192_8 : blockSum (rowCell 6) 192 8 ≤ (626762815116671006480249 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_192_4 sum_6_196_4 (by norm_num)

theorem sum_6_200_2 : blockSum (rowCell 6) 200 2 ≤ (1075247479268836445512779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_200) (by simpa only [blockSum_one] using cell_6_201) (by norm_num)

theorem sum_6_202_2 : blockSum (rowCell 6) 202 2 ≤ (231698867345319788015769 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_202) (by simpa only [blockSum_one] using cell_6_203) (by norm_num)

theorem sum_6_200_4 : blockSum (rowCell 6) 200 4 ≤ (400408589730023119515171 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_200_2 sum_6_202_2 (by norm_num)

theorem sum_6_204_2 : blockSum (rowCell 6) 204 2 ≤ (797632615294343274256779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_204) (by simpa only [blockSum_one] using cell_6_205) (by norm_num)

theorem sum_6_206_2 : blockSum (rowCell 6) 206 2 ≤ (10710156306519975898377 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_206) (by simpa only [blockSum_one] using cell_6_207) (by norm_num)

theorem sum_6_204_4 : blockSum (rowCell 6) 204 4 ≤ (1483082618911621731752907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_204_2 sum_6_206_2 (by norm_num)

theorem sum_6_200_8 : blockSum (rowCell 6) 200 8 ≤ (1742562783780868664664381 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_200_4 sum_6_204_4 (by norm_num)

theorem sum_6_192_16 : blockSum (rowCell 6) 192 16 ≤ (2438188429682111848532813 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_192_8 sum_6_200_8 (by norm_num)

theorem sum_6_208_2 : blockSum (rowCell 6) 208 2 ≤ (1148795448461544920967 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_208) (by simpa only [blockSum_one] using cell_6_209) (by norm_num)

theorem sum_6_210_2 : blockSum (rowCell 6) 210 2 ≤ (125997950996983393228597 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_210) (by simpa only [blockSum_one] using cell_6_211) (by norm_num)

theorem sum_6_208_4 : blockSum (rowCell 6) 208 4 ≤ (273043768400061143112373 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_208_2 sum_6_210_2 (by norm_num)

theorem sum_6_212_2 : blockSum (rowCell 6) 212 2 ≤ (431238886139267789377739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_212) (by simpa only [blockSum_one] using cell_6_213) (by norm_num)

theorem sum_6_214_2 : blockSum (rowCell 6) 214 2 ≤ (368472859656928726099997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_214) (by simpa only [blockSum_one] using cell_6_215) (by norm_num)

theorem sum_6_212_4 : blockSum (rowCell 6) 212 4 ≤ (99963968224524564434717 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_212_2 sum_6_214_2 (by norm_num)

theorem sum_6_208_8 : blockSum (rowCell 6) 208 8 ≤ (472971704849110271981807 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_208_4 sum_6_212_4 (by norm_num)

theorem sum_6_216_2 : blockSum (rowCell 6) 216 2 ≤ (157204713645950698720493 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_216) (by simpa only [blockSum_one] using cell_6_217) (by norm_num)

theorem sum_6_218_2 : blockSum (rowCell 6) 218 2 ≤ (267915109903765596448289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_218) (by simpa only [blockSum_one] using cell_6_219) (by norm_num)

theorem sum_6_216_4 : blockSum (rowCell 6) 216 4 ≤ (23292981487826679755571 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_216_2 sum_6_218_2 (by norm_num)

theorem sum_6_220_2 : blockSum (rowCell 6) 220 2 ≤ (9119675469262627762029 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_220) (by simpa only [blockSum_one] using cell_6_221) (by norm_num)

theorem sum_6_222_2 : blockSum (rowCell 6) 222 2 ≤ (19376301208524300993941 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_222) (by simpa only [blockSum_one] using cell_6_223) (by norm_num)

theorem sum_6_220_4 : blockSum (rowCell 6) 220 4 ≤ (84350979763361740798027 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_220_2 sum_6_222_2 (by norm_num)

theorem sum_6_216_8 : blockSum (rowCell 6) 216 8 ≤ (100407943601247569787941 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_216_4 sum_6_220_4 (by norm_num)

theorem sum_6_208_16 : blockSum (rowCell 6) 208 16 ≤ (1447983127704458392903319 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_208_8 sum_6_216_8 (by norm_num)

theorem sum_6_192_32 : blockSum (rowCell 6) 192 32 ≤ (1264871997413736417993789 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_192_16 sum_6_208_16 (by norm_num)

#print axioms sum_6_192_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
