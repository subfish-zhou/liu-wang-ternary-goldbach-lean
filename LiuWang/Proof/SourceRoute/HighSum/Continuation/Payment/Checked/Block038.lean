import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_192_0 : expNegUpper (371987845431252470769 / 4784759183237377600 : ℝ) ≤ (17238728583716657305102769 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_192_1 : expNegUpper (119157467978126197535311 / 1531122938635960832000 : ℝ) ≤ (159251257701932145124031507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459187 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_192 : rowCell 2 192 ≤ (3022922568921879929791241 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17238728583716657305102769 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (159251257701932145124031507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_192_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_192_1
  · norm_num [gridPoint]

theorem exp_2_193_0 : expNegUpper (39936393486502901165293 / 513165720933090816000 : ℝ) ≤ (159251218377666787013033177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459187 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_193_1 : expNegUpper (19988626535255586965773 / 256582860466545408000 : ℝ) ≤ (73531447670837698047787027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1837891 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_193 : rowCell 2 193 ≤ (5584175094125244178443069 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (159251218377666787013033177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (73531447670837698047787027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_193_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_193_1
  · norm_num [gridPoint]

theorem exp_2_194_0 : expNegUpper (344531193278555427097 / 4422554929338112000 : ℝ) ≤ (147062859420574138239966617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1837891 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_194_1 : expNegUpper (689769834526846732011 / 8845109858676224000 : ℝ) ≤ (67879298887226677154999137 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_194 : rowCell 2 194 ≤ (10311797378032176707128139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (147062859420574138239966617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (67879298887226677154999137 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_194_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_194_1
  · norm_num [gridPoint]

theorem exp_2_195_0 : expNegUpper (121366332094296525339357 / 1556314126043161088000 : ℝ) ≤ (8484910310801068835958893 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_195_1 : expNegUpper (30372840865614703296559 / 389078531510790272000 : ℝ) ≤ (62639291375617998327276089 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (920097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_195 : rowCell 2 195 ≤ (9517531668800180118647583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8484910310801068835958893 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (62639291375617998327276089 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_195_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_195_1
  · norm_num [gridPoint]

theorem exp_2_196_0 : expNegUpper (10179202816021143982597 / 130396405426978176000 : ℝ) ≤ (125278552807953245694590977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (920097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_196_1 : expNegUpper (8151779764310271585109 / 104317124341582540800 : ℝ) ≤ (4622669239344075059785077 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (920677 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_196 : rowCell 2 196 ≤ (8781327239257427992671431 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (125278552807953245694590977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4622669239344075059785077 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_196_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_196_1
  · norm_num [gridPoint]

theorem exp_2_197_0 : expNegUpper (24587646546740930713687 / 314644488502014054400 : ℝ) ≤ (115566703658453106921132311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (920677 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_197_1 : expNegUpper (61532865020561303301093 / 786611221255035136000 : ℝ) ≤ (106570394491577504759133117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_197 : rowCell 2 197 ≤ (16198436773399351371852637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (115566703658453106921132311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (106570394491577504759133117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_197_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_197_1
  · norm_num [gridPoint]

theorem exp_2_198_0 : expNegUpper (61864869455493974700117 / 790855429101078784000 : ℝ) ≤ (26642592390914263877816769 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_198_1 : expNegUpper (123858474184203058391953 / 1581710858202157568000 : ℝ) ≤ (98240212134068049939093961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1843693 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_198 : rowCell 2 198 ≤ (2986994325381021747867951 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26642592390914263877816769 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (98240212134068049939093961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_198_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_198_1
  · norm_num [gridPoint]

theorem exp_2_199_0 : expNegUpper (2656532529417434923 / 33924738393600000 : ℝ) ≤ (19648037880063253693100959 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1843693 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_199_1 : expNegUpper (332413170363290869 / 4240592299200000 : ℝ) ≤ (90529932314260336727040861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (184487 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_199 : rowCell 2 199 ≤ (13765286873583153990559157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19648037880063253693100959 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (90529932314260336727040861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_199_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_199_1
  · norm_num [gridPoint]

theorem exp_2_200_0 : expNegUpper (15665489117800779767959 / 199844525562949696000 : ℝ) ≤ (90529911588099139946756957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (184487 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_200_1 : expNegUpper (125455134139554305780391 / 1598756204503597568000 : ℝ) ≤ (83396242821518515904563207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923027 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_200 : rowCell 2 200 ≤ (6341425720664335927770473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (90529911588099139946756957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (83396242821518515904563207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_200_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_200_1
  · norm_num [gridPoint]

theorem exp_2_201_0 : expNegUpper (18018085825888360644777 / 229616162158992896000 : ℝ) ≤ (4169811196579192497129707 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923027 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_201_1 : expNegUpper (1803700999092891354817 / 22961616215899289600 : ℝ) ≤ (76798607743877673157261781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1847243 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_201 : rowCell 2 201 ≤ (5840775525409368843451827 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4169811196579192497129707 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (76798607743877673157261781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_201_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_201_1
  · norm_num [gridPoint]

theorem exp_2_202_0 : expNegUpper (4231101194173925595133 / 53863096800935270400 : ℝ) ≤ (76798590532842695610036273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1847243 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_202_1 : expNegUpper (42355585423138996591487 / 538630968009352704000 : ℝ) ≤ (70699111361050790458745041 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1848437 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_202 : rowCell 2 202 ≤ (1344458117446157287383053 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (76798590532842695610036273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (70699111361050790458745041 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_202_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_202_1
  · norm_num [gridPoint]

theorem exp_2_203_0 : expNegUpper (127743228066742614894389 / 1624495511248921088000 : ℝ) ≤ (4418693480283370351868651 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1848437 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_203_1 : expNegUpper (31969550782659184330317 / 406123877812230272000 : ℝ) ≤ (32531154453342075738162913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (924819 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_203 : rowCell 2 203 ≤ (4949921797964279802538511 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4418693480283370351868651 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32531154453342075738162913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_203_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_203_1
  · norm_num [gridPoint]

theorem exp_2_204_0 : expNegUpper (1285571874981317123637 / 16331209567755392000 : ℝ) ≤ (65062294632236484962306321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (924819 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_204_1 : expNegUpper (5147736820500011368267 / 65324838271021568000 : ℝ) ≤ (59855084070215265761179833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1850843 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_204 : rowCell 2 204 ≤ (9109087485440209646751401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (65062294632236484962306321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (59855084070215265761179833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_204_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_204_1
  · norm_num [gridPoint]

theorem exp_2_205_0 : expNegUpper (1391128216255093623559 / 17653432694708736000 : ℝ) ≤ (187047097113693905011643 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1850843 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_205_1 : expNegUpper (696303324770678909461 / 8826716347354368000 : ℝ) ≤ (55046513092901746248350961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (370411 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_205 : rowCell 2 205 ≤ (8378726749516201484443771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (187047097113693905011643 / 3125000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (55046513092901746248350961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_205_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_205_1
  · norm_num [gridPoint]

theorem exp_2_206_0 : expNegUpper (65098223949928622752657 / 825220181373020416000 : ℝ) ≤ (137616253170882698394063 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (370411 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_206_1 : expNegUpper (26067041361502672581909 / 330088072549208166400 : ℝ) ≤ (10121547059840468091023907 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (231659 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_206 : rowCell 2 206 ≤ (1540880370846861475163567 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (137616253170882698394063 / 2500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10121547059840468091023907 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_206_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_206_1
  · norm_num [gridPoint]

theorem exp_2_207_0 : expNegUpper (26204353770974194927149 / 331826864637984870400 : ℝ) ≤ (632596556774104637347559 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (231659 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_207_1 : expNegUpper (8197612231583761761571 / 103695895199370272000 : ℝ) ≤ (46511829893513006507010001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (927247 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_207 : rowCell 2 207 ≤ (7082045165282073338784483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (632596556774104637347559 / 12500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (46511829893513006507010001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_207_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_207_1
  · norm_num [gridPoint]

theorem exp_2_208_0 : expNegUpper (392413383836617681879 / 4963842624820128000 : ℝ) ≤ (23255910055039636643057611 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (927247 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_208_1 : expNegUpper (6285342623484066653123 / 79421481997122048000 : ℝ) ≤ (534171235538874499674769 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (927861 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_208 : rowCell 2 208 ≤ (1626965855896873348819503 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23255910055039636643057611 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (534171235538874499674769 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_208_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_208_1
  · norm_num [gridPoint]

theorem exp_2_209_0 : expNegUpper (5307353689395743666447 / 67063630359798272000 : ℝ) ≤ (21366844973984374431664029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (927861 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_209_1 : expNegUpper (2656528299266552884599 / 33531815179899136000 : ℝ) ≤ (39249955660854619763485029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (371391 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_209 : rowCell 2 209 ≤ (5978321094977001717512461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21366844973984374431664029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39249955660854619763485029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_209_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_209_1
  · norm_num [gridPoint]

theorem exp_2_210_0 : expNegUpper (66760307322289886507151 / 842676617178052864000 : ℝ) ≤ (19624973787854229113131403 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (371391 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_210_1 : expNegUpper (133664465308165568457301 / 1685353234356105728000 : ℝ) ≤ (36038819895607385107253531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (929097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_210 : rowCell 2 210 ≤ (5490124566260376306208007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19624973787854229113131403 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36038819895607385107253531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_210_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_210_1
  · norm_num [gridPoint]

theorem exp_2_211_0 : expNegUpper (44787074730166910633263 / 564712849341003264000 : ℝ) ≤ (18019406274410517053663363 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (929097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_211_1 : expNegUpper (448354520400059397089 / 5647128493410032640 : ℝ) ≤ (6616003426844349230388729 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (929719 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_211 : rowCell 2 211 ≤ (1008041431887204579050777 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18019406274410517053663363 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6616003426844349230388729 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_211_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_211_1
  · norm_num [gridPoint]

theorem exp_2_212_0 : expNegUpper (1352056808649951150467 / 17029466999956689920 : ℝ) ≤ (6616002092055854653980257 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (929719 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_212_1 : expNegUpper (135352097391223042967211 / 1702946699995668992000 : ℝ) ≤ (3794335539537438433726477 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1860687 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_212 : rowCell 2 212 ≤ (4625714935216713024038201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6616002092055854653980257 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3794335539537438433726477 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_212_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_212_1
  · norm_num [gridPoint]

theorem exp_2_213_0 : expNegUpper (136053994660401569184099 / 1711777690274083328000 : ℝ) ≤ (30354678255303238815732011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1860687 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_213_1 : expNegUpper (68100849557059943353949 / 855888845137041664000 : ℝ) ≤ (27845280161442576932570999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (930971 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_213 : rowCell 2 213 ≤ (1060998314193561232358773 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30354678255303238815732011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27845280161442576932570999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_213_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_213_1
  · norm_num [gridPoint]

theorem exp_2_214_0 : expNegUpper (912707837127058273607 / 11470876792388352000 : ℝ) ≤ (27845274658650928391737309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (930971 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_214_1 : expNegUpper (1827402283747293294371 / 22941753584776704000 : ℝ) ≤ (25535500508405998982695147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (931601 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_214 : rowCell 2 214 ≤ (3892574084471980296851803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27845274658650928391737309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25535500508405998982695147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_214_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_214_1
  · norm_num [gridPoint]

theorem exp_2_215_0 : expNegUpper (19680319083329325335231 / 247072597964025344000 : ℝ) ≤ (2553549551380737980587079 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (931601 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_215_1 : expNegUpper (2462723640791839657251 / 30884074745503168000 : ℝ) ≤ (23410198366218181461664393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1864467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_215 : rowCell 2 215 ≤ (3569163972378309263093867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2553549551380737980587079 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23410198366218181461664393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_215_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_215_1
  · norm_num [gridPoint]

theorem exp_2_216_0 : expNegUpper (17327772336934978103733 / 217300961367982144000 : ℝ) ≤ (5852548458534586377161667 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1864467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_216_1 : expNegUpper (27754753383269320924331 / 347681538188771430400 : ℝ) ≤ (2145530847887322393238649 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (932869 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_216 : rowCell 2 216 ≤ (1635816368757268994986029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5852548458534586377161667 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2145530847887322393238649 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_216_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_216_1
  · norm_num [gridPoint]

theorem exp_2_217_0 : expNegUpper (9299068059861402014657 / 116488668963019468800 : ℝ) ≤ (21455304367613616316142857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (932869 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_217_1 : expNegUpper (23273151728232732542281 / 291221672407548672000 : ℝ) ≤ (19657776207510488320253539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (933507 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_217 : rowCell 2 217 ≤ (599600554614275784629757 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21455304367613616316142857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19657776207510488320253539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_217_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_217_1
  · norm_num [gridPoint]

theorem exp_2_218_0 : expNegUpper (70176885091483770122827 / 878137608126241024000 : ℝ) ≤ (4914443119753824528362471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (933507 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_218_1 : expNegUpper (140507964235831039431213 / 1756275216252482048000 : ℝ) ≤ (18005490536979340202677399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (373659 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_218 : rowCell 2 218 ≤ (171652436075887184918429 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4914443119753824528362471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18005490536979340202677399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_218_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_218_1
  · norm_num [gridPoint]

theorem exp_2_219_0 : expNegUpper (5649017461718320065453 / 70609729454617088000 : ℝ) ≤ (2250685894566140450526993 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (373659 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_219_1 : expNegUpper (1413809385079891838833 / 17652432363654272000 : ℝ) ≤ (16487221017251036606543161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1869581 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_219 : rowCell 2 219 ≤ (628809817393637290795311 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2250685894566140450526993 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16487221017251036606543161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_219_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_219_1
  · norm_num [gridPoint]

theorem exp_2_220_0 : expNegUpper (11841752497519255093411 / 147852841232010624000 : ℝ) ≤ (1030451122073807492229211 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1869581 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_220_1 : expNegUpper (47419281059403158446337 / 591411364928042496000 : ℝ) ≤ (7546279227100442096530297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (233859 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_220 : rowCell 2 220 ≤ (2302825668081647159781237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1030451122073807492229211 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7546279227100442096530297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_220_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_220_1
  · norm_num [gridPoint]

theorem exp_2_221_0 : expNegUpper (142980560457125365428539 / 1783247791508582912000 : ℝ) ≤ (7546277838820746049958127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (233859 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_221_1 : expNegUpper (14313868823883056052741 / 178324779150858291200 : ℝ) ≤ (13811859168764710909147399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1872169 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_221 : rowCell 2 221 ≤ (1053867949705076945746969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7546277838820746049958127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13811859168764710909147399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_221_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_221_1
  · norm_num [gridPoint]

theorem exp_2_222_0 : expNegUpper (2055200542799708018403 / 25604061807697049600 : ℝ) ≤ (13811856653404094782413541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1872169 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_222_1 : expNegUpper (20574783383170155168223 / 256040618076970496000 : ℝ) ≤ (3159048162075892460995163 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1873471 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_222 : rowCell 2 222 ≤ (1928615516999817407536603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13811856653404094782413541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3159048162075892460995163 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_222_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_222_1
  · norm_num [gridPoint]

theorem exp_2_223_0 : expNegUpper (48250490859710765143003 / 600447899958253056000 : ℝ) ≤ (12636190370168529876695423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1873471 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_223_1 : expNegUpper (1509502494798226031443 / 18763996873695408000 : ℝ) ≤ (5778646209562401673658793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1874777 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_223 : rowCell 2 223 ≤ (882105250663731682212049 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12636190370168529876695423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5778646209562401673658793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_223_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_223_1
  · norm_num [gridPoint]

theorem sum_2_192_2 : blockSum (rowCell 2) 192 2 ≤ (11630020231969004038025551 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_192) (by simpa only [blockSum_one] using cell_2_193) (by norm_num)

theorem sum_2_194_2 : blockSum (rowCell 2) 194 2 ≤ (9914664523416178412887861 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_194) (by simpa only [blockSum_one] using cell_2_195) (by norm_num)

theorem sum_2_192_4 : blockSum (rowCell 2) 192 4 ≤ (5386171188846295612728353 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_192_2 sum_2_194_2 (by norm_num)

theorem sum_2_196_2 : blockSum (rowCell 2) 196 2 ≤ (33761091251914207357195499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_196) (by simpa only [blockSum_one] using cell_2_197) (by norm_num)

theorem sum_2_198_2 : blockSum (rowCell 2) 198 2 ≤ (896883078140258210309341 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_198) (by simpa only [blockSum_one] using cell_2_199) (by norm_num)

theorem sum_2_196_4 : blockSum (rowCell 2) 196 4 ≤ (62461349752402470087094411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_196_2 sum_2_198_2 (by norm_num)

theorem sum_2_192_8 : blockSum (rowCell 2) 192 8 ≤ (148640088773943199890748059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_192_4 sum_2_196_4 (by norm_num)

theorem sum_2_200_2 : blockSum (rowCell 2) 200 2 ≤ (121822012460737047712223 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_200) (by simpa only [blockSum_one] using cell_2_201) (by norm_num)

theorem sum_2_202_2 : blockSum (rowCell 2) 202 2 ≤ (10327754267748908952070723 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_202) (by simpa only [blockSum_one] using cell_2_203) (by norm_num)

theorem sum_2_200_4 : blockSum (rowCell 2) 200 4 ≤ (22509955513822613723293023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_200_2 sum_2_202_2 (by norm_num)

theorem sum_2_204_2 : blockSum (rowCell 2) 204 2 ≤ (4371953558739102782798793 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_204) (by simpa only [blockSum_one] using cell_2_205) (by norm_num)

theorem sum_2_206_2 : blockSum (rowCell 2) 206 2 ≤ (7393223509758190357301159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_206) (by simpa only [blockSum_one] using cell_2_207) (by norm_num)

theorem sum_2_204_4 : blockSum (rowCell 2) 204 4 ≤ (3227426125447279184579749 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_204_2 sum_2_206_2 (by norm_num)

theorem sum_2_200_8 : blockSum (rowCell 2) 200 8 ≤ (4830885767632376205773971 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_200_4 sum_2_204_4 (by norm_num)

theorem sum_2_192_16 : blockSum (rowCell 2) 192 16 ≤ (45186852211212243836626319 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_192_8 sum_2_200_8 (by norm_num)

theorem sum_2_208_2 : blockSum (rowCell 2) 208 2 ≤ (12486184518564495112790473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_208) (by simpa only [blockSum_one] using cell_2_209) (by norm_num)

theorem sum_2_210_2 : blockSum (rowCell 2) 210 2 ≤ (2632582931424099800365473 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_210) (by simpa only [blockSum_one] using cell_2_211) (by norm_num)

theorem sum_2_208_4 : blockSum (rowCell 2) 208 4 ≤ (4603303248852178862850473 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_208_2 sum_2_210_2 (by norm_num)

theorem sum_2_212_2 : blockSum (rowCell 2) 212 2 ≤ (8869708191990957953473293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_212) (by simpa only [blockSum_one] using cell_2_213) (by norm_num)

theorem sum_2_214_2 : blockSum (rowCell 2) 214 2 ≤ (746173805685028955994567 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_214) (by simpa only [blockSum_one] using cell_2_215) (by norm_num)

theorem sum_2_212_4 : blockSum (rowCell 2) 212 4 ≤ (16331446248841247513418963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_212_2 sum_2_214_2 (by norm_num)

theorem sum_2_208_8 : blockSum (rowCell 2) 208 8 ≤ (1229623827909441932114729 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_208_4 sum_2_212_4 (by norm_num)

theorem sum_2_216_2 : blockSum (rowCell 2) 216 2 ≤ (6269635510585916913120843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_216) (by simpa only [blockSum_one] using cell_2_217) (by norm_num)

theorem sum_2_218_2 : blockSum (rowCell 2) 218 2 ≤ (1315419561697186030469027 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_218) (by simpa only [blockSum_one] using cell_2_219) (by norm_num)

theorem sum_2_216_4 : blockSum (rowCell 2) 216 4 ≤ (11531313757374661034996951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_216_2 sum_2_218_2 (by norm_num)

theorem sum_2_220_2 : blockSum (rowCell 2) 220 2 ≤ (176422462699672042051007 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_220) (by simpa only [blockSum_one] using cell_2_221) (by norm_num)

theorem sum_2_222_2 : blockSum (rowCell 2) 222 2 ≤ (3692826018327280771960701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_222) (by simpa only [blockSum_one] using cell_2_223) (by norm_num)

theorem sum_2_220_4 : blockSum (rowCell 2) 220 4 ≤ (2025846896454770455808969 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_220_2 sum_2_222_2 (by norm_num)

theorem sum_2_216_8 : blockSum (rowCell 2) 216 8 ≤ (19634701343193742858232827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_216_4 sum_2_220_4 (by norm_num)

theorem sum_2_208_16 : blockSum (rowCell 2) 208 16 ≤ (11796532767259176937180831 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_208_8 sum_2_216_8 (by norm_num)

theorem sum_2_192_32 : blockSum (rowCell 2) 192 32 ≤ (1139667699569428415476143 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_192_16 sum_2_208_16 (by norm_num)

#print axioms sum_2_192_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
