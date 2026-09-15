import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_192_0 : expNegUpper (385894232063956470769 / 4784759183237377600 : ℝ) ≤ (9424865248207870108307717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1877767 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_192_1 : expNegUpper (123595375476724597535311 / 1531122938635960832000 : ℝ) ≤ (877597062272445426937533 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (939407 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_192 : rowCell 5 192 ≤ (1327221304021862884380831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9424865248207870108307717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (877597062272445426937533 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_192_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_192_1
  · norm_num [gridPoint]

theorem exp_5_193_0 : expNegUpper (124271360405840863495879 / 1539497162799272448000 : ℝ) ≤ (8775968197670145186346033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (939407 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_193_1 : expNegUpper (62190901466999400897319 / 769748581399636224000 : ℝ) ≤ (2042109590503682653063213 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1879867 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_193 : rowCell 5 193 ≤ (1235601349822489610114431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8775968197670145186346033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2042109590503682653063213 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_193_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_193_1
  · norm_num [gridPoint]

theorem exp_5_194_0 : expNegUpper (2501204676353868789679 / 30957884505366784000 : ℝ) ≤ (8168436129295422235154999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1879867 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_194_1 : expNegUpper (5006876039541213524077 / 61915769010733568000 : ℝ) ≤ (7599907906280733062043221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1880927 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_194 : rowCell 5 194 ≤ (28746045348645192680593 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8168436129295422235154999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7599907906280733062043221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_194_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_194_1
  · norm_num [gridPoint]

theorem exp_5_195_0 : expNegUpper (125852784488362445339357 / 1556314126043161088000 : ℝ) ≤ (7599905851407402515987531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1880927 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_195_1 : expNegUpper (31491419908164463296559 / 389078531510790272000 : ℝ) ≤ (1767032211338109000820897 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1881993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_195 : rowCell 5 195 ≤ (106960626840015029499267 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7599905851407402515987531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1767032211338109000820897 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_195_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_195_1
  · norm_num [gridPoint]

theorem exp_5_196_0 : expNegUpper (31662255602546631947791 / 391189216280934528000 : ℝ) ≤ (353406347742857516067327 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1881993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_196_1 : expNegUpper (25352629771743998755327 / 312951373024747622400 : ℝ) ≤ (205342499240603104173149 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (941533 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_196 : rowCell 5 196 ≤ (49728723642167024032231 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (353406347742857516067327 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (205342499240603104173149 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_196_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_196_1
  · norm_num [gridPoint]

theorem exp_5_197_0 : expNegUpper (542335989682997164121 / 6694563585149235200 : ℝ) ≤ (657095823706961687662811 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (941533 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_197_1 : expNegUpper (1357067219777185176619 / 16736408962873088000 : ℝ) ≤ (6106365681504855352663153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376829 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_197 : rowCell 5 197 ≤ (924441849925658609212313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (657095823706961687662811 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6106365681504855352663153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_197_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_197_1
  · norm_num [gridPoint]

theorem exp_5_198_0 : expNegUpper (64126299988327254700117 / 790855429101078784000 : ℝ) ≤ (6106364083121874202851103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376829 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_198_1 : expNegUpper (128369199026002738391953 / 1581710858202157568000 : ℝ) ≤ (2836206145408978840305393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1885231 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_198 : rowCell 5 198 ≤ (858918955682091002509749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6106364083121874202851103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2836206145408978840305393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_198_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_198_1
  · norm_num [gridPoint]

theorem exp_5_199_0 : expNegUpper (8259837414782444929 / 101774215180800000 : ℝ) ≤ (5672410821897858943830053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1885231 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_199_1 : expNegUpper (1033422399615205087 / 12721776897600000 : ℝ) ≤ (5267264423227944169430811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (943161 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_199 : rowCell 5 199 ≤ (797730947489051605732717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5672410821897858943830053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5267264423227944169430811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_199_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_199_1
  · norm_num [gridPoint]

theorem exp_5_200_0 : expNegUpper (16233880806975819767959 / 199844525562949696000 : ℝ) ≤ (5267263073766879719543669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (943161 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_200_1 : expNegUpper (129990131429087745780391 / 1598756204503597568000 : ℝ) ≤ (4889181343985348184578947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94371 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_200 : rowCell 5 200 ≤ (740617051873024033035879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5267263073766879719543669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4889181343985348184578947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_200_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_200_1
  · norm_num [gridPoint]

theorem exp_5_201_0 : expNegUpper (130685870518485724513439 / 1607313135112950272000 : ℝ) ≤ (4889180104707524502806499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94371 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_201_1 : expNegUpper (13080620344990271483719 / 160731313511295027200 : ℝ) ≤ (4536513338037654994433381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (75541 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_201 : rowCell 5 201 ≤ (687330034241430955310937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4889180104707524502806499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4536513338037654994433381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_201_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_201_1
  · norm_num [gridPoint]

theorem exp_5_202_0 : expNegUpper (13150444178635184785399 / 161589290402805811200 : ℝ) ≤ (181460488013858693498339 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (75541 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_202_1 : expNegUpper (131626026006684189774461 / 1615892904028058112000 : ℝ) ≤ (4207698116071853980192383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (377927 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_202 : rowCell 5 202 ≤ (31881783619984007378433 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (181460488013858693498339 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4207698116071853980192383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_202_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_202_1
  · norm_num [gridPoint]

theorem exp_5_203_0 : expNegUpper (132326770251743574894389 / 1624495511248921088000 : ℝ) ≤ (1051924268000982020947269 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (377927 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_203_1 : expNegUpper (33112402272942704330317 / 406123877812230272000 : ℝ) ≤ (1950628631676259530836767 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (29543 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_203 : rowCell 5 203 ≤ (147828058880713199413779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1051924268000982020947269 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1950628631676259530836767 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_203_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_203_1
  · norm_num [gridPoint]

theorem exp_5_204_0 : expNegUpper (1331528659069995523637 / 16331209567755392000 : ℝ) ≤ (3901256305534520895889117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (29543 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_204_1 : expNegUpper (5331078507900049768267 / 65324838271021568000 : ℝ) ≤ (3615792740915680280423863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (945937 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_204 : rowCell 5 204 ≤ (274074985032950669939681 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3901256305534520895889117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3615792740915680280423863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_204_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_204_1
  · norm_num [gridPoint]

theorem exp_5_205_0 : expNegUpper (4322023830466400870677 / 52960298084126208000 : ℝ) ≤ (3615791862523757963279817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (945937 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_205_1 : expNegUpper (2163033819616356728383 / 26480149042063104000 : ℝ) ≤ (837495861881048205704799 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1893003 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_205 : rowCell 5 205 ≤ (162544190055184541609 / 320000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3615791862523757963279817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (837495861881048205704799 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_205_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_205_1
  · norm_num [gridPoint]

theorem exp_5_206_0 : expNegUpper (67408199378229422752657 / 825220181373020416000 : ℝ) ≤ (837495660561479655688719 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1893003 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_206_1 : expNegUpper (26988604288049616581909 / 330088072549208166400 : ℝ) ≤ (775645462427156829513377 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (947069 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_206 : rowCell 5 206 ≤ (470526799979236230416117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (837495660561479655688719 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (775645462427156829513377 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_206_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_206_1
  · norm_num [gridPoint]

theorem exp_5_207_0 : expNegUpper (27130771187067890927149 / 331826864637984870400 : ℝ) ≤ (3102581111707311685702551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (947069 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_207_1 : expNegUpper (8486359160121361761571 / 103695895199370272000 : ℝ) ≤ (1436205343103753741769213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1895279 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_207 : rowCell 5 207 ≤ (1089254425151605132291 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3102581111707311685702551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1436205343103753741769213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_207_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_207_1
  · norm_num [gridPoint]

theorem exp_5_208_0 : expNegUpper (8530945017089931319459 / 104240695121222688000 : ℝ) ≤ (718102502522190302433143 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1895279 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_208_1 : expNegUpper (136624282173633879715583 / 1667851121939563008000 : ℝ) ≤ (2658359752180316035251281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (948213 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_208 : rowCell 5 208 ≤ (40330870011561940132831 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (718102502522190302433143 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2658359752180316035251281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_208_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_208_1
  · norm_num [gridPoint]

theorem exp_5_209_0 : expNegUpper (5493608070523833266447 / 67063630359798272000 : ℝ) ≤ (664589783240185224262343 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (948213 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_209_1 : expNegUpper (2749412765353260084599 / 33531815179899136000 : ℝ) ≤ (1229691383847063889260111 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1897579 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_209 : rowCell 5 209 ≤ (373190337366991893431111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (664589783240185224262343 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1229691383847063889260111 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_209_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_209_1
  · norm_num [gridPoint]

theorem exp_5_210_0 : expNegUpper (69094555198324446507151 / 842676617178052864000 : ℝ) ≤ (307422775096502546855411 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1897579 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_210_1 : expNegUpper (138320824836367808457301 / 1685353234356105728000 : ℝ) ≤ (45489886683556901682639 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (949369 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_210 : rowCell 5 210 ≤ (345198530020743558288223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (307422775096502546855411 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45489886683556901682639 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_210_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_210_1
  · norm_num [gridPoint]

theorem exp_5_211_0 : expNegUpper (139041856166436731899789 / 1694138548023009792000 : ℝ) ≤ (284311726913225368367783 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (949369 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_211_1 : expNegUpper (1391748518720869391267 / 16941385480230097920 : ℝ) ≤ (2102766981794464063654231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1899903 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_211 : rowCell 5 211 ≤ (319193790019798865183839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (284311726913225368367783 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2102766981794464063654231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_211_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_211_1
  · norm_num [gridPoint]

theorem exp_5_212_0 : expNegUpper (1398984490647979950467 / 17029466999956689920 : ℝ) ≤ (1051383253526893766222423 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1899903 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_212_1 : expNegUpper (140032729367159042967211 / 1702946699995668992000 : ℝ) ≤ (971664154999553642853021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950537 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_212 : rowCell 5 212 ≤ (295044869222809286099751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1051383253526893766222423 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (971664154999553642853021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_212_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_212_1
  · norm_num [gridPoint]

theorem exp_5_213_0 : expNegUpper (140758899084071329184099 / 1711777690274083328000 : ℝ) ≤ (1943327875775895028264447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950537 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_213_1 : expNegUpper (70447233656961383353949 / 855888845137041664000 : ℝ) ≤ (897679111463065067934539 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1902251 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_213 : rowCell 5 213 ≤ (272628349293143477569351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1943327875775895028264447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (897679111463065067934539 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_213_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_213_1
  · norm_num [gridPoint]

theorem exp_5_214_0 : expNegUpper (2832464324331907620821 / 34412630377165056000 : ℝ) ≤ (1795357825888970565538709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1902251 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_214_1 : expNegUpper (5670403028188670283113 / 68825260754330112000 : ℝ) ≤ (829043130339886823913597 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1903433 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_214 : rowCell 5 214 ≤ (251828245496264354644771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1795357825888970565538709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (829043130339886823913597 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_214_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_214_1
  · norm_num [gridPoint]

theorem exp_5_215_0 : expNegUpper (142491410454708797346617 / 1729508185748177408000 : ℝ) ≤ (829042948879469404054697 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1903433 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_215_1 : expNegUpper (17828695566484957600757 / 216188523218522176000 : ℝ) ≤ (382697256771718959331247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1904621 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_215 : rowCell 5 215 ≤ (232535624524572095106671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (829042948879469404054697 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (382697256771718959331247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_215_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_215_1
  · norm_num [gridPoint]

theorem exp_5_216_0 : expNegUpper (17920436473843778103733 / 217300961367982144000 : ℝ) ≤ (61231547818197143293953 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1904621 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_216_1 : expNegUpper (28700588757550024924331 / 347681538188771430400 : ℝ) ≤ (353196928501079426901743 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (381163 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_216 : rowCell 5 216 ≤ (107324118198599306502583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (61231547818197143293953 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (353196928501079426901743 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_216_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_216_1
  · norm_num [gridPoint]

theorem exp_5_217_0 : expNegUpper (28847894043411662043971 / 349466006889058406400 : ℝ) ≤ (282557482211609437535831 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (381163 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_217_1 : expNegUpper (72190111732333397626843 / 873665017222646016000 : ℝ) ≤ (651722860927707313881773 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (381403 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_217 : rowCell 5 217 ≤ (12379385026109686720027 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (282557482211609437535831 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (651722860927707313881773 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_217_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_217_1
  · norm_num [gridPoint]

theorem exp_5_218_0 : expNegUpper (72559677862985850122827 / 878137608126241024000 : ℝ) ≤ (1303445445199019180880751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (381403 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_218_1 : expNegUpper (145261413554968319431213 / 1756275216252482048000 : ℝ) ≤ (300541593923906826492829 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (95411 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_218 : rowCell 5 218 ≤ (91355732557628978427603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1303445445199019180880751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (300541593923906826492829 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_218_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_218_1
  · norm_num [gridPoint]

theorem exp_5_219_0 : expNegUpper (5840126332393161665453 / 70609729454617088000 : ℝ) ≤ (601083061562533924349429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (95411 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_219_1 : expNegUpper (1461465240509933438833 / 17652432363654272000 : ℝ) ≤ (13854884197200595263133 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (238679 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_219 : rowCell 5 219 ≤ (21060985255249657378133 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (601083061562533924349429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13854884197200595263133 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_219_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_219_1
  · norm_num [gridPoint]

theorem exp_5_220_0 : expNegUpper (36722721990242245280233 / 443558523696031872000 : ℝ) ≤ (554195252632249258565807 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (238679 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_220_1 : expNegUpper (147035564945080515339011 / 1774234094784127488000 : ℝ) ≤ (1021595501280446256724459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (238831 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_220 : rowCell 5 220 ≤ (77660246628280064066703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (554195252632249258565807 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1021595501280446256724459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_220_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_220_1
  · norm_num [gridPoint]

theorem exp_5_221_0 : expNegUpper (147782554671730165428539 / 1783247791508582912000 : ℝ) ≤ (255398822741193603084039 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (238831 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_221_1 : expNegUpper (14792854622956848052741 / 178324779150858291200 : ℝ) ≤ (941291005655641728714321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1911871 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_221 : rowCell 5 221 ≤ (2236491129378404139227 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (255398822741193603084039 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (941291005655641728714321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_221_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_221_1
  · norm_num [gridPoint]

theorem exp_5_222_0 : expNegUpper (14867816843445124128821 / 179228432653879347200 : ℝ) ≤ (94129081382384831401001 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1911871 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_222_1 : expNegUpper (148825477896795886177561 / 1792284326538793472000 : ℝ) ≤ (433509650866511138795321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1913099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_222 : rowCell 5 222 ≤ (65931799140013224582721 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (94129081382384831401001 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (433509650866511138795321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_222_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_222_1
  · norm_num [gridPoint]

theorem exp_5_223_0 : expNegUpper (149577739241470855429009 / 1801343699874759168000 : ℝ) ≤ (867019126812585000916341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1913099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_223_1 : expNegUpper (4678949060596918094329 / 56291990621086224000 : ℝ) ≤ (31934093385950337607211 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1914333 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_223 : rowCell 5 223 ≤ (60720191600966785200257 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (867019126812585000916341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31934093385950337607211 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_223_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_223_1
  · norm_num [gridPoint]

theorem sum_5_192_2 : blockSum (rowCell 5) 192 2 ≤ (1281411326922176247247631 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_192) (by simpa only [blockSum_one] using cell_5_193) (by norm_num)

theorem sum_5_194_2 : blockSum (rowCell 5) 194 2 ≤ (221944808234595800221639 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_194) (by simpa only [blockSum_one] using cell_5_195) (by norm_num)

theorem sum_5_192_4 : blockSum (rowCell 5) 192 4 ≤ (1195567684047577624177913 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_192_2 sum_5_194_2 (by norm_num)

theorem sum_5_196_2 : blockSum (rowCell 5) 196 2 ≤ (1919016322768999089856933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_196) (by simpa only [blockSum_one] using cell_5_197) (by norm_num)

theorem sum_5_198_2 : blockSum (rowCell 5) 198 2 ≤ (828324951585571304121233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_198) (by simpa only [blockSum_one] using cell_5_199) (by norm_num)

theorem sum_5_196_4 : blockSum (rowCell 5) 196 4 ≤ (3575666225940141698099399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_196_2 sum_5_198_2 (by norm_num)

theorem sum_5_192_8 : blockSum (rowCell 5) 192 8 ≤ (8357936962130452194811051 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_192_4 sum_5_196_4 (by norm_num)

theorem sum_5_200_2 : blockSum (rowCell 5) 200 2 ≤ (22311673220538359192919 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_200) (by simpa only [blockSum_one] using cell_5_201) (by norm_num)

theorem sum_5_202_2 : blockSum (rowCell 5) 202 2 ≤ (38404622122579154538243 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_202) (by simpa only [blockSum_one] using cell_5_203) (by norm_num)

theorem sum_5_200_4 : blockSum (rowCell 5) 200 4 ≤ (83027968563655872924081 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_200_2 sum_5_202_2 (by norm_num)

theorem sum_5_204_2 : blockSum (rowCell 5) 204 2 ≤ (1056100563988353032407487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_204) (by simpa only [blockSum_one] using cell_5_205) (by norm_num)

theorem sum_5_206_2 : blockSum (rowCell 5) 206 2 ≤ (906228570039878283332517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_206) (by simpa only [blockSum_one] using cell_5_207) (by norm_num)

theorem sum_5_204_4 : blockSum (rowCell 5) 204 4 ≤ (490582283507057828935001 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_204_2 sum_5_206_2 (by norm_num)

theorem sum_5_200_8 : blockSum (rowCell 5) 200 8 ≤ (1154806032016304812327649 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_200_4 sum_5_204_4 (by norm_num)

theorem sum_5_192_16 : blockSum (rowCell 5) 192 16 ≤ (12977161090195671444121647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_192_8 sum_5_200_8 (by norm_num)

theorem sum_5_208_2 : blockSum (rowCell 5) 208 2 ≤ (776499037482611294759421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_208) (by simpa only [blockSum_one] using cell_5_209) (by norm_num)

theorem sum_5_210_2 : blockSum (rowCell 5) 210 2 ≤ (332196160020271211736031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_210) (by simpa only [blockSum_one] using cell_5_211) (by norm_num)

theorem sum_5_208_4 : blockSum (rowCell 5) 208 4 ≤ (1440891357523153718231483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_208_2 sum_5_210_2 (by norm_num)

theorem sum_5_212_2 : blockSum (rowCell 5) 212 2 ≤ (283836609257976381834551 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_212) (by simpa only [blockSum_one] using cell_5_213) (by norm_num)

theorem sum_5_214_2 : blockSum (rowCell 5) 214 2 ≤ (242181935010418224875721 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_214) (by simpa only [blockSum_one] using cell_5_215) (by norm_num)

theorem sum_5_212_4 : blockSum (rowCell 5) 212 4 ≤ (1027379969274208216231 / 976562500000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_212_2 sum_5_214_2 (by norm_num)

theorem sum_5_208_8 : blockSum (rowCell 5) 208 8 ≤ (2492928446059942931652027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_208_4 sum_5_212_4 (by norm_num)

theorem sum_5_216_2 : blockSum (rowCell 5) 216 2 ≤ (206359198407476800262799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_216) (by simpa only [blockSum_one] using cell_5_217) (by norm_num)

theorem sum_5_218_2 : blockSum (rowCell 5) 218 2 ≤ (35119934715725521588027 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_218) (by simpa only [blockSum_one] using cell_5_219) (by norm_num)

theorem sum_5_216_4 : blockSum (rowCell 5) 216 4 ≤ (190979435993052204101467 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_216_2 sum_5_218_2 (by norm_num)

theorem sum_5_220_2 : blockSum (rowCell 5) 220 2 ≤ (149227962768388996521967 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_220) (by simpa only [blockSum_one] using cell_5_221) (by norm_num)

theorem sum_5_222_2 : blockSum (rowCell 5) 222 2 ≤ (63325995370490004891489 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_222) (by simpa only [blockSum_one] using cell_5_223) (by norm_num)

theorem sum_5_220_4 : blockSum (rowCell 5) 220 4 ≤ (55175990701873801260989 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_220_2 sum_5_222_2 (by norm_num)

theorem sum_5_216_8 : blockSum (rowCell 5) 216 8 ≤ (657838825495473414507879 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_216_4 sum_5_220_4 (by norm_num)

theorem sum_5_208_16 : blockSum (rowCell 5) 208 16 ≤ (761721219410177952133557 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_208_8 sum_5_216_8 (by norm_num)

theorem sum_5_192_32 : blockSum (rowCell 5) 192 32 ≤ (2098220898405820150598679 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_192_16 sum_5_208_16 (by norm_num)

#print axioms sum_5_192_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
